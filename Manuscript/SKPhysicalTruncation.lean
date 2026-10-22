import Manuscript.SKTruncation
import Manuscript.UniformSKTransport

/-! Unconditional SK weak-field truncation under the original iid disorder law. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKBranching
open MeasureTheory SpinGlass.Disorder SpinGlass.CutoffTail

def physicalScale (N : ℕ) (beta : ℝ) : ℝ := beta / Real.sqrt (N : ℝ)

theorem physical_secondMoment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) {N : ℕ} (hN : 0 < N)
    {beta B : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) :
    (N : ℝ) * secondMoment μ (physicalScale N beta) ≤ B ^ 2 := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs := secondMoment_le_scale_sq μ hunit (physicalScale N beta)
  have he : (N : ℝ) * physicalScale N beta ^ 2 = beta ^ 2 := by
    unfold physicalScale
    rw [div_pow,Real.sq_sqrt hNR.le]
    field_simp
  have hp := mul_le_mul_of_nonneg_left hs hNR.le
  rw [he] at hp
  exact hp.trans (pow_le_pow_left₀ hbeta hbetaB 2)

/-- Proposition 4.2 on the actual untyped pair-edge coordinates. All moment,
weak-field and complete graphical-mass hypotheses are discharged here. -/
theorem physical_truncation_mse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N D L : ℕ} (hN : 2 ≤ N)
    {beta B Bplus h rho C alpha : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B) (hBplus : B < Bplus)
    (hplus1 : Bplus < 1)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ)))
    (hC : 0 < C) (hBC : branchConstant B (rho ^ 2) ≤ C) (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (C * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * N)) :
    (∫ J : Finset (Fin N) → ℝ,
      (FieldExpansion.normalizedPartition id
        ((Finset.univ : Finset (Fin N)).powersetCard 2) h (fun e => physicalScale N beta * J e) -
        truncation D L h (physicalScale N beta) J) ^ 2 ∂iidLaw μ) ≤
      UniformMixedMass.massConstant {2} (fun _ => 1) (Bplus ^ 2) rho *
        ((B / Bplus) ^ 2) ^ (L + 1) +
      2 * massConstant B (rho ^ 2) * Real.exp (-phi 1 C N (D + 1)) +
      UniformMixedMass.massConstant {2} (fun _ => 1) (Bplus ^ 2) rho *
        ((B / Bplus) ^ 2) ^ (3 * alpha * N / 2) := by
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hplus := hB.trans hBplus
  have hB1 := hBplus.trans hplus1
  have hq : 0 < (B / Bplus) ^ 2 := pow_pos (div_pos hB hplus) _
  have hq1 : (B / Bplus) ^ 2 ≤ 1 := by
    exact (pow_lt_one₀ (div_nonneg hB.le hplus.le)
      ((div_lt_one hplus).mpr hBplus) (by omega : 2 ≠ 0)).le
  have hr := physical_secondMoment μ hunit hNpos hbeta hbetaB
  have hrq : secondMoment μ (physicalScale N beta) ≤ (B / Bplus) ^ 2 * (Bplus ^ 2 / N) := by
    have he : (B / Bplus) ^ 2 * (Bplus ^ 2 / N) = B ^ 2 / N := by field_simp
    rw [he]
    exact (le_div_iff₀ hNR).mpr (by nlinarith [hr])
  have hmass := UniformSKTransport.pair_comparison_mass N hN
    (pow_pos hplus 2) (by nlinarith) hfield
  have hfield' := weak_field_squared N hNpos hfield
  simpa only [Fintype.card_fin] using truncation_mse_bound (V := Fin N) μ hμ D L h (physicalScale N beta)
    (by simpa using hNpos) hB.le hB1 (sq_nonneg rho) (by simpa using hr)
    (by simpa using hfield') (by positivity) hq hq1 hrq hmass hC hBC halpha hgap
    (by simpa using hcut)

end Manuscript.SKBranching
