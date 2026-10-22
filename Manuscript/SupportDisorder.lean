import Manuscript.SupportTail
import Manuscript.DisorderOrthogonality
import SpinGlass.DisorderMomentBounds

/-! Actual mixed physical variances and the higher-order retained-graph MSE. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SupportDisorder
open MeasureTheory SpinGlass.Disorder
open Manuscript.DisorderOrthogonality Manuscript.SupportEvaluation

/-- Squaring the real half-power normalization gives the stated natural power. -/
theorem scaleDenominator_sq (N p : ℕ) (hp : 0 < p) :
    Model.scaleDenominator N p ^ 2 = (N : ℝ) ^ (p-1) := by
  unfold Model.scaleDenominator
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  have he : (((p : ℝ)-1)/2)*(2 : ℝ) = ((p-1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp]
    push_cast
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he, Real.rpow_natCast]

/-- The exact square of the physical scale, with no normalization discrepancy. -/
theorem physicalScale_sq (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (e : Model.Edge N P) (hp : 0 < e.val.card) :
    physicalScale N P a beta e ^ 2 =
      beta^2 * a e.val.card^2 / (N : ℝ)^(e.val.card-1) := by
  rw [physicalScale, div_pow, mul_pow, scaleDenominator_sq N e.val.card hp]

/-- The variance-one assumption supplies the actual edge-moment bound (15). -/
theorem secondMoment_physical_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (e : Model.Edge N P) (hp : 0 < e.val.card) :
    secondMoment μ (physicalScale N P a beta e) ≤
      beta^2 * a e.val.card^2 / (N : ℝ)^(e.val.card-1) := by
  exact (secondMoment_le_scale_sq μ hunit _).trans_eq (physicalScale_sq N P a beta e hp)

/-- Uniformity over `beta ∈ [0,B]` preserves the same physical moment bound. -/
theorem secondMoment_physical_le_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    {beta B : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (e : Model.Edge N P) (hp : 0 < e.val.card) :
    secondMoment μ (physicalScale N P a beta e) ≤
      B^2 * a e.val.card^2 / (N : ℝ)^(e.val.card-1) := by
  apply (secondMoment_physical_le μ hunit N P a beta e hp).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith

/-- Inflated moments are bounded by the comparison inverse-temperature weights,
including the input endpoint `beta = 0`. -/
theorem secondMoment_physical_inflated_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    {beta B betaPlus : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hplus : 0 < betaPlus)
    (e : Model.Edge N P) (hp : 0 < e.val.card) :
    secondMoment μ (physicalScale N P a beta e) / (B/betaPlus)^2 ≤
      betaPlus^2 * a e.val.card^2 / (N : ℝ)^(e.val.card-1) := by
  apply (div_le_div_of_nonneg_right
    (secondMoment_physical_le_bound μ hunit N P a hbeta hbetaB e hp) (sq_nonneg _)).trans_eq
  simp only [div_pow, div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
  calc
    _ = (B^2 * (B^2)⁻¹) *
      (betaPlus^2 * a e.val.card^2 * ((N : ℝ)^(e.val.card-1))⁻¹) := by ring_nf; simp only [inv_inv]; ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hB.ne'), one_mul]

/-- The equivalent edgewise domination needed by the geometric edge tail. -/
theorem secondMoment_physical_le_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    {beta B betaPlus : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hplus : 0 < betaPlus)
    (e : Model.Edge N P) (hp : 0 < e.val.card) :
    secondMoment μ (physicalScale N P a beta e) ≤
      (B/betaPlus)^2 * (betaPlus^2 * a e.val.card^2 / (N : ℝ)^(e.val.card-1)) := by
  have hh := secondMoment_physical_inflated_le μ hunit N P a hbeta hbetaB hB hplus e hp
  have hq : 0 < (B/betaPlus)^2 := sq_pos_of_pos (div_pos hB hplus)
  simpa only [mul_comm] using (div_le_iff₀ hq).mp hh

/-- The retained support polynomial in the actual physical mixed disorder. -/
def retained (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (k : ℕ) (J : Model.Edge N P → ℝ) : ℝ :=
  ∑ Γ ∈ (Finset.univ : Finset (Model.Edge N P)).powerset.filter
      (fun Γ => (support Subtype.val Γ).card ≤ k),
    DisorderOrthogonality.graphWeight Subtype.val h (physicalScale N P a beta) Γ J

/-- The actual squared approximation error is exactly the omitted support mass. -/
theorem retained_error_eq_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ) (k : ℕ) :
    (∫ J, (Model.normalizedPartition N P a beta h J - retained N P a beta h k J)^2
      ∂iidLaw μ) =
    SupportTail.supportTail Subtype.val Finset.univ h
      (fun e => secondMoment μ (physicalScale N P a beta e)) k := by
  have hh := physical_retained_family_error μ hμ N P a beta h
    (fun Γ => (support Subtype.val Γ).card ≤ k)
  simpa only [retained, SupportTail.supportTail, UniformGraphMass.graphMass, not_le] using hh

end Manuscript.SupportDisorder
