import Manuscript.UniformMixedMass
import Manuscript.SupportDisorder

/-! Proposition 2.2 for the actual physical disorder moments, without an
assumed comparison or mass estimate. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.UniformPhysicalMass
open MeasureTheory SpinGlass.Disorder Manuscript.Model Manuscript.MixedThreshold
open Manuscript.MixedCoefficient Manuscript.UniformMixedMass Manuscript.UniformGraphMass
open Manuscript.DisorderOrthogonality Manuscript.SupportDisorder

theorem inflated_graphical_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {beta B h rho : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    graphMass Subtype.val (Finset.univ : Finset (Edge N P)).powerset h
      (fun e => secondMoment μ (physicalScale N P a beta e) / theta P a B ^ 2) ≤
        massConstant P a (betaPlus P a B ^ 2) rho := by
  have hplus : 0 < betaPlus P a B := hB.trans (betaPlus_range P a hB hBT).2.1
  apply (graphMass_mono Subtype.val (Finset.univ : Finset (Edge N P)).powerset h
    (fun e => secondMoment μ (physicalScale N P a beta e) / theta P a B ^ 2)
    (comparisonWeight N P a (betaPlus P a B ^ 2))
    (fun e => div_nonneg (secondMoment_nonneg μ _) (sq_nonneg _)) ?_).trans
      (uniform_graphical_mass_midpoint N P a hP ha hp hpN hB hBT hfield)
  intro e
  exact secondMoment_physical_inflated_le μ hunit N P a hbeta hbetaB hB hplus e
    (by have := hp _ (edge_order_mem e); omega)

theorem physical_graphical_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {beta B h rho : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    graphMass Subtype.val (Finset.univ : Finset (Edge N P)).powerset h
      (fun e => secondMoment μ (physicalScale N P a beta e)) ≤
        massConstant P a (betaPlus P a B ^ 2) rho := by
  obtain ⟨hθ, hθ1⟩ := theta_range P a hB hBT
  have hq : 0 < theta P a B ^ 2 := sq_pos_of_pos hθ
  have hq1 : theta P a B ^ 2 ≤ 1 := by nlinarith
  apply (graphMass_mono Subtype.val (Finset.univ : Finset (Edge N P)).powerset h
    (fun e => secondMoment μ (physicalScale N P a beta e))
    (fun e => secondMoment μ (physicalScale N P a beta e) / theta P a B ^ 2)
    (fun e => secondMoment_nonneg μ _) ?_).trans
      (inflated_graphical_mass μ hunit N P a hP ha hp hpN hbeta hbetaB hB hBT hfield)
  intro e
  exact (le_div_iff₀ hq).2 (mul_le_of_le_one_right (secondMoment_nonneg μ _) hq1)

/-- The actual finite edge-count tail with both the precise floor and real
cutoff estimates. -/
theorem physical_edge_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hunit : UnitSecondMoment μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {beta B h rho t : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) (ht : 0 ≤ t) :
    graphMass Subtype.val ((Finset.univ : Finset (Edge N P)).powerset.filter
      (fun Γ => t < (Γ.card : ℝ))) h
      (fun e => secondMoment μ (physicalScale N P a beta e)) ≤
        massConstant P a (betaPlus P a B ^ 2) rho * theta P a B ^ (2 * Nat.floor t + 2) ∧
    massConstant P a (betaPlus P a B ^ 2) rho * theta P a B ^ (2 * Nat.floor t + 2) ≤
      massConstant P a (betaPlus P a B ^ 2) rho * theta P a B ^ (2 * t) := by
  obtain ⟨hθ, hθ1⟩ := theta_range P a hB hBT
  have hq : 0 < theta P a B ^ 2 := sq_pos_of_pos hθ
  have hq1 : theta P a B ^ 2 ≤ 1 := by nlinarith
  have hplus : 0 < betaPlus P a B := hB.trans (betaPlus_range P a hB hBT).2.1
  have hh := finite_geometric_tail_real Subtype.val
    (Finset.univ : Finset (Edge N P)).powerset h
    (fun e => secondMoment μ (physicalScale N P a beta e))
    (comparisonWeight N P a (betaPlus P a B ^ 2))
    (fun e => secondMoment_nonneg μ _)
    (fun e => (comparisonWeight_range N P a hP ha hp hpN
      (betaPlus_sq_range P a hP ha hp hB hBT).1.le
      (betaPlus_sq_range P a hP ha hp hB hBT).2 e).1)
    hq hq1
    (fun e => secondMoment_physical_le_ratio μ hunit N P a hbeta hbetaB hB hplus e
      (by have := hp _ (edge_order_mem e); omega)) ht
    (uniform_graphical_mass_midpoint N P a hP ha hp hpN hB hBT hfield)
  have hpow : (theta P a B ^ 2) ^ (Nat.floor t + 1) =
      theta P a B ^ (2 * Nat.floor t + 2) := by rw [← pow_mul]; congr 1 <;> omega
  have hrpow : (theta P a B ^ 2) ^ t = theta P a B ^ (2 * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le]
    norm_num
  rwa [hpow, hrpow] at hh

end Manuscript.UniformPhysicalMass
