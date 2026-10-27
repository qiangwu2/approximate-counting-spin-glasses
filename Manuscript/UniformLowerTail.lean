import Manuscript.UniformPhysicalMass
import Manuscript.OriginalLawLowerTail

/-! Proposition 5.5 with the actual uniform constant and the
literal raw-disorder remainder, including temperature zero. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.UniformLowerTail
open MeasureTheory SpinGlass.Disorder Manuscript.Model Manuscript.MixedThreshold
open Manuscript.UniformMixedMass Manuscript.UniformPhysicalMass
open Manuscript.DisorderLowerTail Manuscript.OriginalLawLowerTail

/-- The uniform lower-tail bound under the original iid disorder law. Both
symmetry and variance-one are the model hypotheses; no mass bound is assumed. -/
theorem physical_lower_tail_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {beta B h rho z : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) (hz : 0 < z) :
    (iidLaw μ).real {J | normalizedPartition N P a beta h J < z} ≤
      massConstant P a (betaPlus P a B ^ 2) rho *
        z ^ ConditionalLowerTail.exponent (theta P a B) + tau μ N P a B (theta P a B) := by
  have hN : 0 < N := by obtain ⟨p, hpP⟩ := hP; have := hp p hpP; have := hpN p hpP; omega
  obtain ⟨hθ, hθ1⟩ := theta_range P a hB hBT
  have hl := physical_lower_tail μ hμ hN P a h hbeta hbetaB hB hθ hθ1 hz
  have hm := inflated_graphical_mass μ hunit N P a hP ha hp hpN hbeta hbetaB hB hBT hfield
  exact hl.trans (add_le_add (mul_le_mul_of_nonneg_right hm
    (Real.rpow_nonneg hz.le _)) le_rfl)

/-- The negative moment on the paper's raw cutoff event is integrable; this is
proved from conditional sign averaging and its finite moment domination. -/
theorem integrableOn_raw_negative_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 0 < N) (P : Finset ℕ) (a : ℕ → ℝ) (h : ℝ)
    {beta B θ : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    IntegrableOn (fun J => normalizedPartition N P a beta h J ^ (-ConditionalLowerTail.exponent θ))
      (physicalRawCutoff N P a B θ) (iidLaw μ) := by
  classical
  have hi := integrable_restrictedNegativeMoment μ
    (Subtype.val : Edge N P → Finset (Fin N)) Finset.univ h
    (DisorderOrthogonality.physicalScale N P a beta) hθ hθ1
  have hmeas := measurableSet_inflationCutoff Finset.univ
    (DisorderOrthogonality.physicalScale N P a beta) θ
  have hi' : IntegrableOn
      (fun J => normalizedPartition N P a beta h J ^ (-ConditionalLowerTail.exponent θ))
      (inflationCutoff Finset.univ (DisorderOrthogonality.physicalScale N P a beta) θ)
      (iidLaw μ) := by
    apply (integrable_indicator_iff hmeas).mp
    have heq : (inflationCutoff Finset.univ
        (DisorderOrthogonality.physicalScale N P a beta) θ).indicator
        (fun J : Edge N P → ℝ => normalizedPartition N P a beta h J ^
          (-ConditionalLowerTail.exponent θ)) =
        restrictedNegativeMoment (Subtype.val : Edge N P → Finset (Fin N)) Finset.univ h
          (DisorderOrthogonality.physicalScale N P a beta) θ := by
      funext J
      simp only [Set.indicator_apply, restrictedNegativeMoment, normalizedGraph_physical]
    rw [heq]
    exact hi
  exact hi'.mono_set (physicalRawCutoff_subset_inflation hN P a hbeta hbetaB hB hθ hθ1)

/-- The intermediate negative-moment estimate in the proof on the literal raw cutoff event,
with the fixed constant C₊ from the mixed high-temperature window. -/
theorem raw_negative_moment_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {beta B h rho : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    (∫ J in physicalRawCutoff N P a B (theta P a B),
      normalizedPartition N P a beta h J ^ (-ConditionalLowerTail.exponent (theta P a B))
        ∂iidLaw μ) ≤ massConstant P a (betaPlus P a B ^ 2) rho := by
  classical
  have hN : 0 < N := by obtain ⟨p, hpP⟩ := hP; have := hp p hpP; have := hpN p hpP; omega
  obtain ⟨hθ, hθ1⟩ := theta_range P a hB hBT
  have hi := integrable_restrictedNegativeMoment μ
    (Subtype.val : Edge N P → Finset (Fin N)) Finset.univ h
    (DisorderOrthogonality.physicalScale N P a beta) hθ hθ1
  have hmeas := measurableSet_inflationCutoff Finset.univ
    (DisorderOrthogonality.physicalScale N P a beta) (theta P a B)
  have hi' : IntegrableOn
      (fun J => normalizedPartition N P a beta h J ^ (-ConditionalLowerTail.exponent (theta P a B)))
      (inflationCutoff Finset.univ (DisorderOrthogonality.physicalScale N P a beta) (theta P a B))
      (iidLaw μ) := by
    apply (integrable_indicator_iff hmeas).mp
    have heq : (inflationCutoff Finset.univ
        (DisorderOrthogonality.physicalScale N P a beta) (theta P a B)).indicator
        (fun J : Edge N P → ℝ => normalizedPartition N P a beta h J ^
          (-ConditionalLowerTail.exponent (theta P a B))) =
        restrictedNegativeMoment (Subtype.val : Edge N P → Finset (Fin N)) Finset.univ h
          (DisorderOrthogonality.physicalScale N P a beta) (theta P a B) := by
      funext J
      simp only [Set.indicator_apply, restrictedNegativeMoment, normalizedGraph_physical]
    rw [heq]
    exact hi
  have hsub := physicalRawCutoff_subset_inflation hN P a hbeta hbetaB hB hθ hθ1
  have hm := setIntegral_mono_set hi'
    (ae_of_all _ (fun J => Real.rpow_nonneg (normalizedPartition_pos N P a beta h J).le _))
    (ae_of_all _ hsub)
  apply hm.trans
  apply (physical_restricted_negative_moment μ hμ N P a beta h hθ hθ1).trans
  exact inflated_graphical_mass μ hunit N P a hP ha hp hpN hbeta hbetaB hB hBT hfield

end Manuscript.UniformLowerTail
