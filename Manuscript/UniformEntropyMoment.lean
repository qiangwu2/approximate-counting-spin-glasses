import Manuscript.UniformEntropy
import Manuscript.UniformTailMoment

noncomputable section
namespace Manuscript.UniformEntropy
open Finset Real SpinGlass.Expansion
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integrating the proved exact-entropy Chernoff bound. -/
theorem entropy_exponential_moment (hV : 0 < Fintype.card V) {lam : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    spinMean (fun σ : V → Bool => Real.exp (lam * ((Fintype.card V : ℝ) * entropy (overlap σ)))) ≤
      1 + 2 * lam / (1 - lam) := by
  have hweights : (∑ _σ : V → Bool, ((2 : ℝ)^Fintype.card V)⁻¹) = 1 := by
    simp [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  have htail : ∀ t : ℝ, 0 ≤ t →
      (∑ σ : V → Bool with t ≤ (Fintype.card V : ℝ) * entropy (overlap σ),
        ((2 : ℝ)^Fintype.card V)⁻¹) ≤ 2 * Real.exp (-t) := by
    intro t ht
    have h := entropy_tail (ι := V) hV ht
    rw [cubeProbability_eq_card] at h
    simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv] using h
  have h := Manuscript.UniformTailMoment.finite_exponential_moment
    (fun _σ : V → Bool => ((2 : ℝ)^Fintype.card V)⁻¹)
    (fun σ => (Fintype.card V : ℝ) * entropy (overlap σ))
    (fun _ => by positivity) hweights
    (fun σ => mul_nonneg (Nat.cast_nonneg _) (entropy_nonneg _)) htail hlam hlam1
  simpa only [spinMean, Finset.mul_sum] using h

end Manuscript.UniformEntropy
