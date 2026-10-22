import Manuscript.MixedCoefficient
import Manuscript.UniformOverlap

/-! Distinct-index interaction comparison for the actual finite mixed model. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.MixedEnergy
open SpinGlass.Expansion Manuscript.Model Manuscript.MixedThreshold
open Manuscript.MixedCoefficient Manuscript.UniformEntropy Manuscript.UniformOverlap

/-- The actual physical edges split disjointly according to their cardinalities. -/
theorem physical_sum_by_order (N : ℕ) (P : Finset ℕ) (f : Finset (Fin N) → ℝ) :
    (∑ e : Edge N P, f e.val) =
      ∑ p ∈ P, ∑ e ∈ (Finset.univ : Finset (Fin N)).powersetCard p, f e := by
  calc
    (∑ e : Edge N P, f e.val) = ∑ e ∈ physicalEdges N P, f e := by
      exact (Finset.sum_subtype (physicalEdges N P) (fun _ => Iff.rfl) f).symm
    _ = ∑ p ∈ P, ∑ e ∈ (Finset.univ : Finset (Finset (Fin N))).filter
        (fun e => e.card = p), f e := by
      rw [Finset.sum_fiberwise_eq_sum_filter]
      rfl
    _ = ∑ p ∈ P, ∑ e ∈ (Finset.univ : Finset (Fin N)).powersetCard p, f e := by
      apply Finset.sum_congr rfl
      intro p hp
      congr 1
      ext e
      simp

/-- The comparison interaction sum is the weighted sum of the pure-order
auxiliary energies, with all distinct-index normalizations preserved. -/
theorem comparisonEnergy_eq_sum (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (v : ℝ) (σ : Fin N → Bool) :
    (∑ e : Edge N P, comparisonWeight N P a v e * edgeCharacter Subtype.val σ e) =
      ∑ p ∈ P, v * a p ^ 2 * auxiliaryEnergy p σ := by
  change (∑ e : Edge N P,
    (v * a e.val.card ^ 2 / (N : ℝ) ^ (e.val.card - 1)) * edgeCharacter id σ e.val) = _
  rw [physical_sum_by_order N P (fun e : Finset (Fin N) =>
    (v * a e.card ^ 2 / (N : ℝ) ^ (e.card - 1)) * edgeCharacter id σ e)]
  apply Finset.sum_congr rfl
  intro p hp
  unfold auxiliaryEnergy
  simp only [Fintype.card_fin]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [(Finset.mem_powersetCard.mp he).2]
  ring

/-- The repeated-site discrepancy summed over the finite mixture, before
using the entropy threshold. -/
theorem comparisonEnergy_le_polynomial (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hp : ∀ p ∈ P, 2 ≤ p) (hpN : ∀ p ∈ P, p ≤ N)
    {v : ℝ} (hv : 0 ≤ v) (σ : Fin N → Bool) :
    (∑ e : Edge N P, comparisonWeight N P a v e * edgeCharacter Subtype.val σ e) ≤
      v * (N : ℝ) * xi P a (overlap σ) + v * MixedThreshold.delta P a := by
  rw [comparisonEnergy_eq_sum]
  calc
    _ ≤ ∑ p ∈ P, v * a p ^ 2 *
        ((N : ℝ) * overlap σ ^ p / (p.factorial : ℝ) + UniformOverlap.delta p) := by
      apply Finset.sum_le_sum
      intro p hpP
      have he := (abs_le.mp (auxiliaryEnergy_error (V := Fin N) p
        (by have := hp p hpP; omega) (by simpa using hpN p hpP) σ)).2
      have he' : auxiliaryEnergy p σ ≤
          (N : ℝ) * overlap σ ^ p / (p.factorial : ℝ) + UniformOverlap.delta p := by
        simpa only [Fintype.card_fin] using (by linarith : auxiliaryEnergy p σ ≤
          (Fintype.card (Fin N) : ℝ) * overlap σ ^ p / (p.factorial : ℝ) + UniformOverlap.delta p)
      exact mul_le_mul_of_nonneg_left he' (mul_nonneg hv (sq_nonneg _))
    _ = _ := by
      unfold xi MixedThreshold.delta UniformOverlap.delta
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hpP
      ring

/-- Uniform pointwise entropy upper bound for the actual mixed physical energy. -/
theorem comparisonEnergy_le_entropy (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {v : ℝ} (hv : 0 ≤ v)
    (hvT : v < thresholdSquared P a) (σ : Fin N → Bool) :
    (∑ e : Edge N P, comparisonWeight N P a v e * edgeCharacter Subtype.val σ e) ≤
      v * MixedThreshold.delta P a +
        (v / thresholdSquared P a) * ((N : ℝ) * entropy (overlap σ)) := by
  obtain ⟨p, hpP⟩ := hP
  have hN : 0 < N := by have := hp p hpP; have := hpN p hpP; omega
  have hvar := scaled_xi_le_entropy P a ⟨p, hpP⟩ ha hp hv hvT
    (abs_overlap_le_one (ι := Fin N) (by simpa using hN) σ)
  have hscaled := mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have he := comparisonEnergy_le_polynomial N P a hp hpN hv σ
  nlinarith

end Manuscript.MixedEnergy
