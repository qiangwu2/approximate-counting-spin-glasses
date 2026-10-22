import Manuscript.SKBranchingGaussian

/-! The weak-field branching estimate, including the zero-branching endpoint. -/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKBranching

open MeasureTheory SpinGlass.SKBranching

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fixed_branch_mass_zero (A : Finset V) (hA : A.card = 0)
    {B F φ r : ℝ} (hN : 0 < Fintype.card V)
    (hB : 0 ≤ B) (hB1 : B < 1) (hF : 0 ≤ F) (hφ : 0 ≤ φ) (hr : 0 ≤ r)
    (hNr : (Fintype.card V : ℝ) * r ≤ B ^ 2)
    (hφN : φ * Real.sqrt (Fintype.card V : ℝ) ≤ F) :
    (∑ Γ ∈ branchFamily A, φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) ≤
      massConstant B F := by
  let C := Real.exp (F ^ 2 * B ^ 2 / (1 - B ^ 2))
  have hη := eta_pos hB hB1
  have ht : 1 - eta B < 1 := by linarith
  have hi0 := gaussianIntegrable_tilted_monomial 0 ht
  have hi : GaussianIntegrable (fun x : ℝ => C * Real.exp ((1 - eta B) * x ^ 2 / 2)) := by
    unfold GaussianIntegrable at *
    simpa only [mul_zero, pow_zero, one_mul, mul_assoc] using hi0.const_mul C
  have hpoint (x : ℝ) :
      (∑ d ∈ realizedDegrees A, weightedDegreeMonomial φ r d x) ≤
        C * Real.exp ((1 - eta B) * x ^ 2 / 2) := by
    simpa only [hA, pow_zero, one_mul, C] using
      realized_degree_sum_le_scaled A hN hB hB1 hF hφ hr hNr hφN x
  apply (branchFamily_mass_le_gaussian A hφ hr).trans
  apply (gaussianMean_mono _ _ (realized_degree_sum_nonneg A hφ hr) hi hpoint).trans_eq
  rw [gaussianMean_const_mul]
  have hm := gaussianMean_tilted_even_moment 0 ht
  simp only [mul_zero, pow_zero, one_mul, Nat.cast_zero, zero_add,
    show 1 - (1 - eta B) = eta B by ring] at hm
  rw [hm]
  norm_num [massConstant, C]
  ring

theorem branch_binomial_identity (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    {B F : ℝ} (hη : eta B ≠ 0) :
    (Real.exp 1 * N / b) ^ b *
      (massConstant B F * (degreeConstant B F / (N : ℝ) ^ 2) ^ b *
        (32 / eta B ^ 2) ^ b * (b : ℝ) ^ (2 * b)) =
      massConstant B F * (branchConstant B F * b / N) ^ b := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbR : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [pow_mul]
  have hbase : (Real.exp 1 * N / b) * (degreeConstant B F / (N : ℝ) ^ 2) *
      (32 / eta B ^ 2) * (b : ℝ) ^ 2 = branchConstant B F * b / N := by
    unfold branchConstant
    field_simp
    <;> ring
  calc
    _ = massConstant B F * ((Real.exp 1 * N / b) *
        (degreeConstant B F / (N : ℝ) ^ 2) * (32 / eta B ^ 2) * (b : ℝ) ^ 2) ^ b := by
      simp only [mul_pow]
      ring
    _ = _ := by rw [hbase]

/-- Lemma 4.1 for every positive branching cardinality. The family contains all
simple pair graphs, weighted by the number of odd vertices. -/
theorem branchCard_mass_bound (b : ℕ) (hb : 0 < b)
    {B F φ r : ℝ} (hN : 0 < Fintype.card V)
    (hB : 0 ≤ B) (hB1 : B < 1) (hF : 0 ≤ F) (hφ : 0 ≤ φ) (hr : 0 ≤ r)
    (hNr : (Fintype.card V : ℝ) * r ≤ B ^ 2)
    (hφN : φ * Real.sqrt (Fintype.card V : ℝ) ≤ F) :
    (∑ Γ ∈ branchCardFamily (V := V) b,
      φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) ≤
      massConstant B F * (branchConstant B F * b / Fintype.card V) ^ b := by
  rw [branchCard_mass_eq]
  let K := massConstant B F * (degreeConstant B F / (Fintype.card V : ℝ) ^ 2) ^ b *
      (32 / eta B ^ 2) ^ b * (b : ℝ) ^ (2 * b)
  have hK : 0 ≤ K := by
    have hd := degreeConstant_nonneg hB hF
    have hη := eta_pos hB hB1
    dsimp [K, massConstant]
    positivity
  calc
    _ ≤ ∑ A ∈ (Finset.univ : Finset V).powersetCard b, K := by
      apply Finset.sum_le_sum
      intro A hA
      have hcard := (Finset.mem_powersetCard.mp hA).2
      simpa only [hcard, K] using fixed_branch_mass_bound A (by omega) hN hB hB1 hF hφ hr hNr hφN
    _ = (Nat.choose (Fintype.card V) b : ℝ) * K := by simp
    _ ≤ (Real.exp 1 * Fintype.card V / b) ^ b * K :=
      mul_le_mul_of_nonneg_right (SpinGlass.SupportScalar.binomial_upper_bound _ _) hK
    _ = _ := branch_binomial_identity _ _ hN hb (eta_pos hB hB1).ne'

/-- The zero-branching case of the same estimate, with the convention `0^0=1`. -/
theorem branchCard_mass_zero {B F φ r : ℝ} (hN : 0 < Fintype.card V)
    (hB : 0 ≤ B) (hB1 : B < 1) (hF : 0 ≤ F) (hφ : 0 ≤ φ) (hr : 0 ≤ r)
    (hNr : (Fintype.card V : ℝ) * r ≤ B ^ 2)
    (hφN : φ * Real.sqrt (Fintype.card V : ℝ) ≤ F) :
    (∑ Γ ∈ branchCardFamily (V := V) 0,
      φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) ≤ massConstant B F := by
  rw [branchCard_mass_eq]
  simpa only [Finset.powersetCard_zero, Finset.sum_singleton] using
    fixed_branch_mass_zero (∅ : Finset V) rfl hN hB hB1 hF hφ hr hNr hφN

end Manuscript.SKBranching
