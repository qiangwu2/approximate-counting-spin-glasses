import Manuscript.SKBranchingSeries

/-! From actual weighted degree signatures to the explicit product majorant. -/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKBranching

open SpinGlass.SKBranching

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem field_degree_product (φ : ℝ) (d : V → ℕ) :
    (∏ v, if Even (d v) then (1 : ℝ) else φ) = φ ^ oddCount d := by
  have hp : (∏ v, if Even (d v) then (1 : ℝ) else φ) =
      ∏ v ∈ Finset.univ.filter (fun v => ¬Even (d v)), φ := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v hv
    split_ifs <;> rfl
  rw [hp]
  simp [oddCount]

/-- Even total degree permits use of the nonnegative Gaussian magnitude. -/
theorem degreeMonomial_abs {r : ℝ} (hr : 0 ≤ r) (d : V → ℕ)
    {k : ℕ} (hsum : ∑ v, d v = 2 * k) (x : ℝ) :
    degreeMonomial r d |x| = degreeMonomial r d x := by
  rw [degreeMonomial_eq r hr d hsum, degreeMonomial_eq r hr d hsum, pow_abs_two_mul]

theorem weightedDegreeMonomial_eq_product {φ r : ℝ} (hr : 0 ≤ r) (d : V → ℕ)
    {k : ℕ} (hsum : ∑ v, d v = 2 * k) (x : ℝ) :
    weightedDegreeMonomial φ r d x =
      ∏ v, vertexDegreeTerm φ (Real.sqrt r * |x|) (d v) := by
  simp only [vertexDegreeTerm, mul_div_assoc, Finset.prod_mul_distrib, field_degree_product]
  change φ ^ oddCount d * degreeMonomial r d x =
    φ ^ oddCount d * degreeMonomial r d |x|
  rw [degreeMonomial_abs hr d hsum]

theorem realizedDegrees_cover (A : Finset V) (d : V → ℕ)
    (hd : d ∈ realizedDegrees A) :
    d ∈ Fintype.piFinset (degreeChoices A (Fintype.card (Finset V) + 1)) := by
  obtain ⟨Γ, hΓ, rfl⟩ := Finset.mem_image.mp hd
  have hb : SKGraph.branch id Γ = A := (Finset.mem_filter.mp hΓ).2
  apply Fintype.mem_piFinset.mpr
  intro v
  have hdeg : SpinGlass.Hypergraph.degree Γ v ≤ Fintype.card (Finset V) :=
    (Finset.card_filter_le _ _).trans (Finset.card_le_univ Γ)
  have hbiff : v ∈ A ↔ 3 ≤ SpinGlass.Hypergraph.degree Γ v := by
    rw [← hb]
    exact SKGraph.mem_branch id Γ v
  unfold degreeChoices
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    have hthree := hbiff.mp hv
    by_cases he : Even (SpinGlass.Hypergraph.degree Γ v)
    · have hmod := Nat.even_iff.mp he
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨SpinGlass.Hypergraph.degree Γ v / 2 - 2,
        Finset.mem_range.mpr (by omega), by omega⟩
    · have hmod := Nat.not_even_iff_odd.mp he
      rw [Nat.odd_iff] at hmod
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨SpinGlass.Hypergraph.degree Γ v / 2 - 1,
        Finset.mem_range.mpr (by omega), by omega⟩
  · rw [if_neg hv]
    have hn : ¬3 ≤ SpinGlass.Hypergraph.degree Γ v := fun hh => hv (hbiff.mpr hh)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

theorem degreePolynomial_eq_sum (A : Finset V) (K : ℕ) (φ r x : ℝ) :
    degreePolynomial A K φ r x =
      ∑ d ∈ Fintype.piFinset (degreeChoices A K),
        ∏ v, vertexDegreeTerm φ (Real.sqrt r * |x|) (d v) :=
  Finset.prod_univ_sum _ _

theorem realized_degree_sum_nonneg (A : Finset V) {φ r : ℝ}
    (hφ : 0 ≤ φ) (hr : 0 ≤ r) (x : ℝ) :
    0 ≤ ∑ d ∈ realizedDegrees A, weightedDegreeMonomial φ r d x := by
  apply Finset.sum_nonneg
  intro d hd
  obtain ⟨k, hk⟩ := realizedDegrees_even A d hd
  rw [weightedDegreeMonomial_eq_product hr d hk]
  exact Finset.prod_nonneg (fun v hv => vertexDegreeTerm_nonneg hφ (by positivity) _)

/-- Adding all unrealized coordinatewise degree choices adds nonnegative terms. -/
theorem realized_degree_sum_le_polynomial (A : Finset V) {φ r : ℝ}
    (hφ : 0 ≤ φ) (hr : 0 ≤ r) (x : ℝ) :
    (∑ d ∈ realizedDegrees A, weightedDegreeMonomial φ r d x) ≤
      degreePolynomial A (Fintype.card (Finset V) + 1) φ r x := by
  rw [degreePolynomial_eq_sum]
  calc
    _ = ∑ d ∈ realizedDegrees A,
        ∏ v, vertexDegreeTerm φ (Real.sqrt r * |x|) (d v) := by
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨k, hk⟩ := realizedDegrees_even A d hd
      exact weightedDegreeMonomial_eq_product hr d hk x
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (realizedDegrees_cover A)
      (fun d hd hnot => Finset.prod_nonneg
        (fun v hv => vertexDegreeTerm_nonneg hφ (by positivity) _))

/-- The first Gaussian integrand majorization in Lemma 4.1, with actual field weights. -/
theorem realized_degree_sum_le_majorant (A : Finset V) {φ r : ℝ}
    (hφ : 0 ≤ φ) (hr : 0 ≤ r) (x : ℝ) :
    (∑ d ∈ realizedDegrees A, weightedDegreeMonomial φ r d x) ≤
      (φ * (Real.sqrt r * |x|) ^ 3 / 6 + (Real.sqrt r * |x|) ^ 4 / 24) ^ A.card *
        Real.exp ((Fintype.card V : ℝ) * φ * (Real.sqrt r * |x|) +
          (Fintype.card V : ℝ) * (Real.sqrt r * |x|) ^ 2 / 2) :=
  (realized_degree_sum_le_polynomial A hφ hr x).trans
    (degreePolynomial_le A (Fintype.card (Finset V) + 1) hφ r x)

end Manuscript.SKBranching
