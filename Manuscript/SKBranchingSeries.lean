import Manuscript.SKBranchingFinite

/-! Finite odd/even degree series for the weak-field Gaussian majorant. -/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKBranching

open SpinGlass.SKBranching

/-- The odd branching series starts at degree three, with coefficient `1/6`. -/
theorem odd_branching_factorial_lower (j : ℕ) :
    6 * 2 ^ j * j.factorial ≤ (2 * j + 3).factorial := by
  have hd := Nat.doubleFactorial_le_factorial (2 * j)
  rw [Nat.doubleFactorial_two_mul] at hd
  have hp : (2 * j).factorial * (3 : ℕ).factorial ≤ (2 * j + 3).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  apply (show 6 * 2 ^ j * j.factorial ≤ (2 * j).factorial * (3 : ℕ).factorial from ?_).trans hp
  norm_num
  nlinarith

theorem finite_odd_branching_series_le {x : ℝ} (hx : 0 ≤ x) (K : ℕ) :
    (∑ j ∈ Finset.range K, x ^ (2 * j + 3) / (2 * j + 3).factorial) ≤
      x ^ 3 / 6 * Real.exp (x ^ 2 / 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range K, x ^ 3 / 6 * ((x ^ 2 / 2) ^ j / j.factorial) := by
      apply Finset.sum_le_sum
      intro j hj
      have hf : (6 : ℝ) * 2 ^ j * (j.factorial : ℝ) ≤ (2 * j + 3).factorial := by
        exact_mod_cast odd_branching_factorial_lower j
      have hd : 0 < (6 : ℝ) * 2 ^ j * (j.factorial : ℝ) := by positivity
      calc
        _ ≤ x ^ (2 * j + 3) / ((6 : ℝ) * 2 ^ j * (j.factorial : ℝ)) :=
          div_le_div_of_nonneg_left (pow_nonneg hx _) hd hf
        _ = _ := by rw [pow_add, pow_mul, div_pow]; ring
    _ = x ^ 3 / 6 * ∑ j ∈ Finset.range K, (x ^ 2 / 2) ^ j / j.factorial := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (by positivity) K)
      (by positivity)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both parities are permitted at branching vertices. -/
def degreeChoices (A : Finset V) (K : ℕ) (v : V) : Finset ℕ :=
  if v ∈ A then
    (Finset.range K).image (fun j => 2 * j + 3) ∪
      (Finset.range K).image (fun j => 2 * j + 4)
  else {0, 1, 2}

def vertexDegreeTerm (φ x : ℝ) (d : ℕ) : ℝ :=
  (if Even d then 1 else φ) * x ^ d / d.factorial

def degreePolynomial (A : Finset V) (K : ℕ) (φ r x : ℝ) : ℝ :=
  ∏ v, ∑ d ∈ degreeChoices A K v, vertexDegreeTerm φ (Real.sqrt r * |x|) d

theorem vertexDegreeTerm_nonneg {φ x : ℝ} (hφ : 0 ≤ φ) (hx : 0 ≤ x) (d : ℕ) :
    0 ≤ vertexDegreeTerm φ x d := by
  unfold vertexDegreeTerm
  apply div_nonneg (mul_nonneg ?_ (pow_nonneg hx _)) (Nat.cast_nonneg _)
  split_ifs <;> positivity

theorem odd_even_degree_images_disjoint (K : ℕ) :
    Disjoint ((Finset.range K).image (fun j => 2 * j + 3))
      ((Finset.range K).image (fun j => 2 * j + 4)) := by
  apply Finset.disjoint_left.mpr
  intro n hn hm
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hm
  omega

theorem branching_vertex_series_le {φ x : ℝ} (hφ : 0 ≤ φ) (hx : 0 ≤ x) (K : ℕ) :
    (∑ d ∈ (Finset.range K).image (fun j => 2 * j + 3) ∪
        (Finset.range K).image (fun j => 2 * j + 4), vertexDegreeTerm φ x d) ≤
      (φ * x ^ 3 / 6 + x ^ 4 / 24) * Real.exp (x ^ 2 / 2) := by
  rw [Finset.sum_union (odd_even_degree_images_disjoint K),
    Finset.sum_image (fun i hi j hj h => by omega),
    Finset.sum_image (fun i hi j hj h => by omega)]
  have ho (j : ℕ) : ¬Even (2 * j + 3) := by rw [Nat.even_iff]; omega
  have he (j : ℕ) : Even (2 * j + 4) := by rw [Nat.even_iff]; omega
  simp only [vertexDegreeTerm, ho, he, if_false, if_true, one_mul, mul_div_assoc,
    ← Finset.mul_sum]
  have hb := mul_le_mul_of_nonneg_left (finite_odd_branching_series_le hx K) hφ
  have hc := finite_branching_series_le x K
  nlinarith

theorem nonbranch_vertex_series_le {φ x : ℝ} :
    (∑ d ∈ ({0, 1, 2} : Finset ℕ), vertexDegreeTerm φ x d) ≤
      Real.exp (φ * x + x ^ 2 / 2) := by
  have hb := Real.add_one_le_exp (φ * x + x ^ 2 / 2)
  norm_num [vertexDegreeTerm] at *
  linarith

theorem degreePolynomial_nonneg (A : Finset V) (K : ℕ) {φ : ℝ} (hφ : 0 ≤ φ)
    (r x : ℝ) : 0 ≤ degreePolynomial A K φ r x := by
  apply Finset.prod_nonneg
  intro v hv
  exact Finset.sum_nonneg (fun d hd => vertexDegreeTerm_nonneg hφ (by positivity) d)

/-- The product over vertices gives the manuscript's cubic/quartic branching factor. -/
theorem degreePolynomial_le (A : Finset V) (K : ℕ) {φ : ℝ} (hφ : 0 ≤ φ)
    (r x : ℝ) :
    degreePolynomial A K φ r x ≤
      (φ * (Real.sqrt r * |x|) ^ 3 / 6 + (Real.sqrt r * |x|) ^ 4 / 24) ^ A.card *
        Real.exp ((Fintype.card V : ℝ) * φ * (Real.sqrt r * |x|) +
          (Fintype.card V : ℝ) * (Real.sqrt r * |x|) ^ 2 / 2) := by
  let y := Real.sqrt r * |x|
  let c := φ * y ^ 3 / 6 + y ^ 4 / 24
  have hy : 0 ≤ y := by positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hvertex (v : V) : (∑ d ∈ degreeChoices A K v, vertexDegreeTerm φ y d) ≤
      (if v ∈ A then c else 1) * Real.exp (φ * y + y ^ 2 / 2) := by
    by_cases hv : v ∈ A
    · simp only [degreeChoices, hv, if_true]
      exact (branching_vertex_series_le hφ hy K).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hc)
    · simp only [degreeChoices, hv, if_false, one_mul]
      exact nonbranch_vertex_series_le
  apply (Finset.prod_le_prod (fun v hv =>
    Finset.sum_nonneg (fun d hd => vertexDegreeTerm_nonneg hφ hy d))
      (fun v hv => hvertex v)).trans_eq
  rw [Finset.prod_mul_distrib]
  have hprod : (∏ v : V, if v ∈ A then c else 1) = c ^ A.card := by
    rw [Finset.prod_ite_mem_eq, Finset.prod_const]
  rw [hprod, Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
  congr 2
  dsimp [c, y]
  ring

end Manuscript.SKBranching
