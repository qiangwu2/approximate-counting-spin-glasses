import Manuscript.MixedThreshold
import Manuscript.Model

noncomputable section
open scoped BigOperators
namespace Manuscript.MixedCoefficient
open Manuscript.MixedThreshold Manuscript.Model

theorem factorial_succ_le_pow (k : ℕ) : (k + 1).factorial ≤ (k + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (k + 1 + 1).factorial = (k + 2) * (k + 1).factorial := by rw [Nat.factorial_succ]
      _ ≤ (k + 2) * (k + 1) ^ k := Nat.mul_le_mul_left _ ih
      _ ≤ (k + 2) * (k + 2) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (k + 1 + 1) ^ (k + 1) := by simp only [Nat.pow_succ, Nat.add_assoc, Nat.reduceAdd, Nat.mul_comm]

theorem factorial_le_pow_pred {p : ℕ} (hp : 1 ≤ p) : p.factorial ≤ p ^ (p - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  simpa using factorial_succ_le_pow k


/-- The inflated deterministic edge weight in Proposition 2.2, where `v=β₊²`. -/
def comparisonWeight (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (v : ℝ)
    (e : Edge N P) : ℝ :=
  v * a e.val.card ^ 2 / (N : ℝ) ^ (e.val.card - 1)

theorem xi_one_term_le (P : Finset ℕ) (a : ℕ → ℝ) {p : ℕ} (hp : p ∈ P) :
    a p ^ 2 / (p.factorial : ℝ) ≤ xi P a 1 := by
  have hh := Finset.single_le_sum (s := P)
    (f := fun p => a p ^ 2 * (1 : ℝ) ^ p / (p.factorial : ℝ))
    (fun p hp => by positivity) hp
  simpa [xi] using hh

theorem interaction_one_lt_log_two (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p)
    {v : ℝ} (hvT : v < thresholdSquared P a) :
    v * xi P a 1 < Real.log 2 := by
  have hx := xi_pos P a hP ha (x := 1) (by norm_num)
  exact (lt_div_iff₀ hx).mp (hvT.trans_le (thresholdSquared_le_endpoint P a))

theorem scaled_coefficient_lt_pow (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) {p : ℕ} (hpP : p ∈ P) (hp : 1 ≤ p)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared P a) :
    v * a p ^ 2 < (p : ℝ) ^ (p - 1) := by
  have h1 := mul_le_mul_of_nonneg_left (xi_one_term_le P a hpP) hv
  have h2 := interaction_one_lt_log_two P a hP ha hvT
  have hfrac : v * a p ^ 2 / (p.factorial : ℝ) < Real.log 2 := by
    simpa only [mul_div_assoc] using h1.trans_lt h2
  have hf : (0 : ℝ) < p.factorial := Nat.cast_pos.mpr (Nat.factorial_pos p)
  have h3 := (div_lt_iff₀ hf).mp hfrac
  have hlog : Real.log 2 < 1 := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at hh
    exact hh
  have hfact : (p.factorial : ℝ) ≤ (p : ℝ) ^ (p - 1) := by
    exact_mod_cast factorial_le_pow_pred hp
  have hprod : Real.log 2 * (p.factorial : ℝ) < p.factorial := by nlinarith
  exact h3.trans_le (hprod.le.trans hfact)

/-- All comparison coefficients lie in `[0,1)`, including the smallest system. -/
theorem comparisonWeight_range (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {v : ℝ} (hv : 0 ≤ v)
    (hvT : v < thresholdSquared P a) (e : Edge N P) :
    0 ≤ comparisonWeight N P a v e ∧ comparisonWeight N P a v e < 1 := by
  have he := edge_order_mem e
  have he2 := hp _ he
  have heN := hpN _ he
  have hN : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  constructor
  · unfold comparisonWeight
    positivity
  · unfold comparisonWeight
    apply (div_lt_one (pow_pos hN _)).2
    have hlt := scaled_coefficient_lt_pow P a hP ha he (by omega) hv hvT
    exact hlt.trans_le (pow_le_pow_left₀ (by positivity) (by exact_mod_cast heN) _)

end Manuscript.MixedCoefficient
