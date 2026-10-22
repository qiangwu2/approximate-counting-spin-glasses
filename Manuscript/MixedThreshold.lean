import Manuscript.UniformEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Data.Nat.Factorial.Basic

/-! The exact variational threshold for finite mixtures of unordered distinct-spin interactions. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.MixedThreshold
open Manuscript.UniformEntropy

/-- The elementary weighted logarithm inequality underlying the entropy duality. -/
theorem weighted_log_le {y b : ℝ} (hy : 0 < y) (hb : 0 < b) :
    y*(Real.log b - Real.log y) ≤ b-y := by
  have h := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb hy)) hy.le
  rw [Real.log_div hb.ne' hy.ne'] at h
  have heq : y*(b/y-1) = b-y := by field_simp
  rwa [heq] at h

/-- Exact entropy is the convex dual upper bound of every sign-cube tilt. -/
theorem entropy_ge_tilt {x : ℝ} (hx : -1 < x) (hx1 : x < 1) (t : ℝ) :
    t*x - Real.log (Real.cosh t) ≤ entropy x := by
  have hp : 0 < 1+x := by linarith
  have hm : 0 < 1-x := by linarith
  have hc := Real.cosh_pos t
  have hplus := weighted_log_le hp (div_pos (Real.exp_pos t) hc)
  have hminus := weighted_log_le hm (div_pos (Real.exp_pos (-t)) hc)
  rw [Real.log_div (Real.exp_pos t).ne' hc.ne', Real.log_exp] at hplus
  rw [Real.log_div (Real.exp_pos (-t)).ne' hc.ne', Real.log_exp] at hminus
  have hnorm : Real.exp t / Real.cosh t + Real.exp (-t) / Real.cosh t = 2 := by
    have htwo : Real.exp t + Real.exp (-t) = 2*Real.cosh t := by rw [Real.cosh_eq]; ring
    rw [← add_div, htwo]
    field_simp
  unfold entropy
  nlinarith

/-- The exact entropy dominates its quadratic term, including the endpoint. -/
theorem entropy_ge_half_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x^2/2 ≤ entropy x := by
  obtain hxlt | rfl := hx1.lt_or_eq
  · have ht := entropy_ge_tilt (by linarith) hxlt x
    have hc := Real.log_le_log (Real.cosh_pos x) (Real.cosh_le_exp_half_sq x)
    rw [Real.log_exp] at hc
    nlinarith
  · rw [entropy_one]
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h

/-- A matching upper estimate near zero, proved with elementary logarithm bounds. -/
theorem entropy_le_half_sq_mul_one_add {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    entropy x ≤ x^2*(1+x)/2 := by
  have hp : 0 < 1+x := by linarith
  have hm : 0 < 1-x := by linarith
  have hpq : 0 < 1-x^2 := by nlinarith
  have hplus := Real.log_le_sub_one_of_pos hp
  have hprod := Real.log_le_sub_one_of_pos hpq
  have heq : Real.log (1-x^2) = Real.log (1+x)+Real.log (1-x) := by
    rw [← Real.log_mul hp.ne' hm.ne']
    congr 1
    ring
  have h1 := mul_le_mul_of_nonneg_left hplus hx
  have h2 := mul_le_mul_of_nonneg_left hprod hm.le
  rw [heq] at h2
  unfold entropy
  nlinarith


/-- The interaction polynomial in equation (5). -/
def xi (P : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ P, a p ^ 2 * x ^ p / (p.factorial : ℝ)

/-- The squared threshold is the exact entropy/interaction variational infimum. -/
def thresholdSquared (P : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  sInf ((fun x : ℝ => entropy x / xi P a x) '' Set.Ioc 0 1)

/-- The repeated-site correction, with its combinatorial factorial expression. -/
def delta (P : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, a p ^ 2 * ((p.choose 2 : ℝ) / (p.factorial : ℝ))

theorem xi_nonneg (P : Finset ℕ) (a : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ xi P a x := by
  apply Finset.sum_nonneg
  intro p hp
  positivity

theorem xi_pos (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) {x : ℝ} (hx : 0 < x) : 0 < xi P a x := by
  apply Finset.sum_pos
  · intro p hp
    exact div_pos (mul_pos (sq_pos_of_pos (ha p hp)) (pow_pos hx p))
      (Nat.cast_pos.mpr (Nat.factorial_pos p))
  · exact hP

theorem xi_zero (P : Finset ℕ) (a : ℕ → ℝ) (hp : ∀ p ∈ P, 1 ≤ p) :
    xi P a 0 = 0 := by
  apply Finset.sum_eq_zero
  intro p hpP
  simp [show p ≠ 0 by have := hp p hpP; omega]

theorem xi_le_abs (P : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    xi P a x ≤ xi P a |x| := by
  apply Finset.sum_le_sum
  intro p hp
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  simpa only [abs_pow] using le_abs_self (x ^ p)

theorem xi_le_one_mul_sq (P : Finset ℕ) (a : ℕ → ℝ)
    (hp : ∀ p ∈ P, 2 ≤ p) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    xi P a x ≤ xi P a 1 * x ^ 2 := by
  unfold xi
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hpP
  have hpow := pow_le_pow_of_le_one hx hx1 (hp p hpP)
  have hh := mul_le_mul_of_nonneg_left hpow
    (div_nonneg (sq_nonneg (a p)) (Nat.cast_nonneg p.factorial))
  simpa only [one_pow, mul_one, div_mul_eq_mul_div, mul_div_assoc] using hh

theorem threshold_set_nonempty (P : Finset ℕ) (a : ℕ → ℝ) :
    ((fun x : ℝ => entropy x / xi P a x) '' Set.Ioc 0 1).Nonempty :=
  Set.Nonempty.image _ ⟨1, by norm_num⟩

theorem threshold_set_bddBelow (P : Finset ℕ) (a : ℕ → ℝ) :
    BddBelow ((fun x : ℝ => entropy x / xi P a x) '' Set.Ioc 0 1) := by
  refine ⟨0, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact div_nonneg (entropy_nonneg x) (xi_nonneg P a hx.1.le)

theorem thresholdSquared_le (P : Finset ℕ) (a : ℕ → ℝ) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    thresholdSquared P a ≤ entropy x / xi P a x :=
  csInf_le (threshold_set_bddBelow P a) ⟨x, ⟨hx, hx1⟩, rfl⟩

theorem thresholdSquared_le_endpoint (P : Finset ℕ) (a : ℕ → ℝ) :
    thresholdSquared P a ≤ Real.log 2 / xi P a 1 := by
  simpa using thresholdSquared_le P a (x := 1) (by norm_num) le_rfl

theorem half_inv_xi_one_le_thresholdSquared (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) :
    1 / (2 * xi P a 1) ≤ thresholdSquared P a := by
  have hxi1 : 0 < xi P a 1 := xi_pos P a hP ha (by norm_num)
  apply le_csInf (threshold_set_nonempty P a)
  rintro y ⟨x, hx, rfl⟩
  have hxip : 0 < xi P a x := xi_pos P a hP ha hx.1
  have hquad := entropy_ge_half_sq hx.1.le hx.2
  have hxi := xi_le_one_mul_sq P a hp hx.1.le hx.2
  apply (le_div_iff₀ hxip).2
  have hmul := mul_le_mul_of_nonneg_left hxi (by positivity : 0 ≤ 1 / (2 * xi P a 1))
  have heq : 1 / (2 * xi P a 1) * (xi P a 1 * x ^ 2) = x ^ 2 / 2 := by
    field_simp
  rw [heq] at hmul
  exact hmul.trans hquad

theorem thresholdSquared_pos (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) :
    0 < thresholdSquared P a :=
  lt_of_lt_of_le (by positivity [xi_pos P a hP ha (x := 1) (by norm_num)])
    (half_inv_xi_one_le_thresholdSquared P a hP ha hp)

/-- The full mixed variational inequality, also for negative overlaps and odd orders. -/
theorem scaled_xi_le_entropy (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    {v x : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared P a) (hx : |x| ≤ 1) :
    v * xi P a x ≤ (v / thresholdSquared P a) * entropy x := by
  have hT := thresholdSquared_pos P a hP ha hp
  by_cases hx0 : x = 0
  · subst x
    rw [xi_zero P a (fun p h => by have := hp p h; omega), entropy_zero]
    simp
  have hxi := xi_pos P a hP ha (abs_pos.mpr hx0)
  have hbase := (le_div_iff₀ hxi).1
    (thresholdSquared_le P a (abs_pos.mpr hx0) hx)
  rw [entropy_abs] at hbase
  have hscale := mul_le_mul_of_nonneg_left hbase (div_nonneg hv hT.le)
  have hcancel : (v / thresholdSquared P a) * (thresholdSquared P a * xi P a |x|) =
      v * xi P a |x| := by field_simp
  rw [hcancel] at hscale
  exact (mul_le_mul_of_nonneg_left (xi_le_abs P a x) hv).trans hscale

end Manuscript.MixedThreshold
