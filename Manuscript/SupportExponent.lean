import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar exponent estimate for the higher-order support truncation

This file proves the degree/field tradeoff in Lemma 3.1 of the supplied manuscript.
The combinatorial counting and probabilistic edge-weight estimates are proved
separately in the SupportMass modules and SupportDisorder.
-/

noncomputable section

namespace Manuscript.SupportExponent

/-- The exponent selected by the two possible degree regimes in Lemma 3.1. -/
def kappa (p alpha : ℝ) : ℝ :=
  min ((p - 2) / p) (2 * alpha - 1 / p)

/-- The uniform exponent when the weak-field parameter satisfies `alpha ≥ 1/4`. -/
def kappaMin (p : ℝ) : ℝ := (p - 2) / (2 * p)

/-- The exponent before minimizing over the total degree. -/
def degreeExponent (p alpha v d : ℝ) : ℝ :=
  -v + (p - 1) / p * d + 2 * alpha * max (2 * v - d) 0

private theorem coefficient_eq (p : ℝ) (hp : 0 < p) :
    (p - 1) / p = 1 - 1 / p := by
  field_simp

private theorem endpoint_eq (p : ℝ) (hp : 0 < p) :
    (p - 2) / p = 1 - 2 * (1 / p) := by
  field_simp

/-- The slope of the degree contribution is nonnegative for orders at least one. -/
theorem degree_coefficient_nonneg (p : ℝ) (hp : 1 ≤ p) :
    0 ≤ (p - 1) / p := by
  exact div_nonneg (by linarith) (by linarith)

/-- The weak-field exponent is at least the uniform positive exponent. -/
theorem kappa_ge_kappaMin (p alpha : ℝ) (hp : 3 ≤ p)
    (ha : (1 : ℝ) / 4 ≤ alpha) : kappaMin p ≤ kappa p alpha := by
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 * p := by positivity
  apply le_min
  · dsimp [kappaMin]
    apply (div_le_div_iff₀ h2p hp0).2
    nlinarith
  · dsimp [kappaMin]
    apply (div_le_iff₀ h2p).2
    have hcancel : (1 / p) * p = (1 : ℝ) := by field_simp
    nlinarith [mul_nonneg (by linarith : 0 ≤ 4 * alpha - 1) (le_of_lt hp0)]

/-- The uniform exponent is strictly positive for every interaction order ≥ 3. -/
theorem kappaMin_pos (p : ℝ) (hp : 3 ≤ p) : 0 < kappaMin p := by
  dsimp [kappaMin]
  apply div_pos <;> linarith

/-- Hence the selected exponent is positive throughout the weak-field range. -/
theorem kappa_pos (p alpha : ℝ) (hp : 3 ≤ p)
    (ha : (1 : ℝ) / 4 ≤ alpha) : 0 < kappa p alpha :=
  lt_of_lt_of_le (kappaMin_pos p hp) (kappa_ge_kappaMin p alpha hp ha)

/-- The selected exponent never exceeds the zero-field exponent. -/
theorem kappa_le_zero_field (p alpha : ℝ) :
    kappa p alpha ≤ (p - 2) / p := min_le_left _ _

/-- If total degree lies between `v` and `2v`, the degree exponent is an
explicit nonnegative linear combination of its two endpoint slopes. -/
theorem degreeExponent_eq_interpolation (p alpha v d : ℝ) (hp : 0 < p)
    (hd : d ≤ 2 * v) :
    degreeExponent p alpha v d =
      (2 * v - d) * (2 * alpha - 1 / p) + (d - v) * ((p - 2) / p) := by
  unfold degreeExponent
  rw [max_eq_left (by linarith)]
  rw [coefficient_eq p hp, endpoint_eq p hp]
  ring

/-- The scalar degree/field tradeoff underlying Lemma 3.1.

The proof itself only needs `p ≥ 1`; its application in the manuscript has
`p ≥ 3`, `alpha ≥ 1/4`, `v ≥ 1`, and `d ≥ v`. -/
theorem degreeExponent_ge_kappa (p alpha v d : ℝ) (hp : 1 ≤ p)
    (hv : 0 ≤ v) (hd : v ≤ d) :
    kappa p alpha * v ≤ degreeExponent p alpha v d := by
  have hp0 : 0 < p := by linarith
  have hkA : kappa p alpha ≤ 2 * alpha - 1 / p := min_le_right _ _
  have hkB : kappa p alpha ≤ (p - 2) / p := min_le_left _ _
  by_cases hsmall : d ≤ 2 * v
  · rw [degreeExponent_eq_interpolation p alpha v d hp0 hsmall]
    have hA := mul_le_mul_of_nonneg_left hkA (by linarith : 0 ≤ 2 * v - d)
    have hB := mul_le_mul_of_nonneg_left hkB (by linarith : 0 ≤ d - v)
    nlinarith
  · have hlarge : 2 * v ≤ d := le_of_lt (lt_of_not_ge hsmall)
    have hmax : max (2 * v - d) 0 = 0 := max_eq_right (by linarith)
    have hB := mul_le_mul_of_nonneg_right hkB hv
    have hcoeff := degree_coefficient_nonneg p hp
    have hgrowth := mul_le_mul_of_nonneg_left hlarge hcoeff
    have hendpoint : -v + (p - 1) / p * (2 * v) = ((p - 2) / p) * v := by
      rw [coefficient_eq p hp0, endpoint_eq p hp0]
      ring
    unfold degreeExponent
    rw [hmax]
    nlinarith

/-- At zero field, only even-degree graphs survive, so `d ≥ 2v`; the
unpenalized degree exponent already has the zero-field lower bound. -/
theorem zero_field_degree_bound (p v d : ℝ) (hp : 1 ≤ p)
    (hd : 2 * v ≤ d) :
    ((p - 2) / p) * v ≤ -v + (p - 1) / p * d := by
  have hp0 : 0 < p := by linarith
  have hgrowth := mul_le_mul_of_nonneg_left hd (degree_coefficient_nonneg p hp)
  have hendpoint : -v + (p - 1) / p * (2 * v) = ((p - 2) / p) * v := by
    rw [coefficient_eq p hp0, endpoint_eq p hp0]
    ring
  linarith

/-- The exponent reaches its zero-field value at the field-decay threshold
specified after Lemma 3.1. -/
theorem kappa_eq_zero_field (p alpha : ℝ) (hp : 0 < p)
    (ha : (p - 1) / (2 * p) ≤ alpha) :
    kappa p alpha = (p - 2) / p := by
  apply min_eq_left
  have h2p : 0 < 2 * p := by positivity
  have ha' := (div_le_iff₀ h2p).1 ha
  apply (div_le_iff₀ hp).2
  have hcancel : (1 / p) * p = (1 : ℝ) := by field_simp
  nlinarith

/-- If `p` is an active order at least `pMin`, its edge normalization contributes
at least the fraction `(pMin-1)/pMin` of its incidence degree. -/
theorem edge_normalization_bound (pMin p : ℝ) (hm : 0 < pMin)
    (hp : pMin ≤ p) :
    (pMin - 1) / pMin * p ≤ p - 1 := by
  have hcancel : ((pMin - 1) / pMin) * pMin = pMin - 1 := by
    field_simp
  apply (mul_le_mul_iff_right₀ hm).1
  nlinarith

/-- The finite weighted-degree inequality used before minimizing `g(d)` in
Lemma 3.1. Counts are permitted to be arbitrary nonnegative reals. -/
theorem total_edge_normalization_bound {ι : Type*} (s : Finset ι)
    (orders counts : ι → ℝ) (pMin : ℝ) (hm : 0 < pMin)
    (hp : ∀ i ∈ s, pMin ≤ orders i) (hc : ∀ i ∈ s, 0 ≤ counts i) :
    (pMin - 1) / pMin * (∑ i ∈ s, orders i * counts i) ≤
      ∑ i ∈ s, (orders i - 1) * counts i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (edge_normalization_bound pMin (orders i) hm (hp i hi))
    (hc i hi)

end Manuscript.SupportExponent
