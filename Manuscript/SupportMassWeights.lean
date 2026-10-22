import Manuscript.SupportMassCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Pointwise decay extraction for actual mixed hypergraphs in a weak field. -/
noncomputable section
open scoped BigOperators

namespace Manuscript.SupportMassWeights
open Manuscript.FieldExpansion Manuscript.SupportEvaluation Manuscript.SupportDegrees

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The actual graph's degree and odd boundary imply the complete extracted exponent. -/
theorem extracted_exponent_le (incidence : E → Finset V) (Γ : Finset E)
    (pmin alpha : ℝ) (hpmin : 1 ≤ pmin) (ha : 0 ≤ alpha)
    (hp : ∀ e ∈ Γ, pmin ≤ ((incidence e).card : ℝ)) :
    (SupportExponent.kappa pmin alpha + 1) * ((support incidence Γ).card : ℝ) ≤
      2 * alpha * ((boundary incidence Γ).card : ℝ) +
        ∑ e ∈ Γ, (((incidence e).card : ℝ) - 1) := by
  have hd := actual_degreeExponent_ge_kappa incidence Γ pmin alpha hpmin
  have hb := real_boundary_card_ge_deficit incidence Γ
  have hsum := SupportExponent.total_edge_normalization_bound Γ
    (fun e => ((incidence e).card : ℝ)) (fun _ => (1 : ℝ)) pmin
    (by linarith) hp (fun _ _ => zero_le_one)
  simp only [mul_one] at hsum
  have hcast : (totalDegree incidence Γ : ℝ) = ∑ e ∈ Γ, ((incidence e).card : ℝ) := by
    simp [totalDegree]
  rw [← hcast] at hsum
  unfold SupportExponent.degreeExponent at hd
  have hfield := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * alpha by positivity)
  nlinarith

/-- The homogeneous field contributes a power of the support ratio, with one
fixed `rho^(2v)` factor for all graphs on `v` used vertices. -/
theorem field_factor_le (incidence : E → Finset V) (Γ : Finset E)
    (h rho t alpha : ℝ) (hrho : 1 ≤ rho) (ht : 0 < t)
    (hfield : |Real.tanh h| ≤ rho * t ^ alpha) :
    Real.tanh h ^ (2 * (boundary incidence Γ).card) ≤
      rho ^ (2 * (support incidence Γ).card) *
        t ^ (2 * alpha * ((boundary incidence Γ).card : ℝ)) := by
  have hb := Finset.card_le_card (boundary_subset_support incidence Γ)
  have hpow := pow_le_pow_left₀ (abs_nonneg (Real.tanh h)) hfield
    (2 * (boundary incidence Γ).card)
  have habs : |Real.tanh h| ^ (2 * (boundary incidence Γ).card) =
      Real.tanh h ^ (2 * (boundary incidence Γ).card) := by
    rw [pow_mul, pow_mul, sq_abs]
  rw [habs, mul_pow] at hpow
  have hreal : (t ^ alpha) ^ (2 * (boundary incidence Γ).card) =
      t ^ (2 * alpha * ((boundary incidence Γ).card : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    push_cast
    ring
  rw [hreal] at hpow
  apply hpow.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
  exact pow_le_pow_right₀ hrho (Nat.mul_le_mul_left 2 hb)

/-- Extract all support-ratio decay before summing the residual generating product. -/
theorem graph_weight_le (incidence : E → Finset V) (Γ : Finset E)
    (h rho t pmin alpha : ℝ) (hrho : 1 ≤ rho) (ht : 0 < t) (ht1 : t ≤ 1)
    (hpmin : 1 ≤ pmin) (ha : 0 ≤ alpha)
    (hp : ∀ e ∈ Γ, pmin ≤ ((incidence e).card : ℝ))
    (hfield : |Real.tanh h| ≤ rho * t ^ alpha)
    (r q : E → ℝ) (hr : ∀ e ∈ Γ, 0 ≤ r e) (hq : ∀ e ∈ Γ, 0 ≤ q e)
    (hrq : ∀ e ∈ Γ, r e ≤ q e * t ^ (((incidence e).card : ℝ) - 1)) :
    Real.tanh h ^ (2 * (boundary incidence Γ).card) * ∏ e ∈ Γ, r e ≤
      (rho ^ (2 * (support incidence Γ).card) *
        t ^ ((SupportExponent.kappa pmin alpha + 1) * ((support incidence Γ).card : ℝ))) *
          ∏ e ∈ Γ, q e := by
  have hprod : (∏ e ∈ Γ, r e) ≤ (∏ e ∈ Γ, q e) *
      t ^ (∑ e ∈ Γ, (((incidence e).card : ℝ) - 1)) := by
    calc
      _ ≤ ∏ e ∈ Γ, q e * t ^ (((incidence e).card : ℝ) - 1) :=
        Finset.prod_le_prod hr hrq
      _ = _ := by rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos ht]
  have hfieldbound := field_factor_le incidence Γ h rho t alpha hrho ht hfield
  have hfactor0 : 0 ≤ Real.tanh h ^ (2 * (boundary incidence Γ).card) := by
    rw [pow_mul]
    positivity
  have hQ0 : 0 ≤ ∏ e ∈ Γ, q e := Finset.prod_nonneg hq
  have hRh0 : 0 ≤ rho ^ (2 * (support incidence Γ).card) := by positivity
  have hexp := Real.rpow_le_rpow_of_exponent_ge ht ht1
    (extracted_exponent_le incidence Γ pmin alpha hpmin ha hp)
  calc
    _ ≤ (rho ^ (2 * (support incidence Γ).card) *
      t ^ (2 * alpha * ((boundary incidence Γ).card : ℝ))) *
        ((∏ e ∈ Γ, q e) * t ^ (∑ e ∈ Γ, (((incidence e).card : ℝ) - 1))) :=
          mul_le_mul hfieldbound hprod (Finset.prod_nonneg hr) (by positivity)
    _ = (rho ^ (2 * (support incidence Γ).card) *
      t ^ (2 * alpha * ((boundary incidence Γ).card : ℝ) +
        ∑ e ∈ Γ, (((incidence e).card : ℝ) - 1))) * ∏ e ∈ Γ, q e := by
          rw [Real.rpow_add ht]
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp hRh0) hQ0

/-- The manuscript's weak-field hypothesis implies the local support-ratio version. -/
theorem weak_field_to_ratio {N v : ℕ} (hN : 0 < N) (hv : 0 < v)
    (h rho alpha : ℝ) (hrho : 0 ≤ rho) (ha : 0 ≤ alpha)
    (hfield : |Real.tanh h| ≤ rho * (N : ℝ) ^ (-alpha)) :
    |Real.tanh h| ≤ rho * ((v : ℝ) / N) ^ alpha := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  apply hfield.trans
  apply mul_le_mul_of_nonneg_left _ hrho
  rw [Real.rpow_neg hNR.le, Real.div_rpow (by positivity) hNR.le]
  have hpow := Real.one_le_rpow hvR ha
  simpa only [one_div] using
    (div_le_div_of_nonneg_right hpow (Real.rpow_nonneg hNR.le alpha))

/-- The interaction normalization separates into a local fugacity and a ratio power. -/
theorem edge_scale_identity {N v p : ℕ} (hN : 0 < N) (hv : 0 < v) (hp : 0 < p)
    (c : ℝ) :
    c / (N : ℝ) ^ (p - 1) =
      (c / (v : ℝ) ^ (p - 1)) * ((v : ℝ) / N) ^ ((p : ℝ) - 1) := by
  have hcast : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp]
    norm_num
  rw [hcast, Real.rpow_natCast, div_pow]
  have hvpow : (v : ℝ)^(p-1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hv)
  field_simp

end Manuscript.SupportMassWeights
