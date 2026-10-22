import Manuscript.FieldExpansion
import Manuscript.UniformEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual field-weighted graphical mass and its finite geometric edge tail. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.UniformGraphMass
open SpinGlass.Expansion Manuscript.FieldExpansion Manuscript.UniformEntropy
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- Squared-field graph mass for any specified finite family of edge subsets. -/
def graphMass (incidence : E → Finset V) (family : Finset (Finset E))
    (h : ℝ) (r : E → ℝ) : ℝ :=
  ∑ Γ ∈ family, Real.tanh h ^ (2 * (boundary incidence Γ).card) * ∏ e ∈ Γ, r e

theorem fieldFactor_nonneg (incidence : E → Finset V) (Γ : Finset E) (h : ℝ) :
    0 ≤ Real.tanh h ^ (2 * (boundary incidence Γ).card) := by
  rw [pow_mul]
  positivity

theorem graphMass_nonneg (incidence : E → Finset V) (family : Finset (Finset E))
    (h : ℝ) (r : E → ℝ) (hr : ∀ e, 0 ≤ r e) : 0 ≤ graphMass incidence family h r := by
  apply Finset.sum_nonneg
  intro Γ hΓ
  exact mul_nonneg (fieldFactor_nonneg incidence Γ h) (Finset.prod_nonneg (fun e he => hr e))

theorem graphMass_mono (incidence : E → Finset V) (family : Finset (Finset E))
    (h : ℝ) (r z : E → ℝ) (hr : ∀ e, 0 ≤ r e) (hrz : ∀ e, r e ≤ z e) :
    graphMass incidence family h r ≤ graphMass incidence family h z := by
  apply Finset.sum_le_sum
  intro Γ hΓ
  apply mul_le_mul_of_nonneg_left _ (fieldFactor_nonneg incidence Γ h)
  exact Finset.prod_le_prod (fun e he => hr e) (fun e he => hrz e)

/-- Edgewise inflation leaves a geometric factor for each discarded edge. -/
theorem finite_geometric_tail (incidence : E → Finset V) (family : Finset (Finset E))
    (h : ℝ) (r z : E → ℝ) {q : ℝ}
    (hr : ∀ e, 0 ≤ r e) (hz : ∀ e, 0 ≤ z e)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hrq : ∀ e, r e ≤ q * z e) (m : ℕ) :
    graphMass incidence (family.filter (fun Γ => m ≤ Γ.card)) h r ≤
      q ^ m * graphMass incidence family h z := by
  unfold graphMass
  calc
    _ ≤ ∑ Γ ∈ family.filter (fun Γ => m ≤ Γ.card),
        q ^ m * (Real.tanh h ^ (2 * (boundary incidence Γ).card) * ∏ e ∈ Γ, z e) := by
      apply Finset.sum_le_sum
      intro Γ hΓ
      have hcard := (Finset.mem_filter.mp hΓ).2
      have hprod : (∏ e ∈ Γ, r e) ≤ q ^ m * ∏ e ∈ Γ, z e := by
        calc
          _ ≤ ∏ e ∈ Γ, (q * z e) :=
            Finset.prod_le_prod (fun e he => hr e) (fun e he => hrq e)
          _ = q ^ Γ.card * ∏ e ∈ Γ, z e := by rw [Finset.prod_mul_distrib]; simp
          _ ≤ q ^ m * ∏ e ∈ Γ, z e := mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one hq hq1 hcard) (Finset.prod_nonneg (fun e he => hz e))
      have hh := mul_le_mul_of_nonneg_left hprod (fieldFactor_nonneg incidence Γ h)
      nlinarith
    _ = q ^ m * ∑ Γ ∈ family.filter (fun Γ => m ≤ Γ.card),
        Real.tanh h ^ (2 * (boundary incidence Γ).card) * ∏ e ∈ Γ, z e := by
      rw [Finset.mul_sum]
    _ ≤ q ^ m * ∑ Γ ∈ family,
        Real.tanh h ^ (2 * (boundary incidence Γ).card) * ∏ e ∈ Γ, z e := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun Γ hΓ hn => mul_nonneg (fieldFactor_nonneg incidence Γ h)
          (Finset.prod_nonneg (fun e he => hz e)))

/-- Real cutoff form, with the manuscript's precise floor refinement. -/
theorem finite_geometric_tail_real (incidence : E → Finset V)
    (family : Finset (Finset E)) (h : ℝ) (r z : E → ℝ) {q t C : ℝ}
    (hr : ∀ e, 0 ≤ r e) (hz : ∀ e, 0 ≤ z e)
    (hq : 0 < q) (hq1 : q ≤ 1) (hrq : ∀ e, r e ≤ q * z e)
    (ht : 0 ≤ t) (hC : graphMass incidence family h z ≤ C) :
    graphMass incidence (family.filter (fun Γ => t < (Γ.card : ℝ))) h r ≤
      C * q ^ (Nat.floor t + 1) ∧ C * q ^ (Nat.floor t + 1) ≤ C * q ^ t := by
  have hC0 : 0 ≤ C := (graphMass_nonneg incidence family h z hz).trans hC
  constructor
  · have heq : ∀ Γ : Finset E, (t < (Γ.card : ℝ)) ↔ Nat.floor t + 1 ≤ Γ.card := by
      intro Γ
      rw [← Nat.floor_lt ht]
      omega
    simp_rw [heq]
    have hh := finite_geometric_tail incidence family h r z hr hz hq.le hq1 hrq (Nat.floor t + 1)
    exact hh.trans (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hC (pow_nonneg hq.le (Nat.floor t + 1)))
  · apply mul_le_mul_of_nonneg_left _ hC0
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hq hq1 (by exact_mod_cast (Nat.lt_floor_add_one t).le)

end Manuscript.UniformGraphMass
