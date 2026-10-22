import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The non-strict moment threshold in Remark 1.2(ii)

These are scalar exponent identities and inequalities. They certify that equality
in the stated moment threshold is sufficient for the exponent comparison.
They do not replace the separate truncated-moment little-o or probability proofs.
-/

noncomputable section

namespace Manuscript.MomentExponents

/-- The power of `N` contributed by interactions of order `p` to the tail bound. -/
def tailExponent (p m : ℝ) : ℝ := p - m * (p - 1) / 2

/-- The manuscript's threshold for a target decay `N^(-b)`. -/
def momentThreshold (pmin b : ℝ) : ℝ := 2 * (pmin + b) / (pmin - 1)

theorem momentThreshold_gt_two {pmin b : ℝ} (hpmin : 2 ≤ pmin)
    (hb : 0 ≤ b) : 2 < momentThreshold pmin b := by
  unfold momentThreshold
  apply (lt_div_iff₀ (by linarith : 0 < pmin - 1)).2
  linarith

/-- At the minimum order, the threshold gives exactly the requested exponent. -/
theorem tailExponent_at_threshold {pmin b : ℝ} (hpmin : 1 < pmin) :
    tailExponent pmin (momentThreshold pmin b) = -b := by
  unfold tailExponent momentThreshold
  have hne : pmin - 1 ≠ 0 := by linarith
  field_simp
  linarith

/-- Increasing the interaction order can only improve the exponent if `m ≥ 2`. -/
theorem tailExponent_antitone_order {pmin p m : ℝ} (hp : pmin ≤ p)
    (hm : 2 ≤ m) : tailExponent p m ≤ tailExponent pmin m := by
  unfold tailExponent
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hp)]

/-- The weak inequality in the manuscript's moment assumption suffices. -/
theorem tailExponent_le_neg {pmin p m b : ℝ} (hpmin : 2 ≤ pmin)
    (hp : pmin ≤ p) (hb : 0 ≤ b) (hm : momentThreshold pmin b ≤ m) :
    tailExponent p m ≤ -b := by
  have hm2 : 2 < m := lt_of_lt_of_le (momentThreshold_gt_two hpmin hb) hm
  have hbase := (div_le_iff₀ (by linarith : 0 < pmin - 1)).1 hm
  have hmono := tailExponent_antitone_order hp (le_of_lt hm2)
  unfold tailExponent at *
  nlinarith

/-- A strict moment hypothesis gives a strict exponent at every active order. -/
theorem tailExponent_lt_neg {pmin p m b : ℝ} (hpmin : 2 ≤ pmin)
    (hp : pmin ≤ p) (hb : 0 ≤ b) (hm : momentThreshold pmin b < m) :
    tailExponent p m < -b := by
  have hm2 : 2 < m := lt_trans (momentThreshold_gt_two hpmin hb) hm
  have hbase := (div_lt_iff₀ (by linarith : 0 < pmin - 1)).1 hm
  have hmono := tailExponent_antitone_order hp (le_of_lt hm2)
  unfold tailExponent at *
  nlinarith

/-- At threshold equality, orders above the minimum still have strict decay. -/
theorem tailExponent_lt_neg_of_order_gt {pmin p m b : ℝ} (hpmin : 2 ≤ pmin)
    (hp : pmin < p) (hb : 0 ≤ b) (hm : momentThreshold pmin b ≤ m) :
    tailExponent p m < -b := by
  have hm2 : 2 < m := lt_of_lt_of_le (momentThreshold_gt_two hpmin hb) hm
  have hbase := (div_le_iff₀ (by linarith : 0 < pmin - 1)).1 hm
  unfold tailExponent
  nlinarith [mul_pos (sub_pos.mpr hm2) (sub_pos.mpr hp)]

/-- The natural-number interaction-order form used by the finite mixture model. -/
theorem natural_order_tailExponent_le_neg {pmin p : ℕ} {m b : ℝ}
    (hpmin : 2 ≤ pmin) (hp : pmin ≤ p) (hb : 0 ≤ b)
    (hm : momentThreshold (pmin : ℝ) b ≤ m) :
    tailExponent (p : ℝ) m ≤ -b := by
  apply tailExponent_le_neg (pmin := (pmin : ℝ))
  · exact_mod_cast hpmin
  · exact_mod_cast hp
  · exact hb
  · exact hm

end Manuscript.MomentExponents
