import Manuscript.MixedThreshold
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Explicit parameters associated with the exact mixed variational threshold. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.MixedThreshold

theorem delta_nonneg (P : Finset ℕ) (a : ℕ → ℝ) : 0 ≤ delta P a := by
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- The collision normalization equals the manuscript's factorial formula. -/
theorem choose_two_div_factorial {p : ℕ} (hp : 2 ≤ p) :
    (p.choose 2 : ℝ) / (p.factorial : ℝ) = 1 / (2 * ((p-2).factorial : ℝ)) := by
  have hnat := Nat.choose_mul_factorial_mul_factorial hp
  have hf : (p.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  have hf2 : ((p-2).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have heq : (p.choose 2 : ℝ) * 2 * ((p-2).factorial : ℝ) = (p.factorial : ℝ) := by
    exact_mod_cast hnat
  field_simp
  nlinarith

theorem delta_eq_factorial (P : Finset ℕ) (a : ℕ → ℝ) (hp : ∀ p ∈ P, 2 ≤ p) :
    delta P a = ∑ p ∈ P, a p ^ 2 / (2 * ((p-2).factorial : ℝ)) := by
  apply Finset.sum_congr rfl
  intro p hpP
  rw [choose_two_div_factorial (hp p hpP)]
  ring

/-- The threshold itself is the nonnegative square root of the exact infimum. -/
def betaF (P : Finset ℕ) (a : ℕ → ℝ) : ℝ := Real.sqrt (thresholdSquared P a)

/-- The paper's fixed inflated inverse temperature. -/
def betaPlus (P : Finset ℕ) (a : ℕ → ℝ) (B : ℝ) : ℝ := (B + betaF P a) / 2

def theta (P : Finset ℕ) (a : ℕ → ℝ) (B : ℝ) : ℝ := B / betaPlus P a B

theorem betaF_pos (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) : 0 < betaF P a :=
  Real.sqrt_pos.2 (thresholdSquared_pos P a hP ha hp)

theorem betaF_sq (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) :
    betaF P a ^ 2 = thresholdSquared P a :=
  Real.sq_sqrt (thresholdSquared_pos P a hP ha hp).le

theorem betaPlus_range (P : Finset ℕ) (a : ℕ → ℝ) {B : ℝ}
    (hB : 0 < B) (hBT : B < betaF P a) :
    0 < B ∧ B < betaPlus P a B ∧ betaPlus P a B < betaF P a := by
  dsimp [betaPlus]
  constructor
  · exact hB
  constructor <;> linarith

theorem betaPlus_sq_range (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) {B : ℝ}
    (hB : 0 < B) (hBT : B < betaF P a) :
    0 < betaPlus P a B ^ 2 ∧ betaPlus P a B ^ 2 < thresholdSquared P a := by
  obtain ⟨_, h1, h2⟩ := betaPlus_range P a hB hBT
  have hs := betaF_sq P a hP ha hp
  constructor
  · exact sq_pos_of_pos (hB.trans h1)
  · nlinarith

theorem theta_range (P : Finset ℕ) (a : ℕ → ℝ) {B : ℝ}
    (hB : 0 < B) (hBT : B < betaF P a) : 0 < theta P a B ∧ theta P a B < 1 := by
  obtain ⟨_, h1, h2⟩ := betaPlus_range P a hB hBT
  exact ⟨div_pos hB (hB.trans h1), (div_lt_one (hB.trans h1)).2 h1⟩

/-- The SK interaction polynomial has exactly the stated normalization. -/
theorem xi_sk (a : ℕ → ℝ) (ha : a 2 = 1) (x : ℝ) :
    xi {2} a x = x ^ 2 / 2 := by simp [xi, ha]

/-- The SK variational squared threshold equals one, rather than merely being
bounded below by one. -/
theorem thresholdSquared_sk (a : ℕ → ℝ) (ha : a 2 = 1) :
    thresholdSquared {2} a = 1 := by
  have hP : ({2} : Finset ℕ).Nonempty := by simp
  have ha' : ∀ p ∈ ({2} : Finset ℕ), 0 < a p := by simpa [ha]
  have hp : ∀ p ∈ ({2} : Finset ℕ), 2 ≤ p := by simp
  have hlo := half_inv_xi_one_le_thresholdSquared {2} a hP ha' hp
  rw [xi_sk a ha] at hlo
  norm_num at hlo
  apply le_antisymm _ hlo
  by_contra! hgt
  let x := min ((thresholdSquared {2} a - 1) / 2) (1 / 2)
  have hx : 0 < x := lt_min (by linarith) (by norm_num)
  have hx1 : x < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hxT : 1 + x < thresholdSquared {2} a := by
    have hm : x ≤ (thresholdSquared {2} a - 1) / 2 := min_le_left _ _
    linarith
  have ht := thresholdSquared_le {2} a hx hx1.le
  rw [xi_sk a ha] at ht
  have hbound := entropy_le_half_sq_mul_one_add hx.le hx1
  have ht' := (le_div_iff₀ (by positivity : 0 < x ^ 2 / 2)).mp ht
  have hprod : 0 < x ^ 2 := sq_pos_of_pos hx
  nlinarith

theorem betaF_sk (a : ℕ → ℝ) (ha : a 2 = 1) : betaF {2} a = 1 := by
  unfold betaF
  rw [thresholdSquared_sk a ha, Real.sqrt_one]

end Manuscript.MixedThreshold
