import Manuscript.SKBranchingMajorant
import SpinGlass.SKBranchingScalar

/-! Explicit scalar estimates for the weak-field SK branching bound. -/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKBranching

def eta (B : ℝ) : ℝ := (1 - B ^ 2) / 2
def degreeConstant (B F : ℝ) : ℝ := F * B ^ 3 / 6 + B ^ 4 / 24
def massConstant (B F : ℝ) : ℝ :=
  eta B ^ (-(1 / 2 : ℝ)) * Real.exp (F ^ 2 * B ^ 2 / (1 - B ^ 2))
def branchConstant (B F : ℝ) : ℝ :=
  32 * Real.exp 1 * degreeConstant B F / eta B ^ 2

theorem eta_pos {B : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) : 0 < eta B := by
  unfold eta
  nlinarith

theorem eta_le_one (B : ℝ) : eta B ≤ 1 := by unfold eta; nlinarith [sq_nonneg B]

theorem degreeConstant_nonneg {B F : ℝ} (hB : 0 ≤ B) (hF : 0 ≤ F) :
    0 ≤ degreeConstant B F := by unfold degreeConstant; positivity

theorem scaled_root_le {N r B : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (hNr : N * r ≤ B ^ 2) : Real.sqrt r * Real.sqrt N ≤ B := by
  have hs : (Real.sqrt r * Real.sqrt N) ^ 2 = N * r := by
    rw [mul_pow, Real.sq_sqrt hr, Real.sq_sqrt hN]
    ring
  have hn : 0 ≤ Real.sqrt r * Real.sqrt N := by positivity
  nlinarith

theorem scaled_cubic_le {N r B φ F : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (hφ : 0 ≤ φ) (hF : 0 ≤ F)
    (hNr : N * r ≤ B ^ 2) (hφN : φ * Real.sqrt N ≤ F) :
    φ * Real.sqrt r ^ 3 * N ^ 2 ≤ F * B ^ 3 := by
  have hz := scaled_root_le hN hr hB hNr
  have hp := mul_le_mul hφN (pow_le_pow_left₀ (by positivity) hz 3)
    (by positivity : 0 ≤ (Real.sqrt r * Real.sqrt N) ^ 3) hF
  have heq : φ * Real.sqrt r ^ 3 * N ^ 2 =
      (φ * Real.sqrt N) * (Real.sqrt r * Real.sqrt N) ^ 3 := by
    calc
      _ = φ * Real.sqrt r ^ 3 * (Real.sqrt N ^ 2) ^ 2 := by rw [Real.sq_sqrt hN]
      _ = _ := by ring
  rwa [heq]

theorem scaled_quartic_le {N r B : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hNr : N * r ≤ B ^ 2) : r ^ 2 * N ^ 2 ≤ B ^ 4 := by
  have hp := pow_le_pow_left₀ (mul_nonneg hN hr) hNr 2
  nlinarith

theorem abs_cube_le_one_add_fourth (x : ℝ) : |x| ^ 3 ≤ 1 + x ^ 4 := by
  have hfour : |x| ^ 4 = x ^ 4 := (by decide : Even 4).pow_abs x
  rw [← hfour]
  by_cases hx : |x| ≤ 1
  · have hp : |x| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    linarith [pow_nonneg (abs_nonneg x) 4]
  · have hp : |x| ^ 3 ≤ |x| ^ 4 := pow_le_pow_right₀ (by linarith) (by omega)
    linarith

/-- The cubic and quartic factors both cost `N⁻²` for each fixed branching vertex. -/
theorem branchFactor_le {N r B φ F : ℝ} (hN : 0 < N) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (hφ : 0 ≤ φ) (hF : 0 ≤ F)
    (hNr : N * r ≤ B ^ 2) (hφN : φ * Real.sqrt N ≤ F) (x : ℝ) :
    φ * (Real.sqrt r * |x|) ^ 3 / 6 + (Real.sqrt r * |x|) ^ 4 / 24 ≤
      degreeConstant B F / N ^ 2 * (1 + x ^ 4) := by
  have hN2 : 0 < N ^ 2 := pow_pos hN _
  have hc : φ * Real.sqrt r ^ 3 / 6 ≤ (F * B ^ 3 / 6) / N ^ 2 := by
    apply (le_div_iff₀ hN2).mpr
    have hp := scaled_cubic_le hN.le hr hB hφ hF hNr hφN
    nlinarith
  have hq : r ^ 2 / 24 ≤ (B ^ 4 / 24) / N ^ 2 := by
    apply (le_div_iff₀ hN2).mpr
    have hp := scaled_quartic_le hN.le hr hNr
    nlinarith
  have hC : 0 ≤ (F * B ^ 3 / 6) / N ^ 2 := by positivity
  have hQ : 0 ≤ (B ^ 4 / 24) / N ^ 2 := by positivity
  have ha := mul_le_mul hc (abs_cube_le_one_add_fourth x)
    (pow_nonneg (abs_nonneg x) 3) hC
  have hb := mul_le_mul hq (show x ^ 4 ≤ 1 + x ^ 4 by linarith)
    (by positivity : 0 ≤ x ^ 4) hQ
  have hr4 : Real.sqrt r ^ 4 = r ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, Real.sq_sqrt hr]
  rw [mul_pow, mul_pow, hr4, (by decide : Even 4).pow_abs x]
  calc
    _ = (φ * Real.sqrt r ^ 3 / 6) * |x| ^ 3 + (r ^ 2 / 24) * x ^ 4 := by ring
    _ ≤ ((F * B ^ 3 / 6) / N ^ 2) * (1 + x ^ 4) +
        ((B ^ 4 / 24) / N ^ 2) * (1 + x ^ 4) := add_le_add ha hb
    _ = _ := by unfold degreeConstant; ring

/-- Completing the square absorbs the linear field term into half of the gap. -/
theorem absorb_linear {B c : ℝ} (hgap : 0 < 1 - B ^ 2) (x : ℝ) :
    c * |x| + B ^ 2 * x ^ 2 / 2 ≤
      c ^ 2 / (1 - B ^ 2) + (1 - eta B) * x ^ 2 / 2 := by
  have hs := sq_nonneg ((1 - B ^ 2) * |x| - 2 * c)
  have habs : |x| ^ 2 = x ^ 2 := sq_abs x
  simp only [sub_sq, mul_pow, habs] at hs
  have hb : c * |x| - (1 - B ^ 2) * x ^ 2 / 4 ≤ c ^ 2 / (1 - B ^ 2) := by
    apply (le_div_iff₀ hgap).mpr
    nlinarith
  unfold eta
  nlinarith

theorem gaussianExponent_le {N r B φ F : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (hB1 : B < 1) (hφ : 0 ≤ φ) (hF : 0 ≤ F)
    (hNr : N * r ≤ B ^ 2) (hφN : φ * Real.sqrt N ≤ F) (x : ℝ) :
    N * φ * (Real.sqrt r * |x|) + N * (Real.sqrt r * |x|) ^ 2 / 2 ≤
      F ^ 2 * B ^ 2 / (1 - B ^ 2) + (1 - eta B) * x ^ 2 / 2 := by
  have hz := scaled_root_le hN hr hB hNr
  have hl := mul_le_mul hφN hz (by positivity : 0 ≤ Real.sqrt r * Real.sqrt N) hF
  have heq : N * φ * Real.sqrt r = (φ * Real.sqrt N) * (Real.sqrt r * Real.sqrt N) := by
    calc
      _ = Real.sqrt N ^ 2 * φ * Real.sqrt r := by rw [Real.sq_sqrt hN]
      _ = _ := by ring
  have hlx := mul_le_mul_of_nonneg_right (heq ▸ hl) (abs_nonneg x)
  have hqx := mul_le_mul_of_nonneg_right hNr (sq_nonneg x)
  have hs := absorb_linear (c := F * B) (by nlinarith : 0 < 1 - B ^ 2) x
  rw [mul_pow, Real.sq_sqrt hr, sq_abs]
  calc
    _ ≤ F * B * |x| + B ^ 2 * x ^ 2 / 2 := by nlinarith only [hlx, hqx]
    _ ≤ _ := by simpa only [mul_pow] using hs

end Manuscript.SKBranching
