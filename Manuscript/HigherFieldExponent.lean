import Manuscript.SupportExponent
import Manuscript.OriginalLawLowerTail
import SpinGlass.TanhBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The input-dependent effective field exponent in equation (25). -/
noncomputable section
namespace Manuscript.HigherFieldExponent
open Manuscript.SupportExponent

/-- At zero field the finite representative already saturates the best exponent. -/
def alpha (N : ℕ) (rho p h : ℝ) : ℝ :=
  if h = 0 then (p - 1) / (2 * p)
  else Real.log (rho / |Real.tanh h|) / Real.log (N : ℝ)

def selectedKappa (N : ℕ) (rho p h : ℝ) : ℝ := kappa p (alpha N rho p h)

theorem abs_tanh_pos {h : ℝ} (hh : h ≠ 0) : 0 < |Real.tanh h| := by
  apply abs_pos.mpr
  intro hz
  have hc := congrArg Real.artanh hz
  apply hh
  simpa only [Real.artanh_tanh, Real.artanh_zero] using hc

/-- The logarithmic definition gives the exact nonzero-field magnitude. -/
theorem field_identity {N : ℕ} (hN : 1 < N) {rho p h : ℝ}
    (hrho : 0 < rho) (hh : h ≠ 0) :
    rho * (N : ℝ) ^ (-alpha N rho p h) = |Real.tanh h| := by
  have hN' : 1 < (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 < (N : ℝ) := by linarith
  have hl : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hN').ne'
  have ht := abs_tanh_pos hh
  rw [alpha, if_neg hh, Real.rpow_def_of_pos hN0]
  have he : Real.log (N : ℝ) * -(Real.log (rho / |Real.tanh h|) / Real.log (N : ℝ)) =
      -Real.log (rho / |Real.tanh h|) := by field_simp
  rw [he, Real.exp_neg, Real.exp_log (div_pos hrho ht)]
  field_simp

theorem field_le (N : ℕ) (hN : 1 < N) {rho p h : ℝ} (hrho : 0 < rho) : |Real.tanh h| ≤ rho * (N : ℝ) ^ (-alpha N rho p h) := by
  by_cases hh : h = 0
  · subst h
    simpa only [Real.tanh_zero, abs_zero] using
      mul_nonneg hrho.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · exact (field_identity hN hrho hh).ge

/-- The manuscript's weak-field window gives alpha≥1/4. -/
theorem alpha_ge_quarter (N : ℕ) (hN : 4 ≤ N) {rho p h : ℝ}
    (hrho : 1 ≤ rho) (hp : 3 ≤ p)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    (1 : ℝ) / 4 ≤ alpha N rho p h := by
  have hN1 : 1 < N := by omega
  have hN' : 1 < (N : ℝ) := by exact_mod_cast hN1
  have hN0 : 0 < (N : ℝ) := by linarith
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos hN'
  have hrho0 : 0 < rho := by linarith
  by_cases hh : h = 0
  · rw [alpha, if_pos hh]
    apply (le_div_iff₀ (by positivity : 0 < 2 * p)).2
    linarith
  · have ht := abs_tanh_pos hh
    have htbound := (SpinGlass.TanhBound.abs_tanh_le_abs h).trans hfield
    have hlogs := Real.log_le_log ht htbound
    rw [Real.log_mul hrho0.ne' (Real.rpow_pos_of_pos hN0 _).ne', Real.log_rpow hN0] at hlogs
    rw [alpha, if_neg hh, Real.log_div hrho0.ne' ht.ne']
    apply (le_div_iff₀ hl).2
    linarith

theorem selectedKappa_zero (N : ℕ) (rho : ℝ) {p : ℝ} (hp : 0 < p) :
    selectedKappa N rho p 0 = (p - 2) / p := by
  unfold selectedKappa alpha
  simp only [ite_true]
  exact kappa_eq_zero_field p _ hp le_rfl

/-- The literal piecewise exponent in equation (25). -/
theorem selectedKappa_eq (N : ℕ) (rho : ℝ) {p h : ℝ} (hp : 0 < p) :
    selectedKappa N rho p h =
      if h = 0 then (p - 2) / p else
        min ((p - 2) / p)
          (2 * Real.log (rho / |Real.tanh h|) / Real.log (N : ℝ) - 1 / p) := by
  by_cases hh : h = 0
  · subst h
    simp only [ite_true, selectedKappa_zero N rho hp]
  · simp only [selectedKappa, alpha, if_neg hh, kappa]
    congr 2
    ring

theorem selectedKappa_ge_min (N : ℕ) (hN : 4 ≤ N) {rho p h : ℝ}
    (hrho : 1 ≤ rho) (hp : 3 ≤ p)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    kappaMin p ≤ selectedKappa N rho p h :=
  kappa_ge_kappaMin p _ hp (alpha_ge_quarter N hN hrho hp hfield)

end Manuscript.HigherFieldExponent
