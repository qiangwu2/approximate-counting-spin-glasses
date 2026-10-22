import SpinGlass.BoundedSearch

/-!
The explicit common cutoffs (52)--(56), including the finite first-crossing
search and the uniform retained-work estimate of Lemma 5.1.  The exponent
`kap` may depend on the field and on N; every design constant and the work
exponent depend only on the fixed lower bound `kapMin`.
-/

noncomputable section
namespace Manuscript.Cutoffs
open Finset Real SpinGlass.CutoffTail
open scoped BigOperators

def gamma (kapMin A : ℝ) : ℝ :=
  min (1 / 8) (Real.exp (-(1 + 2 / kapMin)) / A)

def cstar (kapMin A : ℝ) : ℝ :=
  SpinGlass.CutoffSelection.hZero kapMin A (gamma kapMin A)

def nu (kapMin A c1 : ℝ) : ℝ :=
  SpinGlass.CutoffSelection.nu kapMin A (gamma kapMin A) c1

def sizeThreshold (P : ℕ) (kapMin A : ℝ) : ℕ :=
  Nat.ceil (max (P : ℝ) (max 4 (2 / gamma kapMin A)))

def cutoffScan (kapMin kap A : ℝ) (N : ℕ) (Lambda : ℝ) :
    SpinGlass.BoundedSearch.Result :=
  SpinGlass.BoundedSearch.cutoffScan kap A (gamma kapMin A) N Lambda

def workConstant (kapMin A t : ℝ) : ℝ :=
  SpinGlass.CutoffSelection.costConstant kapMin A (gamma kapMin A) t

theorem gamma_pos {kapMin A : ℝ} (hA : 0 < A) : 0 < gamma kapMin A := by
  exact lt_min (by norm_num) (div_pos (Real.exp_pos _) hA)

theorem gamma_le_eighth (kapMin A : ℝ) : gamma kapMin A ≤ 1 / 8 := min_le_left _ _

theorem gamma_le_one (kapMin A : ℝ) : gamma kapMin A ≤ 1 :=
  (gamma_le_eighth kapMin A).trans (by norm_num)

theorem gamma_gap {kapMin A : ℝ} (hk : 0 < kapMin) (hA : 0 < A) :
    2 ≤ kapMin * (Real.log (1 / (A * gamma kapMin A)) - 1) := by
  have hg := gamma_pos (kapMin := kapMin) hA
  have hc : gamma kapMin A ≤ Real.exp (-(1 + 2 / kapMin)) / A := min_le_right _ _
  have hm : A * gamma kapMin A ≤ Real.exp (-(1 + 2 / kapMin)) := by
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hc
  have hl := Real.log_le_log (mul_pos hA hg) hm
  rw [Real.log_exp] at hl
  rw [one_div, Real.log_inv]
  have htwo : kapMin * (2 / kapMin) = 2 := by field_simp
  have := mul_le_mul_of_nonneg_left hl hk.le
  nlinarith

theorem gamma_gap_variable {kapMin kap A : ℝ} (hk : 0 < kapMin)
    (hkk : kapMin ≤ kap) (hA : 0 < A) :
    2 ≤ kap * (Real.log (1 / (A * gamma kapMin A)) - 1) := by
  have h := gamma_gap hk hA
  have hp : 0 ≤ Real.log (1 / (A * gamma kapMin A)) - 1 := by
    by_contra hn
    have := mul_neg_of_pos_of_neg hk (lt_of_not_ge hn)
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right hkk hp)

theorem cstar_pos {kapMin A : ℝ} (hk : 0 < kapMin) (hA : 0 < A) :
    0 < cstar kapMin A :=
  SpinGlass.CutoffSelection.hZero_pos hk hA (gamma_pos hA) (gamma_gap hk hA)

theorem nu_pos {kapMin A c1 : ℝ} (hk : 0 < kapMin) (hA : 0 < A)
    (hc : 0 < c1) : 0 < nu kapMin A c1 :=
  SpinGlass.CutoffSelection.nu_pos hk hA (gamma_pos hA) hc (gamma_gap hk hA)

theorem four_nu_le_c1 (kapMin A c1 : ℝ) : 4 * nu kapMin A c1 ≤ c1 :=
  SpinGlass.CutoffSelection.four_nu_le_omega _ _ _ _

theorem four_nu_le_cstar (kapMin A c1 : ℝ) :
    4 * nu kapMin A c1 ≤ cstar kapMin A :=
  SpinGlass.CutoffSelection.four_nu_le_hZero _ _ _ _

theorem sizeThreshold_ge_P (P : ℕ) (kapMin A : ℝ) :
    P ≤ sizeThreshold P kapMin A := by
  have h : (P : ℝ) ≤ sizeThreshold P kapMin A :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem sizeThreshold_ge_four (P : ℕ) (kapMin A : ℝ) :
    4 ≤ sizeThreshold P kapMin A := by
  have h : (4 : ℝ) ≤ sizeThreshold P kapMin A :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (Nat.le_ceil _)
  exact_mod_cast h

theorem sizeThreshold_ge_scale (P : ℕ) (kapMin A : ℝ) :
    2 / gamma kapMin A ≤ (sizeThreshold P kapMin A : ℝ) :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (Nat.le_ceil _)

/-- The fixed design threshold remains valid when the actual exponent is larger. -/
theorem nu_le_variable {kapMin kap A c1 : ℝ} (hk : 0 < kapMin)
    (hkk : kapMin ≤ kap) (hA : 0 < A) :
    nu kapMin A c1 ≤
      SpinGlass.CutoffSelection.nu kap A (gamma kapMin A) c1 := by
  have hlog : 0 < Real.log (2 / (A * gamma kapMin A)) := by
    have h0 := cstar_pos hk hA
    unfold cstar SpinGlass.CutoffSelection.hZero at h0
    exact (mul_pos_iff.mp h0).resolve_right (by
      intro hn
      have hg := gamma_pos (kapMin := kapMin) hA
      have hp : 0 ≤ kapMin * gamma kapMin A / 2 := by positivity
      exact (not_lt_of_ge hp) hn.1) |>.2
  have hg := (gamma_pos (kapMin := kapMin) hA).le
  unfold nu SpinGlass.CutoffSelection.nu SpinGlass.CutoffSelection.hZero
  gcongr

/-- Actual finite scan: it returns the first crossing, rather than a postulated
cutoff or a non-effective existence witness. -/
theorem cutoffScan_correct {kapMin kap A c1 Lambda : ℝ} {N : ℕ}
    (hk : 0 < kapMin) (hkk : kapMin ≤ kap) (hA : 0 < A)
    (hN : 2 / gamma kapMin A ≤ (N : ℝ)) (hLam : 0 < Lambda)
    (hsmall : Lambda < nu kapMin A c1 * N) :
    ∃ m, (cutoffScan kapMin kap A N Lambda).found = some m ∧
      1 ≤ m ∧ m ≤ Nat.floor (gamma kapMin A * N) ∧ Lambda ≤ phi kap A N m ∧
      ∀ j : ℕ, 1 ≤ j → j < m → phi kap A N j < Lambda := by
  apply SpinGlass.BoundedSearch.cutoffScan_correct (hk.trans_le hkk) hA
    (gamma_pos hA) (gamma_gap_variable hk hkk hA) hN hLam
  exact hsmall.trans_le (mul_le_mul_of_nonneg_right (nu_le_variable hk hkk hA)
    (Nat.cast_nonneg N))

theorem cutoffScan_evaluations {kapMin kap A Lambda : ℝ} {N : ℕ}
    (hA : 0 < A) : (cutoffScan kapMin kap A N Lambda).evaluations ≤ N :=
  SpinGlass.BoundedSearch.cutoffScan_evaluations (gamma_pos hA).le (gamma_le_one _ _)

/-- Each exponent test uses a fixed number of arithmetic, logarithm, and
comparison operations. This bound includes the scan and its loop bookkeeping. -/
def searchOperations (kapMin kap A : ℝ) (N : ℕ) (Lambda : ℝ) : ℕ :=
  12 * (cutoffScan kapMin kap A N Lambda).evaluations + 2

theorem searchOperations_le {kapMin kap A Lambda : ℝ} {N : ℕ} (hA : 0 < A) :
    searchOperations kapMin kap A N Lambda ≤ 12 * N + 2 := by
  unfold searchOperations
  have := cutoffScan_evaluations (kapMin := kapMin) (kap := kap)
    (Lambda := Lambda) (N := N) hA
  omega

theorem selected_error_bounds {kapMin kap A c1 Lambda : ℝ} {N m : ℕ}
    (hsmall : Lambda ≤ nu kapMin A c1 * N) (hm : Lambda ≤ phi kap A N m) :
    Real.exp (-phi kap A N m) ≤ Real.exp (-Lambda) ∧
      Real.exp (-c1 * N) ≤ Real.exp (-4 * Lambda) := by
  constructor
  · exact Real.exp_le_exp.mpr (neg_le_neg hm)
  · have h := mul_le_mul_of_nonneg_right (four_nu_le_c1 kapMin A c1)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem phi_min_le {kapMin kap A : ℝ} {N j : ℕ}
    (hk : 0 < kapMin) (hkk : kapMin ≤ kap) (hA : 0 < A)
    (hj : 1 ≤ j) (hjrange : (j : ℝ) ≤ gamma kapMin A * N) :
    phi kapMin A N j ≤ phi kap A N j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hrat : 1 / (A * gamma kapMin A) ≤ (N : ℝ) / (A * j) := by
    apply (div_le_div_iff₀ (mul_pos hA (gamma_pos hA)) (mul_pos hA hj0)).2
    nlinarith [mul_le_mul_of_nonneg_left hjrange hA.le]
  have hg := gamma_pos (kapMin := kapMin) hA
  have hl := (SpinGlass.CutoffSelection.log_gap_pos hk (gamma_gap hk hA)).le.trans
    (Real.log_le_log (by positivity) hrat)
  unfold phi
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hkk hj0.le) hl

theorem workConstant_pos {kapMin A t : ℝ} (hk : 0 < kapMin)
    (hA : 1 ≤ A) (ht : 1 ≤ t) : 0 < workConstant kapMin A t :=
  SpinGlass.CutoffSelection.costConstant_pos hk hA ht
    (gamma_gap hk (by linarith))

/-- Lemma 5.1's retained-work estimate, with a constant independent of the
possibly N-dependent and field-dependent exponent `kap`. -/
theorem selected_binomial_cost {kapMin kap A t Lambda : ℝ} {N m : ℕ}
    (hk : 0 < kapMin) (hkk : kapMin ≤ kap) (hA : 1 ≤ A) (ht : 1 ≤ t)
    (hN : 0 < N) (hLam : 0 ≤ Lambda) (hm : m ≤ Nat.floor (gamma kapMin A * N))
    (hminimal : ∀ j : ℕ, 1 ≤ j → j < m → phi kap A N j < Lambda) :
    (∑ j ∈ Finset.range m, (N.choose j : ℝ) * t ^ j) ≤
      (N + 1) * Real.exp (workConstant kapMin A t * Lambda) := by
  have hA0 : 0 < A := by linarith
  apply SpinGlass.CutoffSelection.selected_binomial_cost hk hA
    (gamma_pos hA0) (gamma_le_one _ _) ht (gamma_gap hk hA0) hN hLam hm
  intro j hj hjm
  have hg := gamma_pos (kapMin := kapMin) hA0
  have hjrange : (j : ℝ) ≤ gamma kapMin A * N :=
    (by exact_mod_cast (le_trans (Nat.le_of_lt hjm) hm) :
      (j : ℝ) ≤ Nat.floor (gamma kapMin A * N)).trans
        (Nat.floor_le (by positivity))
  exact (phi_min_le hk hkk hA0 hj hjrange).trans_lt (hminimal j hj hjm)

end Manuscript.Cutoffs
