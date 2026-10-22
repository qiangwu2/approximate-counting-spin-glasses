import Manuscript.CutoffExecution
import SpinGlass.AlgorithmBudgets

/-!
# Current manuscript Lemma 5.1, stated in the requested MSE budget

Source: the frozen 2026-10-22 `main-12-2-2.tex`, SHA-256
`edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`.

`A` is the manuscript's `C_star`; `CΛ` is `C_Lambda`. The fixed design
constants are exactly `Cutoffs.gamma`, `Cutoffs.nu`, and
`Cutoffs.sizeThreshold`. Their definitions depend on `kapMin`, not on the
actual exponent `kap`, which may vary with the input size and field.

The theorem states the error and weighted-binomial bounds in `u`, with the
same cutoff for every `t >= 1`. It also identifies the returned index of
the counted finite search. No cutoff existence or cost bound is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.CurrentCutoff

open SpinGlass.CutoffTail SpinGlass.AlgorithmBudgets

/-- The current Lemma 5.1, including uniformity in the actual exponent and
the identity of the finite search's return value. The binomial sum over
`range (k+1)` is the manuscript's sum from `j=0` through `j=k`. -/
theorem lemma_5_1 (P : ℕ) {kapMin A c1 CΛ : ℝ}
    (hkapMin : 0 < kapMin) (hA : 1 ≤ A) (hc1 : 0 < c1) (hCΛ : 1 ≤ CΛ) :
    0 < Cutoffs.gamma kapMin A ∧
    Cutoffs.gamma kapMin A < 1 / 4 ∧
    0 < Cutoffs.nu kapMin A c1 ∧
    P ≤ Cutoffs.sizeThreshold P kapMin A ∧
    ∀ (N : ℕ) (kap u : ℝ),
      Cutoffs.sizeThreshold P kapMin A ≤ N →
      kapMin ≤ kap → 0 < u → u < 1 →
      CΛ * Real.exp (-Cutoffs.nu kapMin A c1 * N) < u →
      ∃ k : ℕ,
        k < Nat.floor (Cutoffs.gamma kapMin A * N) ∧
        Real.exp (-phi kap A N (k + 1 : ℕ)) ≤ u / CΛ ∧
        (∀ t : ℝ, 1 ≤ t →
          0 < Cutoffs.workConstant kapMin A t ∧
          (∑ j ∈ Finset.range (k + 1), (N.choose j : ℝ) * t ^ j) ≤
            ((N : ℝ) + 1) * (CΛ / u) ^ (Cutoffs.workConstant kapMin A t)) ∧
        (CutoffExecution.cutoffSearch kapMin kap A N (Real.log (CΛ / u))).found =
          some (k + 1) ∧
        (CutoffExecution.cutoffSearch kapMin kap A N (Real.log (CΛ / u))).operations ≤
          10 * N + 3 := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hC0 : 0 < CΛ := lt_of_lt_of_le zero_lt_one hCΛ
  refine ⟨Cutoffs.gamma_pos hA0, ?_, Cutoffs.nu_pos hkapMin hA0 hc1,
    Cutoffs.sizeThreshold_ge_P P kapMin A, ?_⟩
  · exact (Cutoffs.gamma_le_eighth kapMin A).trans_lt (by norm_num)
  intro N kap u hN hkap hu hu1 hwindow
  let Λ := logBudget CΛ u
  have hΛ : 0 < Λ := logBudget_pos hCΛ hu hu1
  have hsmall : Λ < Cutoffs.nu kapMin A c1 * N := by
    have hlog := Real.log_lt_log
      (mul_pos hC0 (Real.exp_pos (-Cutoffs.nu kapMin A c1 * N))) hwindow
    rw [Real.log_mul hC0.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    dsimp [Λ, logBudget]
    rw [Real.log_div hC0.ne' hu.ne']
    nlinarith
  have hscale : 2 / Cutoffs.gamma kapMin A ≤ (N : ℝ) :=
    (Cutoffs.sizeThreshold_ge_scale P kapMin A).trans (by exact_mod_cast hN)
  have hNpos : 0 < N := by
    have := (Cutoffs.sizeThreshold_ge_four P kapMin A).trans hN
    omega
  obtain ⟨m, hfound, hm1, hmrange, hmPhi, hminimal, hoperations⟩ :=
    CutoffExecution.cutoffSearch_correct hkapMin hkap hA0 hscale hΛ hsmall
  have hmstep : m - 1 + 1 = m := by omega
  have herr := (Cutoffs.selected_error_bounds hsmall.le hmPhi).1
  have hexp : Real.exp (-Λ) = u / CΛ := exp_neg_logBudget hC0 hu
  refine ⟨m - 1, by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [hmstep] using herr.trans_eq hexp
  · intro t ht
    refine ⟨Cutoffs.workConstant_pos hkapMin hA ht, ?_⟩
    have hcost := Cutoffs.selected_binomial_cost hkapMin hkap hA ht
      hNpos hΛ.le hmrange hminimal
    have hpower : Real.exp (Cutoffs.workConstant kapMin A t * Λ) =
        (CΛ / u) ^ (Cutoffs.workConstant kapMin A t) := by
      rw [Real.rpow_def_of_pos (div_pos hC0 hu)]
      dsimp [Λ, logBudget]
      rw [mul_comm]
    simpa only [hmstep, hpower] using hcost
  · simpa only [hmstep, Λ, logBudget] using hfound
  · exact hoperations

end Manuscript.CurrentCutoff
