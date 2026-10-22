import Manuscript.SKRestrictedKernels
import SpinGlass.ColorMemoExecution

/-! A fixed instruction program for one cached colorful-path recurrence cell.
All predecessor values and edge weights are read from addressed RAM. -/
noncomputable section
namespace Manuscript.SKRestrictedMemoCell
open RestrictedMachine SKRestrictedKernels
open scoped BigOperators

theorem dot_finite (params : Parameters) (input : Inputs) (s : State) (N : ℕ)
    (f g : Fin N → ℝ) (hlen : s.natReg 4 = N) (hzero : s.realReg 0 = 0)
    (hf : ∀ i : Fin N, s.realMem (s.natReg 0+i.val*s.natReg 2) = f i)
    (hg : ∀ i : Fin N, s.realMem (s.natReg 1+i.val*s.natReg 3) = g i) :
    ∃ t, Exec params input dotProgram s (27*N+5) t ∧
      DotInvariant s N t ∧ t.realReg 0 = ∑ i, f i*g i := by
  obtain ⟨t, he, hi⟩ := dot_realized params input s
  rw [hlen] at he hi
  refine ⟨t, he, hi, ?_⟩
  rw [hi.2.2.2.2.2.2, hzero, zero_add, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hf, hg]

/-- The natural metadata registers are singleton flag7, membership flag9,
destination8, start-value address10. The dot-product layout occupies0..4. -/
def program : Program :=
  .branch 7 (code [.loadReal 0 10, .storeReal 8 0])
    (.branch 9
      (.seq (code [.rconst 0 0]) (.seq dotProgram (code [.storeReal 8 0])))
      (code [.rconst 0 0, .storeReal 8 0]))

/-- The actual singleton/invalid/recurrence control agrees with the saved-table
update, including writing the result into its requested cache coordinate. -/
theorem cell_realized {N K : ℕ} (params : Parameters) (input : Inputs) (s : State)
    (χ : Fin N → Fin K) (start : Fin N → ℝ) (w : Fin N → Fin N → ℝ)
    (old : Finset (Fin K) → Fin N → ℝ) (S : Finset (Fin K)) (j : Fin N)
    (hlen : s.natReg 4 = N)
    (hsingle : s.natReg 7 = if S = {χ j} then 1 else 0)
    (hmember : s.natReg 9 = if χ j ∈ S then 1 else 0)
    (hstart : s.realMem (s.natReg 10) = start j)
    (hprev : χ j ∈ S → ∀ i : Fin N,
      s.realMem (s.natReg 0+i.val*s.natReg 2) = old (S.erase (χ j)) i)
    (hweight : ∀ i : Fin N,
      s.realMem (s.natReg 1+i.val*s.natReg 3) = w i j) :
    ∃ count t, Exec params input program s count t ∧ count ≤ 27*N+15 ∧
      t.realMem = Function.update s.realMem (s.natReg 8)
        (SpinGlass.ColorMemoExecution.update χ start w old S j) ∧
      t.natMem = s.natMem ∧
      (∀ r, 4 ≤ r → t.realReg r = s.realReg r) := by
  by_cases hs : S = {χ j}
  · have hflag : s.natReg 7 ≠ 0 := by simp [hs] at hsingle; omega
    let t := runCode params input [.loadReal 0 10, .storeReal 8 0] s
    refine ⟨9, t, ?_, by omega, ?_, ?_, ?_⟩
    · have he := Exec.branchNonzero (no := .branch 9
          (.seq (code [.rconst 0 0]) (.seq dotProgram (code [.storeReal 8 0])))
          (code [.rconst 0 0, .storeReal 8 0])) hflag
          (exec_code params input [.loadReal 0 10, .storeReal 8 0] s)
      simpa [program, codeCost, instrCost] using he
    · simp [t, runCode, step, writeRealMem, SpinGlass.ColorMemoExecution.update, hs, hstart]
    · simp [t, runCode, step, writeRealMem]
    · intro r hr
      have hr0 : r ≠ 0 := by omega
      simp [t, runCode, step, writeRealMem, hr0]
  · have hflag : s.natReg 7 = 0 := by simpa [hs] using hsingle
    by_cases hj : χ j ∈ S
    · have hjflag : s.natReg 9 ≠ 0 := by simp [hj] at hmember; omega
      let s0 := runCode params input [.rconst 0 0] s
      have hs0 : s0 = writeRealReg s 0 0 := by simp [s0, runCode, step]
      obtain ⟨t, he, hi, hv⟩ := dot_finite params input s0 N
        (old (S.erase (χ j))) (fun i => w i j)
        (by simpa [hs0] using hlen) (by simp [hs0])
        (by simpa [hs0] using hprev hj) (by simpa [hs0] using hweight)
      let out := runCode params input [.storeReal 8 0] t
      have haddr : t.natReg 8 = s.natReg 8 := by
        simpa [hs0] using hi.2.2.2.2.1 8 (by decide) (by decide)
      have hmem : t.realMem = s.realMem := by simpa [hs0] using hi.1
      have hnatmem : t.natMem = s.natMem := by simpa [hs0] using hi.2.1
      refine ⟨27*N+15, out, ?_, le_rfl, ?_, ?_, ?_⟩
      · have hinit : Exec params input (code [.rconst 0 0]) s 1 s0 := by
          simpa [s0, codeCost, instrCost] using exec_code params input [.rconst 0 0] s
        have hstore : Exec params input (code [.storeReal 8 0]) t 3 out := by
          simpa [out, codeCost, instrCost] using exec_code params input [.storeReal 8 0] t
        have hr := Exec.branchZero (yes := code [.loadReal 0 10, .storeReal 8 0]) hflag
          (Exec.branchNonzero (no := code [.rconst 0 0, .storeReal 8 0]) hjflag
            (Exec.seq hinit (Exec.seq he hstore)))
        convert hr using 1 <;> first | rfl | omega
      · simp [out, runCode, step, writeRealMem, haddr, hmem, hv,
          SpinGlass.ColorMemoExecution.update, hs, hj]
      · simpa [out, runCode, step, writeRealMem] using hnatmem
      · intro r hr
        have hr0 : r ≠ 0 := by omega
        simpa [out, runCode, step, writeRealMem, hs0, hr0] using hi.2.2.2.2.2.1 r hr
    · have hjflag : s.natReg 9 = 0 := by simpa [hj] using hmember
      let t := runCode params input [.rconst 0 0, .storeReal 8 0] s
      refine ⟨10, t, ?_, by omega, ?_, ?_, ?_⟩
      · have hr := Exec.branchZero (yes := code [.loadReal 0 10, .storeReal 8 0]) hflag
          (Exec.branchZero (yes := .seq (code [.rconst 0 0])
            (.seq dotProgram (code [.storeReal 8 0]))) hjflag
            (exec_code params input [.rconst 0 0, .storeReal 8 0] s))
        simpa [program, codeCost, instrCost] using hr
      · simp [t, runCode, step, writeRealMem, SpinGlass.ColorMemoExecution.update, hs, hj]
      · simp [t, runCode, step, writeRealMem]
      · intro r hr
        have hr0 : r ≠ 0 := by omega
        simp [t, runCode, step, writeRealMem, hr0]

end Manuscript.SKRestrictedMemoCell
