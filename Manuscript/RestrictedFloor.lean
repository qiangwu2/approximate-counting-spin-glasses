import Manuscript.RestrictedMachine
import Manuscript.CutoffExecution

/-! The bounded floor used by cutoff selection is a descending comparison loop. -/
noncomputable section
namespace Manuscript.RestrictedFloor
open RestrictedMachine

/-- Real register 0 holds the target, natural register 0 the descending
candidate. Registers 1 and 4 hold one and zero. Register 2 is the loop flag. -/
def testCode : List Instruction :=
  [ .natToReal 1 0, .rle 2 1 0, .nsub 2 1 2,
    .nle 3 0 4, .nsub 3 1 3, .nmul 2 2 3 ]
def bodyCode : List Instruction := [.nsub 0 0 1] ++ testCode
def loop : Program := .while 2 (code bodyCode)
def program : Program :=
  .seq (code ([.nconst 1 1, .nconst 4 0] ++ testCode)) loop

theorem test_cost : codeCost testCode = 23 := rfl
theorem body_cost : codeCost bodyCode = 27 := rfl

theorem test_values (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 1 = 1) (hzero : s.natReg 4 = 0) :
    let t := runCode params input testCode s
    t.realReg 0 = s.realReg 0 ∧ t.natReg 0 = s.natReg 0 ∧
      t.natReg 1 = 1 ∧ t.natReg 4 = 0 ∧
      t.natReg 2 = if 0 < s.natReg 0 ∧ ¬(s.natReg 0 : ℝ) ≤ s.realReg 0 then 1 else 0 := by
  by_cases hn : s.natReg 0 = 0 <;>
    by_cases hr : (s.natReg 0 : ℝ) ≤ s.realReg 0 <;>
    simp [testCode, runCode, step, hone, hzero, hn, hr, Nat.pos_iff_ne_zero] at *

theorem body_values (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 1 = 1) (hzero : s.natReg 4 = 0) :
    let t := runCode params input bodyCode s
    t.realReg 0 = s.realReg 0 ∧ t.natReg 0 = s.natReg 0 - 1 ∧
      t.natReg 1 = 1 ∧ t.natReg 4 = 0 ∧
      t.natReg 2 = if 0 < s.natReg 0 - 1 ∧
        ¬((s.natReg 0 - 1 : ℕ) : ℝ) ≤ s.realReg 0 then 1 else 0 := by
  by_cases hn : s.natReg 0 - 1 = 0
  · have hle : s.natReg 0 ≤ 1 := by omega
    simp [bodyCode, testCode, runCode, step, hone, hzero, hn, hle]
  · have hpos : 1 < s.natReg 0 := by omega
    by_cases hr : ((s.natReg 0 - 1 : ℕ) : ℝ) ≤ s.realReg 0 <;>
      simp [bodyCode, testCode, runCode, step, hone, hzero, hn, hr, hpos]

theorem body_frame (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input bodyCode s).realMem = s.realMem ∧
    (runCode params input bodyCode s).natMem = s.natMem := ⟨rfl, rfl⟩

theorem loop_exec (params : Parameters) (input : Inputs) (r : ℝ) (n : ℕ)
    (s : State) (hr : s.realReg 0 = r) (hsn : s.natReg 0 = n)
    (hone : s.natReg 1 = 1) (hzero : s.natReg 4 = 0)
    (hflag : s.natReg 2 = if 0 < n ∧ ¬(n : ℝ) ≤ r then 1 else 0) :
    ∃ cost final, Exec params input loop s cost final ∧ cost ≤ 30*n+3 ∧
      final.natReg 0 = (CutoffExecution.boundedFloor r n).value ∧
      final.realReg 0 = r ∧ final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  cases n with
  | zero =>
    have hz : s.natReg 2 = 0 := by simpa using hflag
    refine ⟨3, s, Exec.whileZero s hz, by omega, ?_, hr, rfl, rfl⟩
    simpa [CutoffExecution.boundedFloor] using hsn
  | succ n =>
    by_cases hstop : (n+1 : ℝ) ≤ r
    · have hz : s.natReg 2 = 0 := by simpa [hstop] using hflag
      refine ⟨3, s, Exec.whileZero s hz, by omega, ?_, hr, rfl, rfl⟩
      simpa [CutoffExecution.boundedFloor, hstop] using hsn
    · have hnz : s.natReg 2 ≠ 0 := by simp [hflag, hstop]
      let next := runCode params input bodyCode s
      obtain ⟨hr', hn', ho', hz', hf'⟩ := body_values params input s hone hzero
      have hnn : next.natReg 0 = n := by simpa [hsn] using hn'
      have hfn : next.natReg 2 = if 0 < n ∧ ¬(n : ℝ) ≤ r then 1 else 0 := by
        simpa [hr, hsn] using hf'
      obtain ⟨cost, final, hex, hc, hv, hxv, hm, hn⟩ := loop_exec params input r n next
        (hr'.trans hr) hnn ho' hz' hfn
      have hb : Exec params input (code bodyCode) s 27 next := exec_code _ _ _ _
      refine ⟨27+cost+3, final, Exec.whileNonzero hnz hb hex, by omega, ?_, hxv,
        hm.trans (body_frame params input s).1, hn.trans (body_frame params input s).2⟩
      simpa [CutoffExecution.boundedFloor, hstop] using hv
termination_by n

theorem program_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ cost final, Exec params input program s cost final ∧ cost ≤ 30*s.natReg 0+28 ∧
      final.natReg 0 = (CutoffExecution.boundedFloor (s.realReg 0) (s.natReg 0)).value ∧
      final.realReg 0 = s.realReg 0 ∧ final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  let setup := [.nconst 1 1, .nconst 4 0] ++ testCode
  let start := runCode params input setup s
  have hv := test_values params input
    (runCode params input [.nconst 1 1, .nconst 4 0] s) (by rfl) (by rfl)
  have hs : start.realReg 0 = s.realReg 0 ∧ start.natReg 0 = s.natReg 0 ∧
      start.natReg 1 = 1 ∧ start.natReg 4 = 0 ∧
      start.natReg 2 = if 0 < s.natReg 0 ∧ ¬(s.natReg 0 : ℝ) ≤ s.realReg 0 then 1 else 0 := by
    simpa [start, setup, runCode, step] using hv
  obtain ⟨cost, final, hex, hc, hv, hx, hm, hn⟩ := loop_exec params input
    (s.realReg 0) (s.natReg 0) start hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  have hi : Exec params input (code setup) s 25 start := exec_code _ _ _ _
  exact ⟨25+cost, final, Exec.seq hi hex, by omega, hv, hx, hm, hn⟩

end Manuscript.RestrictedFloor
