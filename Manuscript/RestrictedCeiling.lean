import Manuscript.RestrictedMachine
import Manuscript.CountedCeil

/-! Ceiling by actual comparisons and increments in the restricted machine. -/
noncomputable section
namespace Manuscript.RestrictedCeiling
open RestrictedMachine

/-- Real register 0 is the target, natural register 0 the current integer,
natural register 1 is one, and natural register 2 is the continuation flag. -/
def testCode : List Instruction :=
  [.natToReal 1 0, .rle 2 0 1, .nsub 2 1 2]

def bodyCode : List Instruction := [.nadd 0 0 1] ++ testCode
def loop : Program := .while 2 (code bodyCode)
def program : Program :=
  .seq (code ([.nconst 0 0, .nconst 1 1] ++ testCode)) loop

theorem test_cost : codeCost testCode = 11 := rfl
theorem body_cost : codeCost bodyCode = 15 := rfl

theorem test_values (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 1 = 1) :
    let t := runCode params input testCode s
    t.realReg 0 = s.realReg 0 ∧ t.natReg 0 = s.natReg 0 ∧
      t.natReg 1 = 1 ∧
      t.natReg 2 = if s.realReg 0 ≤ (s.natReg 0 : ℝ) then 0 else 1 := by
  simp [testCode, runCode, step, hone]
  split_ifs <;> rfl

theorem body_values (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 1 = 1) :
    let t := runCode params input bodyCode s
    t.realReg 0 = s.realReg 0 ∧ t.natReg 0 = s.natReg 0 + 1 ∧
      t.natReg 1 = 1 ∧
      t.natReg 2 = if s.realReg 0 ≤ ((s.natReg 0 + 1 : ℕ) : ℝ) then 0 else 1 := by
  simp [bodyCode, testCode, runCode, step, hone]
  split_ifs <;> rfl

theorem body_frame (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input bodyCode s).realMem = s.realMem ∧
    (runCode params input bodyCode s).natMem = s.natMem := ⟨rfl, rfl⟩

theorem loop_exec (params : Parameters) (input : Inputs) (x : ℝ) (n : ℕ)
    (hn : n ≤ Nat.ceil x) (s : State)
    (hx : s.realReg 0 = x) (hsn : s.natReg 0 = n) (hone : s.natReg 1 = 1)
    (hflag : s.natReg 2 = if x ≤ (n : ℝ) then 0 else 1) :
    ∃ final, Exec params input loop s (18 * (Nat.ceil x - n) + 3) final ∧
      final.natReg 0 = Nat.ceil x ∧ final.realReg 0 = x ∧
      final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  by_cases hstop : x ≤ (n : ℝ)
  · have heq : n = Nat.ceil x := le_antisymm hn (Nat.ceil_le.mpr hstop)
    have hz : s.natReg 2 = 0 := by simpa [hstop] using hflag
    refine ⟨s, ?_, hsn.trans heq, hx, rfl, rfl⟩
    simpa [heq, loop] using Exec.whileZero (params := params) (input := input)
      (body := code bodyCode) s hz
  · have hnext : n < Nat.ceil x := Nat.lt_ceil.mpr (lt_of_not_ge hstop)
    let next := runCode params input bodyCode s
    have hnz : s.natReg 2 ≠ 0 := by simp [hflag, hstop]
    obtain ⟨hx', hn', hone', hflag'⟩ := body_values params input s hone
    have hxn : next.realReg 0 = x := hx'.trans hx
    have hnn : next.natReg 0 = n + 1 := by simpa [hsn] using hn'
    have hfn : next.natReg 2 = if x ≤ ((n + 1 : ℕ) : ℝ) then 0 else 1 := by
      simpa [hx, hsn] using hflag'
    obtain ⟨final, hr, hf, hxr, hmr, hnr⟩ := loop_exec params input x (n+1)
      (by omega) next hxn hnn hone' hfn
    have hb : Exec params input (code bodyCode) s 15 next := exec_code _ _ _ _
    have hrun := Exec.whileNonzero hnz hb hr
    refine ⟨final, ?_, hf, hxr, hmr.trans (body_frame params input s).1,
      hnr.trans (body_frame params input s).2⟩
    have hc : 18 * (Nat.ceil x - n) + 3 =
        15 + (18 * (Nat.ceil x - (n+1)) + 3) + 3 := by omega
    rw [hc]
    exact hrun
termination_by Nat.ceil x - n
decreasing_by omega

theorem program_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input program s (18 * Nat.ceil (s.realReg 0) + 16) final ∧
      final.natReg 0 = (CountedCeil.ceiling (s.realReg 0)).value ∧
      final.realReg 0 = s.realReg 0 ∧
      final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  let setup := [.nconst 0 0, .nconst 1 1] ++ testCode
  let start := runCode params input setup s
  have hs0 : start.natReg 0 = 0 := by simp [start, setup, testCode, runCode, step]
  have hs1 : start.natReg 1 = 1 := by simp [start, setup, testCode, runCode, step]
  have hx : start.realReg 0 = s.realReg 0 := by simp [start, setup, testCode, runCode, step]
  have hflag : start.natReg 2 = if s.realReg 0 ≤ (0 : ℝ) then 0 else 1 := by
    simp [start, setup, testCode, runCode, step]
    split_ifs <;> rfl
  obtain ⟨final, hr, hv, hxv, hm, hn⟩ := loop_exec params input (s.realReg 0) 0
    (Nat.zero_le _) start hx hs0 hs1 (by simpa using hflag)
  have hs : Exec params input (code setup) s 13 start := exec_code _ _ _ _
  refine ⟨final, ?_, ?_, hxv, hm, hn⟩
  · have hh := Exec.seq hs hr
    convert hh using 1 <;> simp [program, setup] <;> omega
  · simpa using hv

end Manuscript.RestrictedCeiling
