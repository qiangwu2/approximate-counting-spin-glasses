import Manuscript.RestrictedFrames
import Manuscript.RestrictedLoops

/-!
Uniform digit-index arithmetic. Inputs are natural registers, and the loop
bound is read at execution time. These programs do not contain a precomputed
table of output indices. The only immediates are fixed small integers.
-/
noncomputable section
namespace Manuscript.RestrictedMachine
namespace IndexGeneration

def rho (n : ℕ) : ℕ := if 4 ≤ n then 4+n%2 else n

/-- Specification of the base-six degree combination with an accumulator.
This recursion is proved equal to the output of the fixed program below. -/
def degreeFold : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, a, _ => a
  | n+1, x, y, a, w => degreeFold n (x/6) (y/6) (a+rho (x%6+y%6)*w) (w*6)

def degreePrefix : List Instruction :=
  [.nmod 109 100 105, .nmod 110 101 105, .nadd 111 109 110, .nle 112 106 111]
def degreeHigh : List Instruction := [.nmod 113 111 107, .nadd 113 106 113]
def degreeLow : List Instruction := [.ncopy 113 111]
def degreeTail : List Instruction :=
  [.nmul 114 113 102, .nadd 103 103 114,
   .ndiv 100 100 105, .ndiv 101 101 105, .nmul 102 102 105]
def degreeBody : Program := .seq (code degreePrefix)
  (.seq (.branch 112 (code degreeHigh) (code degreeLow)) (code degreeTail))
def degreeInit : List Instruction :=
  [.nconst 102 1, .nconst 103 0, .nconst 105 6, .nconst 106 4, .nconst 107 2]
/-- Input x=nat100, y=nat101, digit count=nat104; result=nat103.
Only natural registers100..114 are scratch; both memories remain unchanged. -/
def degreeProgram : Program := .seq (code degreeInit) (.repeat 104 degreeBody)

def degreeNext (p : Parameters) (i : Inputs) (s : State) : State :=
  let m := runCode p i degreePrefix s
  let t := if m.natReg 112 = 0 then runCode p i degreeLow m else runCode p i degreeHigh m
  runCode p i degreeTail t
def degreeConstants (s : State) : Prop := s.natReg 105=6 ∧ s.natReg 106=4 ∧ s.natReg 107=2

theorem degree_next_exec (p : Parameters) (i : Inputs) (s : State) :
    ∃ c, Exec p i degreeBody s c (degreeNext p i s) ∧ c ≤ 47 := by
  let m := runCode p i degreePrefix s
  by_cases h : m.natReg 112 = 0
  · refine ⟨16+(2+3+20), ?_, by decide⟩
    exact Exec.seq (exec_code p i degreePrefix s)
      (Exec.seq (Exec.branchZero h (exec_code p i degreeLow m))
        (by simpa [degreeNext, m, h, degreeTail, codeCost, instrCost] using exec_code p i degreeTail (runCode p i degreeLow m)))
  · refine ⟨16+(8+3+20), ?_, by decide⟩
    exact Exec.seq (exec_code p i degreePrefix s)
      (Exec.seq (Exec.branchNonzero h (exec_code p i degreeHigh m))
        (by simpa [degreeNext, m, h, degreeTail, codeCost, instrCost] using exec_code p i degreeTail (runCode p i degreeHigh m)))

theorem degree_next_spec (p : Parameters) (i : Inputs) (s : State) (hs : degreeConstants s) :
    let t := degreeNext p i s
    t.natReg 100 = s.natReg 100 / 6 ∧ t.natReg 101 = s.natReg 101 / 6 ∧
    t.natReg 102 = s.natReg 102 * 6 ∧
    t.natReg 103 = s.natReg 103 + rho (s.natReg 100%6+s.natReg 101%6)*s.natReg 102 ∧
    degreeConstants t := by
  rcases hs with ⟨h6,h4,h2⟩
  by_cases h : 4 ≤ s.natReg 100%6+s.natReg 101%6 <;>
    simp [degreeNext, degreePrefix, degreeHigh, degreeLow, degreeTail,
      runCode, step, h6, h4, h2, h, rho, degreeConstants]

theorem degree_iterate_value (p : Parameters) (i : Inputs) (n : ℕ) (s : State)
    (hs : degreeConstants s) :
    (iterateState (degreeNext p i) n s).natReg 103 =
      degreeFold n (s.natReg 100) (s.natReg 101) (s.natReg 103) (s.natReg 102) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have h := degree_next_spec p i s hs
    rw [iterateState, ih _ h.2.2.2.2, h.1, h.2.1, h.2.2.1, h.2.2.2.1]
    rfl

theorem degree_execution (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i degreeProgram s c t ∧ c ≤ 52*s.natReg 104+10 ∧
      t.natReg 103 = degreeFold (s.natReg 104) (s.natReg 100) (s.natReg 101) 0 1 := by
  let m := runCode p i degreeInit s
  have hm : degreeConstants m := by simp [m, degreeInit, degreeConstants, runCode, step]
  have hb : m.natReg 104 = s.natReg 104 := by simp [m, degreeInit, runCode, step]
  obtain ⟨c,hc,bc⟩ := repeats_bounded p i degreeBody (degreeNext p i) 47 (degree_next_exec p i) (m.natReg 104) m
  refine ⟨5+(c+2), iterateState (degreeNext p i) (m.natReg 104) m,
    Exec.seq (exec_code p i degreeInit s) (Exec.repeat hc), ?_, ?_⟩
  · rw [hb] at bc
    omega
  · rw [degree_iterate_value p i _ m hm]
    simp [m, degreeInit, runCode, step]

theorem degree_realReg_frame (p : Parameters) (i : Inputs) (s t : State) (c r : ℕ)
    (h : Exec p i degreeProgram s c t) : t.realReg r = s.realReg r := by
  apply h.realReg_frame
  simp [degreeProgram, degreeBody, degreeInit, degreePrefix, degreeHigh, degreeLow,
    degreeTail, code, Program.All, Instruction.realDestination]
theorem degree_natReg_frame (p : Parameters) (i : Inputs) (s t : State) (c r : ℕ)
    (h : Exec p i degreeProgram s c t) (hr : r < 100 ∨ 114 < r) : t.natReg r = s.natReg r := by
  apply h.natReg_frame
  simp [degreeProgram, degreeBody, degreeInit, degreePrefix, degreeHigh, degreeLow,
    degreeTail, code, Program.All, Instruction.natDestination]
  omega
theorem degree_memory_frame (p : Parameters) (i : Inputs) (s t : State) (c : ℕ)
    (h : Exec p i degreeProgram s c t) : t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  constructor
  · apply h.realMem_frame
    simp [degreeProgram, degreeBody, degreeInit, degreePrefix, degreeHigh, degreeLow,
      degreeTail, code, Program.All, Instruction.writesRealMemory]
  · apply h.natMem_frame
    simp [degreeProgram, degreeBody, degreeInit, degreePrefix, degreeHigh, degreeLow,
      degreeTail, code, Program.All, Instruction.writesNatMemory]

/-- Sum of the common set-bit indicators in the first n positions. -/
def overlapFold : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, a => a
  | n+1, x, y, a => overlapFold n (x/2) (y/2) (a+(x%2)*(y%2))
def overlapInit : List Instruction := [.nconst 122 0, .nconst 124 2]
def overlapBody : List Instruction :=
  [.nmod 125 120 124, .nmod 126 121 124, .nmul 127 125 126,
   .nadd 122 122 127, .ndiv 120 120 124, .ndiv 121 121 124]
/-- Input masks nat120,nat121; number of bits nat123; overlap count nat122. -/
def overlapProgram : Program := .seq (code overlapInit) (.repeat 123 (code overlapBody))
def overlapNext (p : Parameters) (i : Inputs) (s : State) : State := runCode p i overlapBody s

theorem overlap_next_spec (p : Parameters) (i : Inputs) (s : State) (hs : s.natReg 124=2) :
    let t := overlapNext p i s
    t.natReg 120 = s.natReg 120/2 ∧ t.natReg 121 = s.natReg 121/2 ∧
    t.natReg 122 = s.natReg 122+(s.natReg 120%2)*(s.natReg 121%2) ∧ t.natReg 124=2 := by
  simp [overlapNext, overlapBody, runCode, step, hs]

theorem overlap_iterate_value (p : Parameters) (i : Inputs) (n : ℕ) (s : State)
    (hs : s.natReg 124=2) :
    (iterateState (overlapNext p i) n s).natReg 122 =
      overlapFold n (s.natReg 120) (s.natReg 121) (s.natReg 122) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have h := overlap_next_spec p i s hs
    rw [iterateState, ih _ h.2.2.2, h.1, h.2.1, h.2.2.1]
    rfl

theorem overlap_execution (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i overlapProgram s c t ∧ c ≤ 29*s.natReg 123+7 ∧
      t.natReg 122 = overlapFold (s.natReg 123) (s.natReg 120) (s.natReg 121) 0 := by
  let m := runCode p i overlapInit s
  have hm : m.natReg 124=2 := by simp [m, overlapInit, runCode, step]
  have hb : m.natReg 123 = s.natReg 123 := by simp [m, overlapInit, runCode, step]
  have bodyRuns : ∀ s, ∃ c, Exec p i (code overlapBody) s c (overlapNext p i s) ∧ c ≤ 24 :=
    fun s => ⟨24, exec_code p i overlapBody s, by decide⟩
  obtain ⟨c,hc,bc⟩ := repeats_bounded p i (code overlapBody) (overlapNext p i) 24 bodyRuns (m.natReg 123) m
  refine ⟨2+(c+2), iterateState (overlapNext p i) (m.natReg 123) m,
    Exec.seq (exec_code p i overlapInit s) (Exec.repeat hc), ?_, ?_⟩
  · rw [hb] at bc
    omega
  · rw [overlap_iterate_value p i _ m hm]
    simp [m, overlapInit, runCode, step]

theorem overlap_natReg_frame (p : Parameters) (i : Inputs) (s t : State) (c r : ℕ)
    (h : Exec p i overlapProgram s c t) (hr : r < 120 ∨ 127 < r) : t.natReg r = s.natReg r := by
  apply h.natReg_frame
  simp [overlapProgram, overlapInit, overlapBody, code, Program.All, Instruction.natDestination]
  omega

theorem overlap_memory_frame (p : Parameters) (i : Inputs) (s t : State) (c : ℕ)
    (h : Exec p i overlapProgram s c t) : t.realMem = s.realMem ∧ t.natMem = s.natMem := by
  constructor
  · apply h.realMem_frame
    simp [overlapProgram, overlapInit, overlapBody, code, Program.All, Instruction.writesRealMemory]
  · apply h.natMem_frame
    simp [overlapProgram, overlapInit, overlapBody, code, Program.All, Instruction.writesNatMemory]

def powerInit : List Instruction := [.nconst 132 1]
def powerBody : List Instruction := [.nmul 132 132 130]
/-- Input base nat130 and exponent nat131; output nat132. -/
def powerProgram : Program := .seq (code powerInit) (.repeat 131 (code powerBody))

theorem power_iterate_value (p : Parameters) (i : Inputs) (n : ℕ) (s : State) :
    (iterateState (runCode p i powerBody) n s).natReg 132 = s.natReg 132 * s.natReg 130 ^ n := by
  induction n generalizing s with
  | zero => simp [iterateState]
  | succ n ih =>
    rw [iterateState, ih]
    simp [powerBody, runCode, step, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem power_execution (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i powerProgram s c t ∧ c ≤ 9*s.natReg 131+6 ∧
      t.natReg 132 = s.natReg 130 ^ s.natReg 131 := by
  let m := runCode p i powerInit s
  have hb : m.natReg 131 = s.natReg 131 := by simp [m, powerInit, runCode, step]
  have bodyRuns : ∀ s, ∃ c, Exec p i (code powerBody) s c (runCode p i powerBody s) ∧ c ≤ 4 :=
    fun s => ⟨4, exec_code p i powerBody s, by decide⟩
  obtain ⟨c,hc,bc⟩ := repeats_bounded p i (code powerBody) (runCode p i powerBody) 4 bodyRuns (m.natReg 131) m
  refine ⟨1+(c+2), iterateState (runCode p i powerBody) (m.natReg 131) m,
    Exec.seq (exec_code p i powerInit s) (Exec.repeat hc), ?_, ?_⟩
  · rw [hb] at bc
    omega
  · rw [power_iterate_value]
    simp [m, powerInit, runCode, step]

end IndexGeneration
end Manuscript.RestrictedMachine
