import Manuscript.RestrictedMachine
import Manuscript.SupportCoefficientExecution

/-! Runtime inclusion--exclusion coefficients, formed from natural register
inputs by counted index arithmetic and a counted loop. -/
noncomputable section
namespace Manuscript.RestrictedCoefficients
open RestrictedMachine

/-- Runtime inputs N,k,s in natural registers 70,71,72. -/
def initCode : List Instruction :=
  [.nsub 73 71 72, .nsub 74 70 72, .nconst 75 1,
   .nsub 74 74 75, .nconst 76 0,
   .rconst 80 1, .rconst 81 1, .rconst 82 1, .rconst 83 (-1)]

/-- One falling-factorial, factorial, and sign update. -/
def bodyCode : List Instruction :=
  [.nsub 77 74 76, .natToReal 84 77, .rmul 80 84 80,
   .nadd 76 76 75, .natToReal 84 76, .rmul 81 84 81,
   .rmul 82 83 82]

def coefficientProgram : Program :=
  .seq (code initCode)
    (.seq (.repeat 73 (code bodyCode)) (code [.rdiv 80 80 81, .rmul 80 82 80]))

def LoopInvariant (n i : ℕ) (s : State) : Prop :=
  s.natReg 74 = n ∧ s.natReg 75 = 1 ∧ s.natReg 76 = i ∧
  s.realReg 80 = n.descFactorial i ∧ s.realReg 81 = i.factorial ∧
  s.realReg 82 = (-1 : ℝ)^i ∧ s.realReg 83 = -1

@[simp] theorem bodyCode_cost : codeCost bodyCode = 26 := by
  norm_num [bodyCode, codeCost, instrCost]

@[simp] theorem initCode_cost : codeCost initCode = 18 := by
  norm_num [initCode, codeCost, instrCost]

theorem body_invariant (params : Parameters) (input : Inputs) {n i : ℕ} {s : State}
    (hs : LoopInvariant n i s) :
    LoopInvariant n (i+1) (runCode params input bodyCode s) := by
  rcases hs with ⟨hn, hone, hi, hd, hf, hsgn, hneg⟩
  simp [LoopInvariant, bodyCode, runCode, step, hn, hone, hi, hd, hf, hsgn, hneg,
    Nat.descFactorial_succ, Nat.factorial_succ, pow_succ, mul_comm]

theorem body_repeats (params : Parameters) (input : Inputs) (n m : ℕ) :
    ∀ i s, LoopInvariant n i s →
      ∃ final, Repeats params input (code bodyCode) m s (31*m+3) final ∧
        LoopInvariant n (i+m) final := by
  induction m with
  | zero =>
      intro i s hs
      exact ⟨s, by simpa using Repeats.zero (params := params) (input := input) (code bodyCode) s,
        by simpa using hs⟩
  | succ m ih =>
      intro i s hs
      let middle := runCode params input bodyCode s
      have hm : LoopInvariant n (i+1) middle := body_invariant params input hs
      obtain ⟨final, he, hf⟩ := ih (i+1) middle hm
      refine ⟨final, ?_, ?_⟩
      · have hb : Exec params input (code bodyCode) s 26 middle := by
          simpa [middle] using exec_code params input bodyCode s
        convert Repeats.succ hb he using 1 <;> omega
      · convert hf using 1 <;> omega

theorem init_invariant (params : Parameters) (input : Inputs) (s : State) :
    LoopInvariant (s.natReg 70-s.natReg 72-1) 0 (runCode params input initCode s) ∧
    (runCode params input initCode s).natReg 73 = s.natReg 71-s.natReg 72 := by
  simp [LoopInvariant, initCode, runCode, step]

theorem coefficient_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input coefficientProgram s (31*(s.natReg 71-s.natReg 72)+31) final ∧
      final.realReg 80 = SupportEvaluation.coefficient (s.natReg 70) (s.natReg 71) (s.natReg 72) := by
  let start := runCode params input initCode s
  let d := s.natReg 71-s.natReg 72
  let n := s.natReg 70-s.natReg 72-1
  obtain ⟨hstart, hd⟩ := init_invariant params input s
  obtain ⟨middle, hm, hinv⟩ := body_repeats params input n d 0 start hstart
  have hr : Exec params input (.repeat 73 (code bodyCode)) start (31*d+5) middle := by
    have hm' : Repeats params input (code bodyCode) (start.natReg 73) start (31*d+3) middle := by
      rw [show start.natReg 73 = d from hd]
      exact hm
    have hh := Exec.repeat hm'
    convert hh using 1 <;> omega
  let tail := [Instruction.rdiv 80 80 81, .rmul 80 82 80]
  let final := runCode params input tail middle
  have ht : Exec params input (code tail) middle 8 final := by
    simpa [tail, codeCost, instrCost] using exec_code params input tail middle
  refine ⟨final, ?_, ?_⟩
  · have hi : Exec params input (code initCode) s 18 start := by
      simpa [start] using exec_code params input initCode s
    have hh := Exec.seq hi (Exec.seq hr ht)
    convert hh using 1 <;> simp only [coefficientProgram, tail, d] <;> omega
  · rcases hinv with ⟨_,_,_,hdesc,hfact,hsign,_⟩
    simp only [Nat.zero_add] at hdesc hfact hsign
    have hf : ((d.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    simp only [final, tail, runCode, step, writeRealReg_realReg]
    norm_num only
    rw [hdesc, hfact, hsign, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
      mul_div_cancel_left₀ _ hf]
    rfl

end Manuscript.RestrictedCoefficients
