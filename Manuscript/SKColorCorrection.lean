import Manuscript.RestrictedFrames
import Manuscript.SKChargedExtractionExecution

/-! Uniform computation of the inverse coloring probability. Both numerator
and falling factorial are computed from runtime natural values, including
all zero-palette and zero-denominator cases. -/
noncomputable section
namespace Manuscript.SKColorCorrection
open RestrictedMachine

def setupCode : List Instruction :=
  [.rconst 300 1,.rconst 301 1,.natToReal 302 300,.nconst 302 0,.nconst 303 1]
def bodyCode : List Instruction :=
  [.rmul 300 300 302,.nsub 304 300 302,.natToReal 303 304,
   .rmul 301 301 303,.nadd 302 302 303]
def program : Program := .seq (code setupCode)
  (.seq (.repeat 301 (code bodyCode)) (.atom (.rdiv 304 300 301)))

def Invariant (K j : ℕ) (s : State) : Prop :=
  s.natReg 300=K ∧ s.natReg 302=j ∧ s.natReg 303=1 ∧
  s.realReg 302=(K:ℝ) ∧ s.realReg 300=(K:ℝ)^j ∧
  s.realReg 301=(K.descFactorial j:ℝ)

theorem body_invariant (p : Parameters) (i : Inputs) (K j : ℕ) (s : State)
    (hs : Invariant K j s) :
    Invariant K (j+1) (runCode p i bodyCode s) := by
  rcases hs with ⟨hK,hj,h1,hrK,hn,hd⟩
  simp [Invariant,bodyCode,runCode,step,hK,hj,h1,hrK,hn,hd,
    pow_succ,Nat.descFactorial_succ,Nat.cast_mul,mul_comm]

theorem loop_realized (p : Parameters) (i : Inputs) (K j n : ℕ) (s : State)
    (hs : Invariant K j s) :
    ∃ t, Repeats p i (code bodyCode) n s (24*n+3) t ∧ Invariant K (j+n) t := by
  induction n generalizing j s with
  | zero => exact ⟨s,Repeats.zero _ _,by simpa using hs⟩
  | succ n ih =>
    let d := runCode p i bodyCode s
    obtain ⟨t,ht,hv⟩ := ih (j+1) d (body_invariant p i K j s hs)
    refine ⟨t,?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv⟩
    have hb : Exec p i (code bodyCode) s 19 d := by
      simpa [bodyCode,codeCost,instrCost,d] using exec_code p i bodyCode s
    convert Repeats.succ hb ht using 1 <;> omega

theorem correction_realized (p : Parameters) (i : Inputs) (s : State) :
    ∃ t, Exec p i program s (24*s.natReg 301+16) t ∧
      t.realReg 304=(SpinGlass.ColoringProbability.probability
        (s.natReg 300) (s.natReg 301))⁻¹ ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let a := runCode p i setupCode s
  have ha : Invariant (s.natReg 300) 0 a := by
    simp [a,setupCode,runCode,step,Invariant]
  have hm : a.natReg 301=s.natReg 301 := by simp [a,setupCode,runCode,step]
  obtain ⟨b,hb,hv⟩ := loop_realized p i (s.natReg 300) 0 (a.natReg 301) a ha
  let t := step p i (.rdiv 304 300 301) b
  have he : Exec p i program s (24*s.natReg 301+16) t := by
    have hs : Exec p i (code setupCode) s 7 a := by
      simpa [setupCode,codeCost,instrCost,a] using exec_code p i setupCode s
    have ht := Exec.seq hs (Exec.seq (Exec.repeat hb) (Exec.atom (.rdiv 304 300 301) b))
    convert ht using 1 <;> first | rfl | simp [hm,instrCost]; omega
  refine ⟨t,he,?_,?_,?_⟩
  · rcases hv with ⟨_,_,_,_,hn,hd⟩
    simp only [Nat.zero_add,hm] at hn hd
    simp [t,step,hn,hd,SpinGlass.ColoringProbability.probability,inv_div]
  · apply he.realMem_frame
    simp [program,setupCode,bodyCode,code,Program.All,Instruction.writesRealMemory]
  · apply he.natMem_frame
    simp [program,setupCode,bodyCode,code,Program.All,Instruction.writesNatMemory]

theorem natReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i program s c t) (hr : r≠302 ∧ r≠303 ∧ r≠304) :
    t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [program,setupCode,bodyCode,code,Program.All,Instruction.natDestination]
  omega

theorem realReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i program s c t) (hr : r<300 ∨ 304<r) :
    t.realReg r=s.realReg r := by
  apply h.realReg_frame
  simp [program,setupCode,bodyCode,code,Program.All,Instruction.realDestination]
  omega
end Manuscript.SKColorCorrection
