import Manuscript.RestrictedSpinTerm

/-! A fixed loop sums the concrete spin-term program over the spin masks
actually stored by the local-cube generator. -/
noncomputable section
namespace Manuscript.RestrictedLocalSum
open RestrictedMachine RestrictedMaskArithmetic

structure Data where
  N : ℕ
  M : ℕ
  U : ℕ
  edgeBase : ℕ
  weightBase : ℕ
  spinBase : ℕ
  plus : ℝ
  minus : ℝ
  natMemory : ℕ → ℕ
  realMemory : ℕ → ℝ

def data (s : State) : Data :=
  ⟨s.natReg 282,s.natReg 283,s.natReg 280,s.natReg 284,s.natReg 285,s.natReg 300,
    s.realReg 250,s.realReg 251,s.natMem,s.realMem⟩
def term (d : Data) (T : ℕ) : ℝ :=
  fieldProduct d.plus d.minus d.N d.U T *
    RestrictedSpinTerm.edgeProduct d.N d.U T d.natMemory d.realMemory d.edgeBase d.weightBase 0 d.M
def sumValue (d : Data) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | i, m+1 => term d (d.natMemory (d.spinBase+i)) + sumValue d (i+1) m

def termCost (d : Data) : ℕ := 59*d.N+26+(66*d.N+56)*d.M

def prefixCode : List Instruction := [.nadd 303 300 302, .loadNat 281 303]
def suffixCode : List Instruction := [.radd 300 300 280, .nadd 302 302 304]
def body : Program := .seq (code prefixCode) (.seq RestrictedSpinTerm.program (code suffixCode))
def initCode : List Instruction := [.rconst 300 0, .nconst 302 0, .nconst 304 1]
def program : Program := .seq (code initCode) (.repeat 301 body)

theorem body_realized (params : Parameters) (input : Inputs) (s : State) (h1 : s.natReg 304=1) :
    ∃ final, Exec params input body s (termCost (data s)+15) final ∧
      final.realReg 300=s.realReg 300+term (data s) (s.natMem (s.natReg 300+s.natReg 302)) ∧
      final.natReg 302=s.natReg 302+1 ∧ data final=data s ∧
      final.natReg 304=1 := by
  let start := runCode params input prefixCode s
  obtain ⟨mid,he,hv⟩ := RestrictedSpinTerm.program_realized params input start
  have hn (r : ℕ) (hr : ((280≤r ∧ r≤285 ∧ r≠281) ∨ (300≤r ∧ r≠303))) :
      mid.natReg r=s.natReg r := by
    rw [RestrictedSpinTerm.nat_frame he r (by omega)]
    simp [start,prefixCode,runCode,step]
    split_ifs <;> omega
  have hreal (r : ℕ) (hr : r=250 ∨ r=251 ∨ 300≤r) : mid.realReg r=s.realReg r := by
    simpa [start,prefixCode,runCode,step] using RestrictedSpinTerm.real_frame he r hr
  have hm : mid.realMem=s.realMem ∧ mid.natMem=s.natMem := by
    simpa [start,prefixCode,runCode,step] using RestrictedSpinTerm.mem_frame he
  have hval : mid.realReg 280=term (data s) (s.natMem (s.natReg 300+s.natReg 302)) := by
    simpa [start,prefixCode,runCode,step,RestrictedSpinTerm.value,term,data] using hv
  let final := runCode params input suffixCode mid
  refine ⟨final,?_,?_,?_,?_,?_⟩
  · have hh := Exec.seq (exec_code params input prefixCode s) (Exec.seq he (exec_code params input suffixCode mid))
    convert hh using 1
    · rfl
    · simp [start,prefixCode,suffixCode,runCode,step,codeCost,instrCost,termCost,data]
      omega
  · simp [final,suffixCode,runCode,step,hval,hreal]
  · simp [final,suffixCode,runCode,step,hn,h1]
  · simp [data,final,suffixCode,runCode,step,hn,hreal,hm.1,hm.2]
  · simp [final,suffixCode,runCode,step,hn,h1]

theorem body_repeats (params : Parameters) (input : Inputs) (m : ℕ) :
    ∀ s : State, s.natReg 304=1 →
      ∃ final, Repeats params input body m s ((termCost (data s)+20)*m+3) final ∧
        final.realReg 300=s.realReg 300+sumValue (data s) (s.natReg 302) m ∧
        final.natReg 302=s.natReg 302+m ∧ data final=data s ∧ final.natReg 304=1 := by
  induction m with
  | zero =>
      intro s h1
      refine ⟨s,?_,?_,?_,rfl,h1⟩
      · simpa using Repeats.zero (params := params) (input := input) body s
      · simp [sumValue]
      · simp
  | succ m ih =>
      intro s h1
      obtain ⟨mid,he,hv,hi,hd,h1'⟩ := body_realized params input s h1
      obtain ⟨final,hf,hval,hindex,hdata,h1''⟩ := ih mid h1'
      refine ⟨final,?_,?_,?_,hdata.trans hd,h1''⟩
      · have hh := Repeats.succ he hf
        convert hh using 1
        rw [hd]
        ring
      · rw [hval,hv,hd,hi,sumValue]
        simp only [data]
        ring
      · omega

/-- Runtime spin-list length is register 301 and its base address is 300.
All arithmetic and list-entry reads are realized by a single fixed program. -/
theorem program_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input program s ((termCost (data s)+20)*s.natReg 301+8) final ∧
      final.realReg 300=sumValue (data s) 0 (s.natReg 301) ∧ data final=data s := by
  let start := runCode params input initCode s
  have h1 : start.natReg 304=1 := by simp [start,initCode,runCode,step]
  have hd : data start=data s := by simp [start,initCode,runCode,step,data]
  have hn : start.natReg 301=s.natReg 301 := by simp [start,initCode,runCode,step]
  obtain ⟨final,he,hv,hi,hdata,h1'⟩ := body_repeats params input (s.natReg 301) start h1
  have he' : Repeats params input body (start.natReg 301) start
      ((termCost (data start)+20)*s.natReg 301+3) final := by simpa [hn] using he
  have hloop := Exec.repeat he'
  refine ⟨final,?_,?_,hdata.trans hd⟩
  · have hh := Exec.seq (exec_code params input initCode s) hloop
    convert hh using 1
    · rfl
    · simp [initCode,codeCost,instrCost,hd]
      omega
  · have hzero : start.realReg 300=0 ∧ start.natReg 302=0 := by
      simp [start,initCode,runCode,step]
    simpa only [hd,hzero.1,hzero.2,zero_add] using hv

theorem nat_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input program s c t) (r : ℕ) (hr : 310≤r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [program,initCode,body,prefixCode,suffixCode,
    RestrictedSpinTerm.program,RestrictedSpinTerm.fieldPrefix,RestrictedSpinTerm.fieldSuffix,
    RestrictedSpinTerm.edgeBody,RestrictedSpinTerm.edgePrefix,RestrictedSpinTerm.edgeSuffix,
    characterProgram,fieldProgram,RestrictedMaskArithmetic.initCode,characterBody,fieldBody,
    code,Program.All,Instruction.natDestination]
  omega

theorem real_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input program s c t) (r : ℕ) (hr : 310≤r) : t.realReg r=s.realReg r := by
  apply he.realReg_frame
  simp [program,initCode,body,prefixCode,suffixCode,
    RestrictedSpinTerm.program,RestrictedSpinTerm.fieldPrefix,RestrictedSpinTerm.fieldSuffix,
    RestrictedSpinTerm.edgeBody,RestrictedSpinTerm.edgePrefix,RestrictedSpinTerm.edgeSuffix,
    characterProgram,fieldProgram,RestrictedMaskArithmetic.initCode,characterBody,fieldBody,
    code,Program.All,Instruction.realDestination]
  omega

end Manuscript.RestrictedLocalSum
