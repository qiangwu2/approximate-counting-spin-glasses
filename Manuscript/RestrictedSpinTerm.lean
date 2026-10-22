import Manuscript.RestrictedMaskArithmetic

/-! A fixed RAM program for one local-spin term. The runtime registers give
N,M,a support mask,a spin mask,and the addresses of the incidence-mask and
cached-weight arrays. All M interactions are scanned, with N charged digit
steps per character; absent induced edges contribute the factor one. -/
noncomputable section
namespace Manuscript.RestrictedSpinTerm
open RestrictedMachine RestrictedMaskArithmetic

def edgePrefix : List Instruction :=
  [.nadd 289 284 286, .loadNat 251 289,
   .ncopy 250 282, .ncopy 252 280, .ncopy 253 281]
def edgeSuffix : List Instruction :=
  [.nmul 289 286 288, .nadd 289 289 285, .loadReal 281 289,
   .rmul 281 281 265, .rconst 282 1, .radd 281 282 281,
   .rmul 280 280 281, .nadd 286 286 287]
def edgeBody : Program :=
  .seq (code edgePrefix) (.seq characterProgram (code edgeSuffix))

def fieldPrefix : List Instruction := [.ncopy 250 282, .ncopy 252 280, .ncopy 253 281]
def fieldSuffix : List Instruction := [.rcopy 280 265, .nconst 286 0, .nconst 287 1, .nconst 288 2]
def program : Program :=
  .seq (code fieldPrefix) (.seq fieldProgram
    (.seq (code fieldSuffix) (.repeat 283 edgeBody)))

/-- The base addresses are arbitrary runtime values. -/
def edgeProduct (N U T : ℕ) (incidence : ℕ → ℕ) (weight : ℕ → ℝ)
    (baseE baseW : ℕ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | i, m+1 => (1+weight (baseW+2*i)*character N (incidence (baseE+i)) U T) *
      edgeProduct N U T incidence weight baseE baseW (i+1) m

def Stable (s t : State) : Prop :=
  (∀ r, 280≤r → r≤288 → r≠286 → t.natReg r=s.natReg r) ∧
  t.realMem=s.realMem ∧ t.natMem=s.natMem

private theorem character_nat_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input characterProgram s c t) (r : ℕ) (hr : 280≤r) :
    t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [characterProgram,RestrictedMaskArithmetic.initCode,characterBody,code,Program.All,
    Instruction.natDestination]
  omega

private theorem character_real_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input characterProgram s c t) (r : ℕ) (hr : 280≤r) :
    t.realReg r=s.realReg r := by
  apply he.realReg_frame
  simp [characterProgram,RestrictedMaskArithmetic.initCode,characterBody,code,Program.All,
    Instruction.realDestination]
  omega

private theorem character_mem_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input characterProgram s c t) :
    t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  constructor
  · apply he.realMem_frame
    simp [characterProgram,RestrictedMaskArithmetic.initCode,characterBody,code,Program.All,
      Instruction.writesRealMemory]
  · apply he.natMem_frame
    simp [characterProgram,RestrictedMaskArithmetic.initCode,characterBody,code,Program.All,
      Instruction.writesNatMemory]

theorem edge_realized (params : Parameters) (input : Inputs) (s : State)
    (h1 : s.natReg 287=1) (h2 : s.natReg 288=2) :
    ∃ final, Exec params input edgeBody s (66*s.natReg 282+51) final ∧
      final.realReg 280 = s.realReg 280 *
        (1+s.realMem (s.natReg 285+2*s.natReg 286)*
          character (s.natReg 282) (s.natMem (s.natReg 284+s.natReg 286))
            (s.natReg 280) (s.natReg 281)) ∧
      final.natReg 286=s.natReg 286+1 ∧ Stable s final := by
  let start := runCode params input edgePrefix s
  obtain ⟨mid,he,hv⟩ := character_realized params input start
  have hnat (r : ℕ) (hr : 280≤r) (hr' : r≤288) : mid.natReg r=s.natReg r := by
    rw [character_nat_frame he r hr]
    have hne : r≠289 := by omega
    simp [start,edgePrefix,runCode,step,hne]
    split_ifs <;> omega
  have hreal : mid.realReg 280=s.realReg 280 := by
    simpa [start,edgePrefix,runCode,step] using character_real_frame he 280 (by omega)
  have hm : mid.realMem=s.realMem ∧ mid.natMem=s.natMem := by
    simpa [start,edgePrefix,runCode,step] using character_mem_frame he
  have hval : mid.realReg 265=character (s.natReg 282)
      (s.natMem (s.natReg 284+s.natReg 286)) (s.natReg 280) (s.natReg 281) := by
    simpa [start,edgePrefix,runCode,step] using hv
  let final := runCode params input edgeSuffix mid
  refine ⟨final,?_,?_,?_,?_,?_,?_⟩
  · have hp := exec_code params input edgePrefix s
    have ht := exec_code params input edgeSuffix mid
    have hh := Exec.seq hp (Exec.seq he ht)
    convert hh using 1
    · rfl
    · simp [start,edgePrefix,edgeSuffix,runCode,step,codeCost,instrCost]
      omega
  · simp [final,edgeSuffix,runCode,step,hreal,hval,hm.1,hnat,h2,Nat.add_comm,Nat.mul_comm]
  · simp [final,edgeSuffix,runCode,step,hnat,h1]
  · intro r hr hr' hne
    have h289 : r≠289 := by omega
    simp [final,edgeSuffix,runCode,step,hnat,hr,hr',hne,h289]
  · simp [final,edgeSuffix,runCode,step,hm.1]
  · simp [final,edgeSuffix,runCode,step,hm.2]

theorem edge_repeats (params : Parameters) (input : Inputs) (m : ℕ) :
    ∀ s : State, s.natReg 287=1 → s.natReg 288=2 →
      ∃ final, Repeats params input edgeBody m s ((66*s.natReg 282+56)*m+3) final ∧
        final.realReg 280=s.realReg 280*edgeProduct (s.natReg 282) (s.natReg 280) (s.natReg 281)
          s.natMem s.realMem (s.natReg 284) (s.natReg 285) (s.natReg 286) m ∧
        final.natReg 286=s.natReg 286+m ∧ Stable s final := by
  induction m with
  | zero =>
      intro s h1 h2
      refine ⟨s,?_,?_,?_,?_,rfl,rfl⟩
      · simpa using Repeats.zero (params := params) (input := input) edgeBody s
      · simp [edgeProduct]
      · simp
      · intros; rfl
  | succ m ih =>
      intro s h1 h2
      obtain ⟨mid,he,hv,hi,hs⟩ := edge_realized params input s h1 h2
      have hn (r : ℕ) (hr : 280≤r) (hr' : r≤288) (hne : r≠286) := hs.1 r hr hr' hne
      obtain ⟨final,hf,hval,hindex,hstable⟩ := ih mid
        (by simpa [hn] using h1) (by simpa [hn] using h2)
      refine ⟨final,?_,?_,?_,?_,?_,?_⟩
      · have hh := Repeats.succ he hf
        convert hh using 1
        simp [hn]
        ring
      · rw [hval,hv,edgeProduct]
        simp only [hn 282 (by omega) (by omega) (by omega),hn 280 (by omega) (by omega) (by omega),
          hn 281 (by omega) (by omega) (by omega),hn 284 (by omega) (by omega) (by omega),
          hn 285 (by omega) (by omega) (by omega),hs.2.1,hs.2.2,hi]
        ring
      · omega
      · intro r hr hr' hne
        exact (hstable.1 r hr hr' hne).trans (hn r hr hr' hne)
      · exact hstable.2.1.trans hs.2.1
      · exact hstable.2.2.trans hs.2.2

def value (s : State) : ℝ :=
  fieldProduct (s.realReg 250) (s.realReg 251) (s.natReg 282) (s.natReg 280) (s.natReg 281) *
    edgeProduct (s.natReg 282) (s.natReg 280) (s.natReg 281) s.natMem s.realMem
      (s.natReg 284) (s.natReg 285) 0 (s.natReg 283)

/-- One fixed program computes the complete biased spin term from the
previously generated masks and physical cache. The cost is derived from
actual loops and is polynomial in N and M. -/
theorem program_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input program s
        (59*s.natReg 282+26+(66*s.natReg 282+56)*s.natReg 283) final ∧
      final.realReg 280=value s := by
  let start := runCode params input fieldPrefix s
  obtain ⟨mid,he,hv⟩ := field_realized params input start
  have hn (r : ℕ) (hr : 280≤r) : mid.natReg r=s.natReg r := by
    rw [he.natReg_frame (by
      simp [fieldProgram,RestrictedMaskArithmetic.initCode,fieldBody,code,Program.All,
        Instruction.natDestination]
      omega)]
    simp [start,fieldPrefix,runCode,step]
    split_ifs <;> omega
  have hm : mid.realMem=s.realMem ∧ mid.natMem=s.natMem := by
    constructor
    · have hx := he.realMem_frame (by
        simp [fieldProgram,RestrictedMaskArithmetic.initCode,fieldBody,code,Program.All,
          Instruction.writesRealMemory])
      simpa [start,fieldPrefix,runCode,step] using hx
    · have hx := he.natMem_frame (by
        simp [fieldProgram,RestrictedMaskArithmetic.initCode,fieldBody,code,Program.All,
          Instruction.writesNatMemory])
      simpa [start,fieldPrefix,runCode,step] using hx
  have hvalue : mid.realReg 265=fieldProduct (s.realReg 250) (s.realReg 251)
      (s.natReg 282) (s.natReg 280) (s.natReg 281) := by
    simpa [start,fieldPrefix,runCode,step] using hv
  let ready := runCode params input fieldSuffix mid
  obtain ⟨final,hr,hval,hindex,hstable⟩ := edge_repeats params input (s.natReg 283) ready
    (by simp [ready,fieldSuffix,runCode,step]) (by simp [ready,fieldSuffix,runCode,step])
  have hbound : ready.natReg 283=s.natReg 283 := by simp [ready,fieldSuffix,runCode,step,hn]
  have hr' : Repeats params input edgeBody (ready.natReg 283) ready
      ((66*ready.natReg 282+56)*s.natReg 283+3) final := by simpa [hbound] using hr
  have hloop := Exec.repeat hr'
  refine ⟨final,?_,?_⟩
  · have hh := Exec.seq (exec_code params input fieldPrefix s)
      (Exec.seq he (Exec.seq (exec_code params input fieldSuffix mid) hloop))
    convert hh using 1
    · rfl
    · simp [start,ready,fieldPrefix,fieldSuffix,runCode,step,codeCost,instrCost,hn]
      ring
  · simpa [value,ready,fieldSuffix,runCode,step,hn,hm.1,hm.2,hvalue] using hval

theorem nat_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input program s c t) (r : ℕ)
    (hr : (280≤r ∧ r≤285) ∨ 300≤r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [program,fieldPrefix,fieldSuffix,edgeBody,edgePrefix,edgeSuffix,
    characterProgram,fieldProgram,RestrictedMaskArithmetic.initCode,characterBody,fieldBody,
    code,Program.All,Instruction.natDestination]
  omega

theorem real_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input program s c t) (r : ℕ)
    (hr : r=250 ∨ r=251 ∨ 300≤r) : t.realReg r=s.realReg r := by
  apply he.realReg_frame
  simp [program,fieldPrefix,fieldSuffix,edgeBody,edgePrefix,edgeSuffix,
    characterProgram,fieldProgram,RestrictedMaskArithmetic.initCode,characterBody,fieldBody,
    code,Program.All,Instruction.realDestination]
  omega

theorem mem_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input program s c t) : t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  constructor
  · apply he.realMem_frame
    simp [program,fieldPrefix,fieldSuffix,edgeBody,edgePrefix,edgeSuffix,
      characterProgram,fieldProgram,RestrictedMaskArithmetic.initCode,characterBody,fieldBody,
      code,Program.All,Instruction.writesRealMemory]
  · apply he.natMem_frame
    simp [program,fieldPrefix,fieldSuffix,edgeBody,edgePrefix,edgeSuffix,
      characterProgram,fieldProgram,RestrictedMaskArithmetic.initCode,characterBody,fieldBody,
      code,Program.All,Instruction.writesNatMemory]

end Manuscript.RestrictedSpinTerm
