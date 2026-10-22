import Manuscript.SKPhysicalLookup
import Manuscript.RestrictedIndices

noncomputable section
namespace Manuscript.SKPhysicalPair
open RestrictedMachine

def checkCode : List Instruction :=
  [.neq 392 390 391,.neq 393 390 500,.neq 394 391 500,.nadd 393 393 394]
def firstCode : List Instruction := [.nconst 130 2,.ncopy 131 390]
def secondCode : List Instruction := [.ncopy 395 132,.ncopy 131 391]
def lookupCode : List Instruction := [.nadd 380 395 132,.ncopy 381 501]
def physical : Program := .seq (code firstCode) (.seq IndexGeneration.powerProgram
  (.seq (code secondCode) (.seq IndexGeneration.powerProgram
    (.seq (code lookupCode) (.seq SKPhysicalLookup.program (code [.rcopy 390 380]))))))
def program : Program := .seq (code checkCode)
  (.branch 393 (code [.rcopy 390 504]) (.branch 392 (code [.rconst 390 0]) physical))

def value (s : State) : ℝ :=
  if s.natReg 390=s.natReg 500 ∨ s.natReg 391=s.natReg 500 then s.realReg 504
  else if s.natReg 390=s.natReg 391 then 0
  else ∑i∈Finset.range (s.natReg 501),
    if s.natMem i=2^s.natReg 390+2^s.natReg 391 then s.realMem (2*i) else 0

theorem power_frames (params : Parameters) (input : Inputs) (s t : State) (c : ℕ)
    (he : Exec params input IndexGeneration.powerProgram s c t) :
    t.realMem=s.realMem ∧ t.natMem=s.natMem ∧
    (∀r,r≠132 → t.natReg r=s.natReg r) := by
  refine ⟨?_,?_,?_⟩
  · exact he.realMem_frame (by simp [IndexGeneration.powerProgram,IndexGeneration.powerInit,
      IndexGeneration.powerBody,code,Program.All,Instruction.writesRealMemory])
  · exact he.natMem_frame (by simp [IndexGeneration.powerProgram,IndexGeneration.powerInit,
      IndexGeneration.powerBody,code,Program.All,Instruction.writesNatMemory])
  · intro r hr
    apply he.natReg_frame
    simpa [IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
      code,Program.All,Instruction.natDestination,ne_comm] using hr

theorem physical_execution (params : Parameters) (input : Inputs) (s : State) :
    ∃c t,Exec params input physical s c t ∧
      c≤9*(s.natReg 390+s.natReg 391)+34*s.natReg 501+36 ∧
      t.realReg 390=∑i∈Finset.range (s.natReg 501),
        if s.natMem i=2^s.natReg 390+2^s.natReg 391 then s.realMem (2*i) else 0 := by
  let a := runCode params input firstCode s
  obtain ⟨c1,b,h1,bc1,hv1⟩ := IndexGeneration.power_execution params input a
  rcases power_frames params input a b c1 h1 with ⟨bm,bn,bf⟩
  have bpow : b.natReg 132=2^s.natReg 390 := by simpa [a,firstCode,runCode,step] using hv1
  let d := runCode params input secondCode b
  obtain ⟨c2,e,h2,bc2,hv2⟩ := IndexGeneration.power_execution params input d
  rcases power_frames params input d e c2 h2 with ⟨em,en,ef⟩
  have epow : e.natReg 132=2^s.natReg 391 := by
    simpa [d,secondCode,runCode,step,bf 391 (by decide),bf 130 (by decide),a,firstCode] using hv2
  let q := runCode params input lookupCode e
  have qkey : q.natReg 380=2^s.natReg 390+2^s.natReg 391 := by
    simp [q,lookupCode,runCode,step,epow,ef 395 (by decide),d,secondCode,bpow]
  have qlen : q.natReg 381=s.natReg 501 := by
    simp [q,lookupCode,runCode,step,ef 501 (by decide),d,secondCode,
      bf 501 (by decide),a,firstCode]
  have qm : q.realMem=s.realMem := by simp [q,lookupCode,runCode,step,em,d,secondCode,bm,a,firstCode]
  have qn : q.natMem=s.natMem := by simp [q,lookupCode,runCode,step,en,d,secondCode,bn,a,firstCode]
  obtain ⟨x,hx,hxi⟩ := SKPhysicalLookup.execution params input q
  let t := runCode params input [.rcopy 390 380] x
  refine ⟨3+(c1+(4+(c2+(6+((34*q.natReg 381+9)+2))))),t,?_,?_,?_⟩
  · exact Exec.seq (exec_code params input firstCode s) (Exec.seq h1
      (Exec.seq (exec_code params input secondCode b) (Exec.seq h2
        (Exec.seq (exec_code params input lookupCode e) (Exec.seq hx
          (exec_code params input [.rcopy 390 380] x))))))
  · have hc1 : c1≤9*s.natReg 390+6 := by simpa [a,firstCode,runCode,step] using bc1
    have hc2 : c2≤9*s.natReg 391+6 := by
      simpa [d,secondCode,runCode,step,bf 391 (by decide),a,firstCode] using bc2
    rw [qlen]
    omega
  · simpa [t,runCode,step,SKPhysicalLookup.value,qlen,qkey,qm,qn] using hxi.1

theorem execution (params : Parameters) (input : Inputs) (s : State)
    (hu : s.natReg 390≤s.natReg 500) (hv : s.natReg 391≤s.natReg 500) :
    ∃c t,Exec params input program s c t ∧
      c≤18*s.natReg 500+34*s.natReg 501+58 ∧ t.realReg 390=value s ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let a := runCode params input checkCode s
  have hpre := exec_code params input checkCode s
  have hcost : codeCost checkCode=16 := by simp [checkCode,codeCost,instrCost]
  rw [hcost] at hpre
  have frames (c : ℕ) (t : State) (he : Exec params input program s c t) :
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
    constructor
    · apply he.realMem_frame
      simp [program,checkCode,physical,firstCode,secondCode,lookupCode,
        IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
        SKPhysicalLookup.program,SKPhysicalLookup.initCode,SKPhysicalLookup.bodyCode,
        code,Program.All,Instruction.writesRealMemory]
    · apply he.natMem_frame
      simp [program,checkCode,physical,firstCode,secondCode,lookupCode,
        IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
        SKPhysicalLookup.program,SKPhysicalLookup.initCode,SKPhysicalLookup.bodyCode,
        code,Program.All,Instruction.writesNatMemory]
  by_cases hg : s.natReg 390=s.natReg 500 ∨ s.natReg 391=s.natReg 500
  · let t := runCode params input [.rcopy 390 504] a
    have hflag : a.natReg 393≠0 := by
      rcases hg with h|h <;> simp [a,checkCode,runCode,step,h]
    have he : Exec params input program s (16+(2+3)) t :=
      Exec.seq hpre (Exec.branchNonzero hflag (exec_code params input [.rcopy 390 504] a))
    exact ⟨_,t,he,by omega,by simp [t,a,checkCode,runCode,step,value,hg],frames _ t he⟩
  · have hflag : a.natReg 393=0 := by simp [a,checkCode,runCode,step,not_or.mp hg]
    by_cases heq : s.natReg 390=s.natReg 391
    · let t := runCode params input [.rconst 390 0] a
      have hnonzero : a.natReg 392≠0 := by simp [a,checkCode,runCode,step,heq]
      have he : Exec params input program s (16+((1+3)+3)) t :=
        Exec.seq hpre (Exec.branchZero hflag (Exec.branchNonzero hnonzero
          (exec_code params input [.rconst 390 0] a)))
      exact ⟨_,t,he,by omega,by simp [t,a,checkCode,runCode,step,value,heq,(not_or.mp hg).2],frames _ t he⟩
    · have hzero : a.natReg 392=0 := by simp [a,checkCode,runCode,step,heq]
      obtain ⟨c,t,he,hb,hv'⟩ := physical_execution params input a
      have hrun : Exec params input program s (16+((c+3)+3)) t :=
        Exec.seq hpre (Exec.branchZero hflag (Exec.branchZero hzero he))
      refine ⟨_,t,hrun,?_,?_,frames _ t hrun⟩
      · simp [a,checkCode,runCode,step] at hb
        omega
      · simpa [value,heq,hg,a,checkCode,runCode,step] using hv'


theorem natReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (he : Exec params input program s c t) (hr : 396≤r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [program,checkCode,physical,firstCode,secondCode,lookupCode,
      IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
      SKPhysicalLookup.program,SKPhysicalLookup.initCode,SKPhysicalLookup.bodyCode,
      code,Program.All,Instruction.natDestination]
  omega

theorem realReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (he : Exec params input program s c t) (hr : 391≤r) : t.realReg r=s.realReg r := by
  apply he.realReg_frame
  simp [program,checkCode,physical,firstCode,secondCode,lookupCode,
      IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
      SKPhysicalLookup.program,SKPhysicalLookup.initCode,SKPhysicalLookup.bodyCode,
      code,Program.All,Instruction.realDestination]
  omega

end Manuscript.SKPhysicalPair
