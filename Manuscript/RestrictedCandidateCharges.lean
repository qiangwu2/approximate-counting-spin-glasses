import Manuscript.RestrictedCandidateLabels

noncomputable section
namespace Manuscript.RestrictedCandidateCharges
open RestrictedMachine

def bodyCode : List Instruction :=
  [.nadd 546 532 540,.storeNat 546 543,.nadd 540 540 543]
def initCode : List Instruction := [.nconst 540 0,.nconst 543 1,.nsub 544 230 543]
def lastCode : List Instruction := [.nadd 546 532 540,.nconst 541 0,.storeNat 546 541]
def program : Program := .seq (code initCode) (.seq (.repeat 544 (code bodyCode)) (code lastCode))

theorem repeats (params : Parameters) (input : Inputs) (n : ℕ) :
    ∀ s : State,s.natReg 543=1 →
    ∃ t,Repeats params input (code bodyCode) n s (16*n+3) t ∧
      t.natReg 540=s.natReg 540+n ∧ t.natReg 532=s.natReg 532 ∧
      t.natMem=RestrictedSubsets.writeList s.natMem (s.natReg 532+s.natReg 540) (List.replicate n 1) := by
  induction n with
  | zero =>
      intro s h1
      refine ⟨s,?_,by simp,rfl,rfl⟩
      simpa using Repeats.zero (params:=params) (input:=input) (code bodyCode) s
  | succ n ih =>
      intro s h1
      let mid := runCode params input bodyCode s
      obtain ⟨t,ht,hi,hb,hm⟩ := ih mid (by simp [mid,bodyCode,runCode,step,writeNatMem,h1])
      refine ⟨t,?_,?_,?_,?_⟩
      · have he := Repeats.succ (exec_code params input bodyCode s) ht
        convert he using 1
        simp [bodyCode,codeCost,instrCost]
        omega
      · simpa [mid,bodyCode,runCode,step,writeNatMem,h1,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi
      · simpa [mid,bodyCode,runCode,step,writeNatMem] using hb
      · simpa [mid,bodyCode,runCode,step,writeNatMem,h1,List.replicate_succ,
          RestrictedSubsets.writeList,Nat.add_assoc] using hm

def memory (s : State) : ℕ→ℕ :=
  Function.update (RestrictedSubsets.writeList s.natMem (s.natReg 532)
    (List.replicate (s.natReg 230-1) 1)) (s.natReg 532+(s.natReg 230-1)) 0

theorem program_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ t,Exec params input program s (16*(s.natReg 230-1)+19) t ∧ t.natMem=memory s := by
  let ready := runCode params input initCode s
  obtain ⟨mid,he,hi,hb,hm⟩ := repeats params input (ready.natReg 544) ready
    (by simp [ready,initCode,runCode,step])
  let t := runCode params input lastCode mid
  refine ⟨t,?_,?_⟩
  · have hh := Exec.seq (exec_code params input initCode s)
      (Exec.seq (Exec.repeat he) (exec_code params input lastCode mid))
    convert hh using 1
    · rfl
    · simp [ready,initCode,lastCode,runCode,step,codeCost,instrCost]
      omega
  · simp [t,lastCode,runCode,step,writeNatMem,hm,hb,hi,ready,initCode,memory]

theorem nat_frame {params : Parameters} {input : Inputs} {s t : State} {c r : ℕ}
    (he : Exec params input program s c t) (hr : r<540 ∨ 549≤r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [program,bodyCode,initCode,lastCode,code,Program.All,Instruction.natDestination]
  omega

theorem real_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input program s c t) : t.realReg=s.realReg ∧ t.realMem=s.realMem := by
  constructor
  · funext r
    apply he.realReg_frame
    simp [program,bodyCode,initCode,lastCode,code,Program.All,Instruction.realDestination]
  · apply he.realMem_frame
    simp [program,bodyCode,initCode,lastCode,code,Program.All,Instruction.writesRealMemory]

theorem memory_physical (s : State) (j : ℕ) (hj : j<s.natReg 230-1) :
    memory s (s.natReg 532+j)=1 := by
  unfold memory
  rw [Function.update_of_ne (by omega)]
  rw [RestrictedSubsets.writeList_get _ _ _ _ (by simpa using hj),List.getElem_replicate]

theorem memory_ghost (s : State) : memory s (s.natReg 532+(s.natReg 230-1))=0 := by
  simp [memory]

theorem memory_below (s : State) (j : ℕ) (hj : j<s.natReg 532) : memory s j=s.natMem j := by
  unfold memory
  rw [Function.update_of_ne (by omega),RestrictedSubsets.writeList_below _ _ _ _ hj]

end Manuscript.RestrictedCandidateCharges
