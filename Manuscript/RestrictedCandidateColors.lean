import Manuscript.RestrictedCandidateCharges

noncomputable section
namespace Manuscript.RestrictedCandidateColors
open RestrictedMachine

def bodyCode : List Instruction :=
  [.nadd 547 531 540,.loadNat 548 547,.nadd 547 522 548,.readNatInput 548 547,
   .nmod 548 548 201,.nadd 546 533 540,.storeNat 546 548,.nadd 540 540 543]
def initCode : List Instruction := [.nconst 540 0,.nconst 543 1]
def program : Program := .seq (code initCode) (.repeat 200 (code bodyCode))

def values (input : Inputs) (labels : ℕ→ℕ) (tape K : ℕ) : ℕ→ℕ→List ℕ
  | 0,_ => []
  | n+1,i => input.nat (tape+labels i)%K::values input labels tape K n (i+1)

theorem body_spec (params : Parameters) (input : Inputs) (s : State) (h1 : s.natReg 543=1) :
    let t := runCode params input bodyCode s
    t.natReg 540=s.natReg 540+1 ∧
    t.natMem=Function.update s.natMem (s.natReg 533+s.natReg 540)
      (input.nat (s.natReg 522+s.natMem (s.natReg 531+s.natReg 540))%s.natReg 201) ∧
    (∀ r,r<540 ∨ 549≤r → t.natReg r=s.natReg r) ∧ t.natReg 543=1 := by
  dsimp only
  constructor
  · simp [bodyCode,runCode,step,writeNatMem,h1]
  constructor
  · simp [bodyCode,runCode,step,writeNatMem]
  constructor
  · intro r hr
    simp [bodyCode,runCode,step,writeNatMem,show r≠540 by omega,show r≠546 by omega,
      show r≠547 by omega,show r≠548 by omega]
  · simp [bodyCode,runCode,step,writeNatMem,h1]

theorem repeats (params : Parameters) (input : Inputs) (label : ℕ→ℕ) (limit : ℕ) (n : ℕ) :
    ∀ s : State,s.natReg 543=1 → s.natReg 540+n≤limit →
      s.natReg 531+limit≤s.natReg 533 →
      (∀ j,j<limit → s.natMem (s.natReg 531+j)=label j) →
    ∃ t,Repeats params input (code bodyCode) n s (34*n+3) t ∧
      t.natMem=RestrictedSubsets.writeList s.natMem (s.natReg 533+s.natReg 540)
        (values input label (s.natReg 522) (s.natReg 201) n (s.natReg 540)) := by
  induction n with
  | zero =>
      intro s h1 hlim hsep hlab
      refine ⟨s,?_,rfl⟩
      simpa using Repeats.zero (params:=params) (input:=input) (code bodyCode) s
  | succ n ih =>
      intro s h1 hlim hsep hlab
      let mid := runCode params input bodyCode s
      have hs := body_spec params input s h1
      change mid.natReg 540=_ ∧ mid.natMem=_ ∧ _ at hs
      obtain ⟨hi,hm,hn,h1'⟩ := hs
      have hread : s.natMem (s.natReg 531+s.natReg 540)=label (s.natReg 540) := hlab _ (by omega)
      have hlab' : ∀ j,j<limit → mid.natMem (mid.natReg 531+j)=label j := by
        intro j hj
        rw [hn 531 (by omega),hm,Function.update_of_ne (by omega)]
        exact hlab j hj
      obtain ⟨t,ht,hm'⟩ := ih mid h1' (by rw [hi];omega)
        (by rw [hn 531 (by omega),hn 533 (by omega)];exact hsep) hlab'
      refine ⟨t,?_,?_⟩
      · have hh := Repeats.succ (exec_code params input bodyCode s) ht
        convert hh using 1
        simp [bodyCode,codeCost,instrCost]
        omega
      · rw [hm',hm,hi,hn 533 (by omega),hn 522 (by omega),hn 201 (by omega),hread]
        simp [values,RestrictedSubsets.writeList,Nat.add_assoc]

def memory (input : Inputs) (s : State) : ℕ→ℕ :=
  RestrictedSubsets.writeList s.natMem (s.natReg 533)
    (values input (fun j=>s.natMem (s.natReg 531+j)) (s.natReg 522) (s.natReg 201) (s.natReg 200) 0)

theorem program_exec (params : Parameters) (input : Inputs) (s : State)
    (hsep : s.natReg 531+s.natReg 200≤s.natReg 533) :
    ∃ t,Exec params input program s (34*s.natReg 200+7) t ∧ t.natMem=memory input s := by
  let ready := runCode params input initCode s
  obtain ⟨t,he,hm⟩ := repeats params input (fun j=>s.natMem (s.natReg 531+j))
    (s.natReg 200) (ready.natReg 200) ready
    (by simp [ready,initCode,runCode,step]) (by simp [ready,initCode,runCode,step])
    (by simpa [ready,initCode,runCode,step] using hsep)
    (by intro j hj;simp [ready,initCode,runCode,step])
  refine ⟨t,?_,?_⟩
  · have hh := Exec.seq (exec_code params input initCode s) (Exec.repeat he)
    convert hh using 1
    · rfl
    · simp [ready,initCode,runCode,step,codeCost,instrCost]
      omega
  · simpa [ready,initCode,runCode,step,memory] using hm

theorem nat_frame {params : Parameters} {input : Inputs} {s t : State} {c r : ℕ}
    (he : Exec params input program s c t) (hr : r<540 ∨ 549≤r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [program,bodyCode,initCode,code,Program.All,Instruction.natDestination]
  omega

theorem real_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : Exec params input program s c t) : t.realReg=s.realReg ∧ t.realMem=s.realMem := by
  constructor
  · funext r
    apply he.realReg_frame
    simp [program,bodyCode,initCode,code,Program.All,Instruction.realDestination]
  · apply he.realMem_frame
    simp [program,bodyCode,initCode,code,Program.All,Instruction.writesRealMemory]

@[simp] theorem values_length (input : Inputs) (labels : ℕ→ℕ) (tape K n i : ℕ) :
    (values input labels tape K n i).length=n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [values,ih]

theorem values_get (input : Inputs) (labels : ℕ→ℕ) (tape K n i j : ℕ) (hj : j<n) :
    (values input labels tape K n i)[j]'(by simpa using hj)=input.nat (tape+labels (i+j))%K := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero => simp [values]
      | succ j => simpa [values,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) j (by omega)

theorem memory_get (input : Inputs) (s : State) (j : ℕ) (hj : j<s.natReg 200) :
    memory input s (s.natReg 533+j)=input.nat (s.natReg 522+s.natMem (s.natReg 531+j))%s.natReg 201 := by
  unfold memory
  rw [RestrictedSubsets.writeList_get _ _ _ _ (by simpa using hj),values_get]
  all_goals simp_all

theorem memory_below (input : Inputs) (s : State) (j : ℕ) (hj : j<s.natReg 533) :
    memory input s j=s.natMem j := RestrictedSubsets.writeList_below _ _ _ _ hj

end Manuscript.RestrictedCandidateColors
