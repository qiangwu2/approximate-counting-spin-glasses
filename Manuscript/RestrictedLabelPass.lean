import Manuscript.RestrictedSubsets
import Manuscript.RestrictedFrames

noncomputable section
namespace Manuscript.RestrictedLabelPass
open RestrictedMachine

def selected (ones : Bool) (u : ℕ) : Prop := if ones then u%2≠0 else u%2=0

instance (ones : Bool) (u : ℕ) : Decidable (selected ones u) := by
  unfold selected
  infer_instance

def labels (ones : Bool) : ℕ→ℕ→ℕ→List ℕ
  | 0,_,_ => []
  | n+1,u,i => if selected ones u then i::labels ones n (u/2) (i+1)
    else labels ones n (u/2) (i+1)

def testCode : List Instruction := [.nmod 545 541 542]
def writeCode : List Instruction := [.nadd 546 549 548,.storeNat 546 540,.nadd 548 548 543]
def advanceCode : List Instruction := [.ndiv 541 541 542,.nadd 540 540 543]
def body (ones : Bool) : Program := .seq (code testCode)
  (.seq (.branch 545 (if ones then code writeCode else .skip) (if ones then .skip else code writeCode))
    (code advanceCode))
def initCode : List Instruction := [.ncopy 541 520,.nconst 540 0,.nconst 542 2,.nconst 543 1,.nconst 548 0]
def program (ones : Bool) : Program := .seq (code initCode) (.repeat 500 (body ones))

theorem body_exec (params : Parameters) (input : Inputs) (ones : Bool) (s : State)
    (h2 : s.natReg 542=2) (h1 : s.natReg 543=1) :
    ∃ t,Exec params input (body ones) s (15+11*(if selected ones (s.natReg 541) then 1 else 0)) t ∧
      t.natReg 540=s.natReg 540+1 ∧ t.natReg 541=s.natReg 541/2 ∧
      t.natReg 548=s.natReg 548+(if selected ones (s.natReg 541) then 1 else 0) ∧
      t.natMem=(if selected ones (s.natReg 541) then
        Function.update s.natMem (s.natReg 549+s.natReg 548) (s.natReg 540) else s.natMem) ∧
      t.natReg 549=s.natReg 549 ∧ t.natReg 542=2 ∧ t.natReg 543=1 := by
  let tested := runCode params input testCode s
  have ht : Exec params input (code testCode) s 4 tested := exec_code _ _ _ _
  have hflag : tested.natReg 545=s.natReg 541%2 := by simp [tested,testCode,runCode,step,h2]
  cases ones <;> by_cases hm : s.natReg 541%2=0
  · let mid := runCode params input writeCode tested
    let t := runCode params input advanceCode mid
    refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hb := Exec.branchZero (yes:=Program.skip) (hflag.trans hm) (exec_code params input writeCode tested)
      have hh := Exec.seq ht (Exec.seq hb (exec_code params input advanceCode mid))
      simpa [body,selected,hm,writeCode,advanceCode,codeCost,instrCost,t,mid] using hh
    all_goals simp [t,mid,tested,testCode,writeCode,advanceCode,runCode,step,h1,h2,selected,hm,writeNatMem]
  · let t := runCode params input advanceCode tested
    refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hb := Exec.branchNonzero (no:=code writeCode) (by rw [hflag];exact hm) (Exec.skip (params:=params) (input:=input) tested)
      have hh := Exec.seq ht (Exec.seq hb (exec_code params input advanceCode tested))
      simpa [body,selected,hm,advanceCode,codeCost,instrCost,t] using hh
    all_goals simp [t,tested,testCode,advanceCode,runCode,step,h1,h2,selected,hm]
  · let t := runCode params input advanceCode tested
    refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hb := Exec.branchZero (yes:=code writeCode) (hflag.trans hm) (Exec.skip (params:=params) (input:=input) tested)
      have hh := Exec.seq ht (Exec.seq hb (exec_code params input advanceCode tested))
      simpa [body,selected,hm,advanceCode,codeCost,instrCost,t] using hh
    all_goals simp [t,tested,testCode,advanceCode,runCode,step,h1,h2,selected,hm]
  · let mid := runCode params input writeCode tested
    let t := runCode params input advanceCode mid
    refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hb := Exec.branchNonzero (no:=Program.skip) (by rw [hflag];exact hm) (exec_code params input writeCode tested)
      have hh := Exec.seq ht (Exec.seq hb (exec_code params input advanceCode mid))
      simpa [body,selected,hm,writeCode,advanceCode,codeCost,instrCost,t,mid] using hh
    all_goals simp [t,mid,tested,testCode,writeCode,advanceCode,runCode,step,h1,h2,selected,hm,writeNatMem]

theorem repeats (params : Parameters) (input : Inputs) (ones : Bool) (n : ℕ) :
    ∀ s : State,s.natReg 542=2 → s.natReg 543=1 →
    ∃ t,Repeats params input (body ones) n s
        (20*n+11*(labels ones n (s.natReg 541) (s.natReg 540)).length+3) t ∧
      t.natReg 548=s.natReg 548+(labels ones n (s.natReg 541) (s.natReg 540)).length ∧
      t.natMem=RestrictedSubsets.writeList s.natMem (s.natReg 549+s.natReg 548)
        (labels ones n (s.natReg 541) (s.natReg 540)) := by
  induction n with
  | zero =>
      intro s h2 h1
      refine ⟨s,?_,?_,rfl⟩
      · simpa [labels] using Repeats.zero (params:=params) (input:=input) (body ones) s
      · simp [labels]
  | succ n ih =>
      intro s h2 h1
      obtain ⟨mid,he,hi,hu,hcount,hmem,hbase,h2',h1'⟩ := body_exec params input ones s h2 h1
      obtain ⟨t,ht,hc,hm⟩ := ih mid h2' h1'
      refine ⟨t,?_,?_,?_⟩
      · have hh := Repeats.succ he ht
        convert hh using 1
        rw [hi,hu]
        by_cases hs : selected ones (s.natReg 541) <;> simp [labels,hs] <;> omega
      · rw [hc,hcount,hi,hu]
        by_cases hs : selected ones (s.natReg 541) <;> simp [labels,hs] <;> omega
      · rw [hm,hmem,hbase,hcount,hi,hu]
        by_cases hs : selected ones (s.natReg 541) <;> simp [labels,hs,RestrictedSubsets.writeList,Nat.add_assoc]

/-- Ascending selected/complement labels are generated directly into RAM.
The pass runs once per original vertex; no subset search is hidden here. -/
theorem program_exec (params : Parameters) (input : Inputs) (ones : Bool) (s : State) :
    ∃ t,Exec params input (program ones) s
        (20*s.natReg 500+11*(labels ones (s.natReg 500) (s.natReg 520) 0).length+11) t ∧
      t.natReg 548=(labels ones (s.natReg 500) (s.natReg 520) 0).length ∧
      t.natMem=RestrictedSubsets.writeList s.natMem (s.natReg 549)
        (labels ones (s.natReg 500) (s.natReg 520) 0) := by
  let ready := runCode params input initCode s
  obtain ⟨t,ht,hc,hm⟩ := repeats params input ones (s.natReg 500) ready
    (by simp [ready,initCode,runCode,step]) (by simp [ready,initCode,runCode,step])
  have hnr : ready.natReg 500=s.natReg 500 := by simp [ready,initCode,runCode,step]
  have ht' : Repeats params input (body ones) (ready.natReg 500) ready
      (20*s.natReg 500+11*(labels ones (s.natReg 500) (ready.natReg 541) (ready.natReg 540)).length+3) t := by
    simpa [hnr] using ht
  have hh := Exec.seq (exec_code params input initCode s) (Exec.repeat ht')
  refine ⟨t,?_,?_,?_⟩
  · convert hh using 1
    · rfl
    · simp [ready,initCode,runCode,step,codeCost,instrCost]
      omega
  · simpa [ready,initCode,runCode,step] using hc
  · simpa [ready,initCode,runCode,step] using hm

theorem nat_frame {params : Parameters} {input : Inputs} {ones : Bool} {s t : State} {c r : ℕ}
    (he : Exec params input (program ones) s c t) (hr : r<540 ∨ 549≤r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  cases ones <;> simp [program,body,testCode,writeCode,advanceCode,initCode,code,Program.All,Instruction.natDestination] <;> omega

theorem real_frame {params : Parameters} {input : Inputs} {ones : Bool} {s t : State} {c : ℕ}
    (he : Exec params input (program ones) s c t) : t.realReg=s.realReg ∧ t.realMem=s.realMem := by
  constructor
  · funext r
    apply he.realReg_frame
    cases ones <;> simp [program,body,testCode,writeCode,advanceCode,initCode,code,Program.All,Instruction.realDestination]
  · apply he.realMem_frame
    cases ones <;> simp [program,body,testCode,writeCode,advanceCode,initCode,code,Program.All,Instruction.writesRealMemory]

theorem labels_length_le (ones : Bool) (n u i : ℕ) : (labels ones n u i).length≤n := by
  induction n generalizing u i with
  | zero => simp [labels]
  | succ n ih =>
      by_cases hs : selected ones u <;> simp [labels,hs]
      · exact ih _ _
      · exact (ih _ _).trans (by omega)

theorem labels_finRange (ones : Bool) (n u i : ℕ) :
    labels ones n u i=
      ((List.finRange n).filter (fun j => decide (selected ones (u/2^j.val)))).map (fun j => i+j.val) := by
  induction n generalizing u i with
  | zero => simp [labels]
  | succ n ih =>
      by_cases hs : selected ones u <;> simp [labels,hs,List.finRange_succ,List.filter_cons,List.filter_map,List.map_map,ih,
        Function.comp_def,pow_succ',Nat.div_div_eq_div_mul,Nat.mul_assoc,Nat.mul_comm,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end Manuscript.RestrictedLabelPass
