import Manuscript.RestrictedLabelPass
import Manuscript.RestrictedMaskLists

noncomputable section
namespace Manuscript.RestrictedCandidateLabels
open RestrictedMachine

def firstCode : List Instruction := [.ncopy 549 530]
def betweenCode : List Instruction := [.ncopy 230 548,.ncopy 549 531]
def lastCode : List Instruction :=
  [.ncopy 200 548,.nadd 546 530 230,.storeNat 546 500,.nconst 543 1,.nadd 230 230 543,.ncopy 204 533]
def program : Program := .seq (code firstCode)
  (.seq (RestrictedLabelPass.program true)
    (.seq (code betweenCode) (.seq (RestrictedLabelPass.program false) (code lastCode))))

def branch (s : State) : List ℕ := RestrictedLabelPass.labels true (s.natReg 500) (s.natReg 520) 0
def outside (s : State) : List ℕ := RestrictedLabelPass.labels false (s.natReg 500) (s.natReg 520) 0

def memory (s : State) : ℕ→ℕ :=
  Function.update (RestrictedSubsets.writeList
    (RestrictedSubsets.writeList s.natMem (s.natReg 530) (branch s)) (s.natReg 531) (outside s))
    (s.natReg 530+(branch s).length) (s.natReg 500)

theorem program_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ t,Exec params input program s
        (40*s.natReg 500+11*(branch s).length+11*(outside s).length+44) t ∧
      t.natReg 230=(branch s).length+1 ∧ t.natReg 200=(outside s).length ∧
      t.natReg 204=s.natReg 533 ∧ t.natMem=memory s ∧
      (∀ r,500≤r → r<540 ∨ 550≤r → t.natReg r=s.natReg r) ∧
      t.realReg=s.realReg ∧ t.realMem=s.realMem := by
  let first := runCode params input firstCode s
  obtain ⟨a,ha,ac,am⟩ := RestrictedLabelPass.program_exec params input true first
  have an (r : ℕ) (hr : r<540 ∨ 550≤r) : a.natReg r=s.natReg r := by
    rw [RestrictedLabelPass.nat_frame ha (by omega)]
    simp [first,firstCode,runCode,step,show r≠549 by omega]
  have a549 : a.natReg 549=s.natReg 530 := by
    rw [RestrictedLabelPass.nat_frame ha (by omega)]
    simp [first,firstCode,runCode,step]
  have av := RestrictedLabelPass.real_frame ha
  let between := runCode params input betweenCode a
  obtain ⟨b,hb,bc,bm⟩ := RestrictedLabelPass.program_exec params input false between
  have bn (r : ℕ) (hr : (r<540 ∧ r≠230) ∨ 550≤r) : b.natReg r=s.natReg r := by
    rw [RestrictedLabelPass.nat_frame hb (by omega)]
    simp [between,betweenCode,runCode,step,show r≠230 by omega,show r≠549 by omega,an r (by omega)]
  have b230 : b.natReg 230=(branch s).length := by
    rw [RestrictedLabelPass.nat_frame hb (by omega)]
    simpa [between,betweenCode,runCode,step,first,firstCode,branch] using ac
  have bm' : b.natMem=RestrictedSubsets.writeList
      (RestrictedSubsets.writeList s.natMem (s.natReg 530) (branch s)) (s.natReg 531) (outside s) := by
    rw [bm]
    simpa [between,betweenCode,runCode,step,am,first,firstCode,branch,outside,an] using
      (show RestrictedSubsets.writeList between.natMem (between.natReg 549)
        (RestrictedLabelPass.labels false (between.natReg 500) (between.natReg 520) 0)=
        RestrictedSubsets.writeList between.natMem (between.natReg 549)
        (RestrictedLabelPass.labels false (between.natReg 500) (between.natReg 520) 0) from rfl)
  have bc' : b.natReg 548=(outside s).length := by
    simpa [outside,between,betweenCode,runCode,step,an] using bc
  have bv := RestrictedLabelPass.real_frame hb
  let t := runCode params input lastCode b
  refine ⟨t,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := Exec.seq (exec_code params input firstCode s)
      (Exec.seq ha (Exec.seq (exec_code params input betweenCode a)
        (Exec.seq hb (exec_code params input lastCode b))))
    convert hh using 1
    · rfl
    · simp [first,firstCode,between,betweenCode,branch,outside,runCode,step,an,
        lastCode,codeCost,instrCost]
      omega
  · simp [t,lastCode,runCode,step,writeNatMem,b230]
  · simp [t,lastCode,runCode,step,writeNatMem,bc']
  · simp [t,lastCode,runCode,step,writeNatMem,bn]
  · simp [t,lastCode,runCode,step,writeNatMem,writeNatMem,bm',b230,bn,memory]
  · intro r hr haway
    simp [t,lastCode,runCode,step,writeNatMem,show r≠200 by omega,show r≠204 by omega,
      show r≠230 by omega,show r≠546 by omega,show r≠543 by omega,bn r (by omega)]
  · simpa [t,lastCode,runCode,step,writeNatMem,between,betweenCode,first,firstCode] using bv.1.trans av.1
  · simpa [t,lastCode,runCode,step,writeNatMem,between,betweenCode,first,firstCode] using bv.2.trans av.2

theorem cost_bound (s : State) :
    40*s.natReg 500+11*(branch s).length+11*(outside s).length+44≤62*s.natReg 500+44 := by
  have hb := RestrictedLabelPass.labels_length_le true (s.natReg 500) (s.natReg 520) 0
  have hu := RestrictedLabelPass.labels_length_le false (s.natReg 500) (s.natReg 520) 0
  dsimp [branch,outside]
  omega

theorem branch_encoded {N : ℕ} (B : Finset (Fin N)) :
    RestrictedLabelPass.labels true N (RestrictedMaskBridge.encode B) 0=
      (RestrictedMaskBridge.selectedVertices B).map Fin.val := by
  rw [RestrictedLabelPass.labels_finRange]
  simp only [Nat.zero_add,RestrictedMaskBridge.selectedVertices]
  congr 2
  funext v
  simp [RestrictedLabelPass.selected,RestrictedMaskBridge.encode_digit]

theorem outside_encoded {N : ℕ} (B : Finset (Fin N)) :
    RestrictedLabelPass.labels false N (RestrictedMaskBridge.encode B) 0=
      (RestrictedMaskBridge.selectedVertices Bᶜ).map Fin.val := by
  rw [RestrictedLabelPass.labels_finRange]
  simp only [Nat.zero_add,RestrictedMaskBridge.selectedVertices]
  congr 2
  funext v
  simp [RestrictedLabelPass.selected,RestrictedMaskBridge.encode_digit]


theorem memory_branch (s : State) (hsep : s.natReg 530+(branch s).length<s.natReg 531)
    (j : ℕ) (hj : j<(branch s).length) :
    memory s (s.natReg 530+j)=(branch s)[j] := by
  unfold memory
  rw [Function.update_of_ne (by omega),RestrictedSubsets.writeList_below _ _ _ _ (by omega)]
  exact RestrictedSubsets.writeList_get _ _ _ _ hj

theorem memory_ghost (s : State) :
    memory s (s.natReg 530+(branch s).length)=s.natReg 500 := by simp [memory]

theorem memory_outside (s : State) (hsep : s.natReg 530+(branch s).length<s.natReg 531)
    (j : ℕ) (hj : j<(outside s).length) :
    memory s (s.natReg 531+j)=(outside s)[j] := by
  unfold memory
  rw [Function.update_of_ne (by omega)]
  exact RestrictedSubsets.writeList_get _ _ _ _ hj

theorem memory_below (s : State) (hsep : s.natReg 530≤s.natReg 531)
    (j : ℕ) (hj : j<s.natReg 530) : memory s j=s.natMem j := by
  unfold memory
  rw [Function.update_of_ne (by omega),RestrictedSubsets.writeList_below _ _ _ _ (by omega),
    RestrictedSubsets.writeList_below _ _ _ _ hj]

end Manuscript.RestrictedCandidateLabels
