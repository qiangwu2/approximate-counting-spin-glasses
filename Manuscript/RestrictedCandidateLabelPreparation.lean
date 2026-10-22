import Manuscript.RestrictedCandidateColors

noncomputable section
namespace Manuscript.RestrictedCandidateLabelPreparation
open RestrictedMachine

structure Layout (s : State) : Prop where
  branch_before : s.natReg 530+s.natReg 500+1≤s.natReg 531
  outside_before : s.natReg 531+s.natReg 500≤s.natReg 532
  charge_before : s.natReg 532+s.natReg 500+1≤s.natReg 533

open RestrictedCandidateLabels (branch outside)

def program : Program := .seq RestrictedCandidateLabels.program
  (.seq RestrictedCandidateCharges.program RestrictedCandidateColors.program)

structure Ready (input : Inputs) (s t : State) : Prop where
  branch_count : t.natReg 230=(branch s).length+1
  outside_count : t.natReg 200=(outside s).length
  color_base : t.natReg 204=s.natReg 533
  branch_labels : ∀ j (hj : j<(branch s).length),t.natMem (s.natReg 530+j)=(branch s)[j]
  ghost_label : t.natMem (s.natReg 530+(branch s).length)=s.natReg 500
  outside_labels : ∀ j (hj : j<(outside s).length),t.natMem (s.natReg 531+j)=(outside s)[j]
  physical_charge : ∀ j,j<(branch s).length → t.natMem (s.natReg 532+j)=1
  ghost_charge : t.natMem (s.natReg 532+(branch s).length)=0
  colors : ∀ j (hj : j<(outside s).length),
    t.natMem (s.natReg 533+j)=input.nat (s.natReg 522+(outside s)[j])%s.natReg 201
  nat_below : ∀ j,j<s.natReg 530 → t.natMem j=s.natMem j
  nat_frame : ∀ r,500≤r → r<540 ∨ 550≤r → t.natReg r=s.natReg r
  real_frame : t.realReg=s.realReg
  real_memory : t.realMem=s.realMem

/-- Fixed label, charge, and color preparation from the candidate mask and the
read-only random tape. Every RAM read/write and loop dispatch is charged. -/
theorem program_exec (params : Parameters) (input : Inputs) (s : State) (layout : Layout s) :
    ∃ count t,Exec params input program s count t ∧ Ready input s t ∧ count≤112*s.natReg 500+70 := by
  have hb : (branch s).length≤s.natReg 500 := RestrictedLabelPass.labels_length_le _ _ _ _
  have hu : (outside s).length≤s.natReg 500 := RestrictedLabelPass.labels_length_le _ _ _ _
  have hsep : s.natReg 530+(branch s).length<s.natReg 531 := by have:=layout.branch_before;omega
  obtain ⟨a,ha,ab,au,ac,am,an,ar,arm⟩ := RestrictedCandidateLabels.program_exec params input s
  obtain ⟨b,he,bm⟩ := RestrictedCandidateCharges.program_exec params input a
  have bn (r : ℕ) (hr : r<540 ∨ 549≤r) : b.natReg r=a.natReg r := RestrictedCandidateCharges.nat_frame he hr
  have bav := RestrictedCandidateCharges.real_frame he
  have bsep : b.natReg 531+b.natReg 200≤b.natReg 533 := by
    rw [bn 531 (by omega),bn 200 (by omega),bn 533 (by omega),an 531 (by omega) (by omega),
      an 533 (by omega) (by omega),au]
    have:=layout.outside_before
    have:=layout.charge_before
    omega
  obtain ⟨t,ht,tm⟩ := RestrictedCandidateColors.program_exec params input b bsep
  have tn (r : ℕ) (hr : r<540 ∨ 549≤r) : t.natReg r=b.natReg r := RestrictedCandidateColors.nat_frame ht hr
  have tv := RestrictedCandidateColors.real_frame ht
  have an' (r : ℕ) (hr : 500≤r) (ha : r<540 ∨ 550≤r) : a.natReg r=s.natReg r := an r hr ha
  have bbelow (j : ℕ) (hj : j<s.natReg 532) : b.natMem j=a.natMem j := by
    rw [bm]
    exact RestrictedCandidateCharges.memory_below a j (by rw [an' 532 (by omega) (by omega)];exact hj)
  have tbelow (j : ℕ) (hj : j<s.natReg 533) : t.natMem j=b.natMem j := by
    rw [tm]
    exact RestrictedCandidateColors.memory_below input b j (by rw [bn 533 (by omega),an' 533 (by omega) (by omega)];exact hj)
  have countEq :
      40*s.natReg 500+11*(branch s).length+11*(outside s).length+44+
      (16*(a.natReg 230-1)+19+(34*b.natReg 200+7))=
      40*s.natReg 500+27*(branch s).length+45*(outside s).length+70 := by
    rw [ab,bn 200 (by omega),au]
    omega
  refine ⟨_,t,Exec.seq ha (Exec.seq he ht),?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [tn 230 (by omega),bn 230 (by omega),ab]
    · rw [tn 200 (by omega),bn 200 (by omega),au]
    · rw [tn 204 (by omega),bn 204 (by omega),ac]
    · intro j hj
      have h1:=layout.branch_before
      have h2:=layout.outside_before
      have h3:=layout.charge_before
      rw [tbelow _ (by omega),bbelow _ (by omega),am]
      exact RestrictedCandidateLabels.memory_branch s hsep j hj
    · have h1:=layout.branch_before
      have h2:=layout.outside_before
      have h3:=layout.charge_before
      rw [tbelow _ (by omega),bbelow _ (by omega),am]
      exact RestrictedCandidateLabels.memory_ghost s
    · intro j hj
      have h2:=layout.outside_before
      have h3:=layout.charge_before
      rw [tbelow _ (by omega),bbelow _ (by omega),am]
      exact RestrictedCandidateLabels.memory_outside s hsep j hj
    · intro j hj
      have h3:=layout.charge_before
      rw [tbelow _ (by omega),bm,←an' 532 (by omega) (by omega)]
      exact RestrictedCandidateCharges.memory_physical a j (by rw [ab];omega)
    · have h3:=layout.charge_before
      rw [tbelow _ (by omega),bm]
      have hh:=RestrictedCandidateCharges.memory_ghost a
      simpa [ab,an'] using hh
    · intro j hj
      rw [tm,←an' 533 (by omega) (by omega),←bn 533 (by omega),
        RestrictedCandidateColors.memory_get input b j (by rw [bn 200 (by omega),au];exact hj)]
      rw [bn 522 (by omega),bn 531 (by omega),bn 201 (by omega),
        an' 522 (by omega) (by omega),an' 531 (by omega) (by omega)]
      have h2:=layout.outside_before
      rw [bbelow _ (by omega),am,RestrictedCandidateLabels.memory_outside s hsep j hj]
      have ha201 : a.natReg 201=s.natReg 201 := by
        apply ha.natReg_frame
        simp [RestrictedCandidateLabels.program,RestrictedCandidateLabels.firstCode,
          RestrictedCandidateLabels.betweenCode,RestrictedCandidateLabels.lastCode,
          RestrictedLabelPass.program,RestrictedLabelPass.body,RestrictedLabelPass.testCode,
          RestrictedLabelPass.writeCode,RestrictedLabelPass.advanceCode,RestrictedLabelPass.initCode,
          code,Program.All,Instruction.natDestination]
      rw [ha201]
    · intro j hj
      have h1:=layout.branch_before
      have h2:=layout.outside_before
      have h3:=layout.charge_before
      rw [tbelow _ (by omega),bbelow _ (by omega),am]
      exact RestrictedCandidateLabels.memory_below s (by omega) j hj
    · intro r hr haw
      rw [tn r (by omega),bn r (by omega),an' r hr haw]
    · exact tv.1.trans (bav.1.trans ar)
    · exact tv.2.trans (bav.2.trans arm)
  · rw [countEq]
    omega


theorem palette_frame {params : Parameters} {input : Inputs} {s t : State} {count : ℕ}
    (he : Exec params input program s count t) : t.natReg 201=s.natReg 201 := by
  apply he.natReg_frame
  simp [program,RestrictedCandidateLabels.program,RestrictedCandidateLabels.firstCode,
    RestrictedCandidateLabels.betweenCode,RestrictedCandidateLabels.lastCode,
    RestrictedLabelPass.program,RestrictedLabelPass.body,RestrictedLabelPass.testCode,
    RestrictedLabelPass.writeCode,RestrictedLabelPass.advanceCode,RestrictedLabelPass.initCode,
    RestrictedCandidateCharges.program,RestrictedCandidateCharges.bodyCode,
    RestrictedCandidateCharges.initCode,RestrictedCandidateCharges.lastCode,
    RestrictedCandidateColors.program,RestrictedCandidateColors.bodyCode,RestrictedCandidateColors.initCode,
    code,Program.All,Instruction.natDestination]

end Manuscript.RestrictedCandidateLabelPreparation
