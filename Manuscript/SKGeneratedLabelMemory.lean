import Manuscript.SKGeneratedLabels

noncomputable section
namespace Manuscript.SKGeneratedLabels
open RestrictedMachine RestrictedMaskBridge

theorem branch_encoded {N : ℕ} (A : Finset (Fin N)) (s : State)
    (hN : s.natReg 500=N) (hA : s.natReg 520=encode A) :
    RestrictedCandidateLabels.branch s=(selectedVertices A).map Fin.val := by
  simpa only [RestrictedCandidateLabels.branch,hN,hA] using RestrictedCandidateLabels.branch_encoded A

theorem outside_encoded {N : ℕ} (A : Finset (Fin N)) (s : State)
    (hN : s.natReg 500=N) (hA : s.natReg 520=encode A) :
    RestrictedCandidateLabels.outside s=(selectedVertices Aᶜ).map Fin.val := by
  simpa only [RestrictedCandidateLabels.outside,hN,hA] using RestrictedCandidateLabels.outside_encoded A

structure LabelMemory {N : ℕ} (A : Finset (Fin N)) (input : Inputs) (s t : State) : Prop where
  branches : t.natReg 230=branchCount A
  outsideCount : t.natReg 200=SKGeneratedLabels.outsideCount A
  branchRead : ∀i:Fin (branchCount A),t.natMem (s.natReg 530+i.val)=branchNat A i
  outsideRead : ∀i:Fin (SKGeneratedLabels.outsideCount A),
    t.natMem (s.natReg 531+i.val)=(outsideVertex A i).val
  chargeRead : ∀i:Fin (branchCount A),
    t.natMem (s.natReg 532+i.val)=(if branch A i=none then 0 else 1)
  colorRead : ∀i:Fin (SKGeneratedLabels.outsideCount A),
    t.natMem (s.natReg 533+i.val)=input.nat (s.natReg 522+(outsideVertex A i).val)%s.natReg 201

theorem label_memory {N : ℕ} (A : Finset (Fin N)) (input : Inputs) (s t : State)
    (hN : s.natReg 500=N) (hA : s.natReg 520=encode A)
    (h : RestrictedCandidateLabelPreparation.Ready input s t) : LabelMemory A input s t := by
  have hb := branch_encoded A s hN hA
  have hu := outside_encoded A s hN hA
  have hbl : (RestrictedCandidateLabels.branch s).length=(selectedVertices A).length := by rw [hb,List.length_map]
  have hul : (RestrictedCandidateLabels.outside s).length=(selectedVertices Aᶜ).length := by rw [hu,List.length_map]
  refine ⟨by rw [h.branch_count,hbl];rfl,by rw [h.outside_count,hul];rfl,?_,?_,?_,?_⟩
  · intro i
    by_cases hi:i.val<(selectedVertices A).length
    · have hh := h.branch_labels i.val (by omega)
      simpa [hb,branchNat,hi] using hh
    · have hie : i.val=(selectedVertices A).length := by have:=i.isLt;unfold branchCount at this;omega
      rw [hie,←hbl,h.ghost_label,hN]
      simp only [branchNat,hi,↓reduceDIte]
  · intro i
    have hh := h.outside_labels i.val (by have:=i.isLt;unfold outsideCount at this;omega)
    simpa [hu,outsideVertex] using hh
  · intro i
    by_cases hi:i.val<(selectedVertices A).length
    · rw [h.physical_charge i.val (by omega)]
      simp [branch,hi]
    · have hie : i.val=(selectedVertices A).length := by have:=i.isLt;unfold branchCount at this;omega
      rw [hie,←hbl,h.ghost_charge]
      simp [branch,hi]
  · intro i
    have hh := h.colors i.val (by have:=i.isLt;unfold outsideCount at this;omega)
    simpa [hu,outsideVertex] using hh

end Manuscript.SKGeneratedLabels
