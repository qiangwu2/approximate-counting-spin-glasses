import Manuscript.RestrictedCandidateLabelPreparation
import Manuscript.SKPhysicalPairCanonical
import Manuscript.SKCanonicalLabels
import Manuscript.SKRawColorTape

noncomputable section
namespace Manuscript.SKGeneratedLabels
open RestrictedMachine RestrictedMaskBridge SpinGlass

def branchCount {N : ℕ} (A : Finset (Fin N)) := (selectedVertices A).length+1
def outsideCount {N : ℕ} (A : Finset (Fin N)) := (selectedVertices Aᶜ).length

def branch {N : ℕ} (A : Finset (Fin N)) (i : Fin (branchCount A)) : Option (Fin N) :=
  if hi:i.val<(selectedVertices A).length then some (selectedVertices A)[i.val] else none

def outsideVertex {N : ℕ} (A : Finset (Fin N)) (i : Fin (outsideCount A)) : Fin N :=
  (selectedVertices Aᶜ)[i.val]
def outside {N : ℕ} (A : Finset (Fin N)) (i : Fin (outsideCount A)) : Option (Fin N) :=
  some (outsideVertex A i)
def ghost {N : ℕ} (A : Finset (Fin N)) : Fin (branchCount A) :=
  ⟨(selectedVertices A).length,by simp [branchCount]⟩

def branchNat {N : ℕ} (A : Finset (Fin N)) (i : Fin (branchCount A)) : ℕ :=
  if hi:i.val<(selectedVertices A).length then (selectedVertices A)[i.val].val else N

@[simp] theorem branch_ghost {N : ℕ} (A : Finset (Fin N)) : branch A (ghost A)=none := by
  simp [branch,ghost]

theorem branchNat_le {N : ℕ} (A : Finset (Fin N)) (i : Fin (branchCount A)) : branchNat A i≤N := by
  unfold branchNat
  split
  · exact Nat.le_of_lt (selectedVertices A)[i.val].isLt
  · rfl

theorem decode_branch {N : ℕ} (A : Finset (Fin N)) (i : Fin (branchCount A)) :
    SKPhysicalPairCanonical.vertex N (branchNat A i)=branch A i := by
  unfold branchNat branch
  split
  · simp [SKPhysicalPairCanonical.vertex,(selectedVertices A)[i.val].isLt]
  · simp [SKPhysicalPairCanonical.vertex]

@[simp] theorem decode_outside {N : ℕ} (A : Finset (Fin N)) (i : Fin (outsideCount A)) :
    SKPhysicalPairCanonical.vertex N (outsideVertex A i).val=outside A i := by
  simp [SKPhysicalPairCanonical.vertex,outside]

theorem branch_injective {N : ℕ} (A : Finset (Fin N)) : Function.Injective (branch A) := by
  intro i j h
  unfold branch at h
  split at h <;> split at h
  · apply Fin.ext
    exact (selectedVertices_nodup A).getElem_inj_iff.mp (Option.some.inj h)
  · cases h
  · cases h
  · apply Fin.ext
    have hi:=i.isLt
    have hj:=j.isLt
    simp only [branchCount] at hi hj
    omega

theorem outside_injective {N : ℕ} (A : Finset (Fin N)) : Function.Injective (outside A) := by
  intro i j h
  apply Fin.ext
  exact (selectedVertices_nodup Aᶜ).getElem_inj_iff.mp (Option.some.inj h)

theorem branch_range {N : ℕ} (A : Finset (Fin N)) (v : Option (Fin N)) :
    v∈SKGhostAdmissible.distinguished A ↔ ∃i,branch A i=v := by
  cases v with
  | none => simp only [SKGhostAdmissible.none_mem_distinguished,true_iff];exact ⟨ghost A,branch_ghost A⟩
  | some v =>
    rw [SKGhostAdmissible.some_mem_distinguished]
    constructor
    · intro hv
      have hm : v∈selectedVertices A := by simpa only [←List.mem_toFinset,selectedVertices_toFinset] using hv
      obtain ⟨i,hi,hiv⟩ := List.mem_iff_getElem.mp hm
      refine ⟨⟨i,by simp only [branchCount];omega⟩,?_⟩
      simpa only [branch,hi,↓reduceDIte] using congrArg some hiv
    · rintro ⟨i,hi⟩
      unfold branch at hi
      split at hi
      · have hm := List.getElem_mem (l:=selectedVertices A) (n:=i.val) (by assumption)
        rw [Option.some.inj hi] at hm
        simpa only [←List.mem_toFinset,selectedVertices_toFinset] using hm
      · cases hi

theorem outside_range {N : ℕ} (A : Finset (Fin N)) (v : Option (Fin N)) :
    v∉SKGhostAdmissible.distinguished A ↔ ∃i,outside A i=v := by
  cases v with
  | none => simp [outside]
  | some v =>
    simp only [SKGhostAdmissible.some_mem_distinguished]
    constructor
    · intro hv
      have hm : v∈selectedVertices Aᶜ := by
        simpa only [←List.mem_toFinset,selectedVertices_toFinset,Finset.mem_compl] using hv
      obtain ⟨i,hi,hiv⟩ := List.mem_iff_getElem.mp hm
      exact ⟨⟨i,hi⟩,congrArg some hiv⟩
    · rintro ⟨i,hi⟩
      have hm : outsideVertex A i∈selectedVertices Aᶜ := List.getElem_mem (l:=selectedVertices Aᶜ) (n:=i.val) i.isLt
      have he : outsideVertex A i=v := Option.some.inj hi
      rw [he] at hm
      simpa only [←List.mem_toFinset,selectedVertices_toFinset,Finset.mem_compl] using hm

/-- The executable ascending order is related to the manuscript's abstract
finite enumeration by the proved relabeling theorem, with no ordering premise. -/
theorem canonical_trial {N K : ℕ} (A : Finset (Fin N)) (ψ : Option (Fin N)→Fin K)
    (f : Finset (Option (Fin N))→ℝ) (L : ℕ) :
    (SKChargedTrialExecution.trial (fun i=>if branch A i=none then 0 else 1)
      (branch A) (outside A) (ψ ∘ outside A) f L (SKExtractionCell.accepted (ghost A))).value=
    (SKChargedTrialExecution.trial
      (SKChargedPrimitiveCounts.endpointCharge (SKGhostAdmissible.distinguished A))
      (SKActualEvaluator.branch (SKGhostAdmissible.distinguished A))
      (Subtype.val : SKActualEvaluator.Outside (SKGhostAdmissible.distinguished A)→Option (Fin N))
      (ψ ∘ Subtype.val) f L (SKGhostAdmissible.accepted A)).value :=
  SKCanonicalLabels.canonical_trial A (branch A) (outside A) (branch_injective A)
    (outside_injective A) (branch_range A) (outside_range A) (ghost A) (branch_ghost A) ψ f L

end Manuscript.SKGeneratedLabels
