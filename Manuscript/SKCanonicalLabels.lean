import Manuscript.SKTrialReindex
import Manuscript.SKRestrictedExtraction
import Manuscript.SKChargedPrimitiveCounts

noncomputable section
namespace Manuscript.SKCanonicalLabels
open SpinGlass SKActualEvaluator

def branchEquiv {V : Type*} [DecidableEq V] {b : ℕ} (B : Finset V)
    (lab : Fin b → V) (hi : Function.Injective lab)
    (hr : ∀ v, v∈B ↔ ∃ i, lab i=v) : Fin b ≃ Fin B.card :=
  (Equiv.ofBijective (fun i => (⟨lab i,(hr _).mpr ⟨i,rfl⟩⟩ : B))
    ⟨fun i j h => hi (congrArg Subtype.val h),by
      intro v
      obtain ⟨i,hh⟩ := (hr v.val).mp v.property
      exact ⟨i,Subtype.ext hh⟩⟩).trans B.equivFin

theorem branchEquiv_value {V : Type*} [Fintype V] [DecidableEq V] {b : ℕ} (B : Finset V)
    (lab : Fin b → V) (hi : Function.Injective lab)
    (hr : ∀ v, v∈B ↔ ∃ i, lab i=v) (i : Fin b) :
    branch B (branchEquiv B lab hi hr i)=lab i := by
  simp [branch,branchEquiv,Equiv.ofBijective_apply]

def outsideEquiv {V W : Type*} [DecidableEq V] (B : Finset V)
    (lab : W → V) (hi : Function.Injective lab)
    (hr : ∀ v, v∉B ↔ ∃ i, lab i=v) : W ≃ Outside B :=
  Equiv.ofBijective (fun i => (⟨lab i,(hr _).mpr ⟨i,rfl⟩⟩ : Outside B))
    ⟨fun i j h => hi (congrArg Subtype.val h),by
      intro v
      obtain ⟨i,hh⟩ := (hr v.val).mp v.property
      exact ⟨i,Subtype.ext hh⟩⟩

theorem outsideEquiv_value {V W : Type*} [DecidableEq V] (B : Finset V)
    (lab : W → V) (hi : Function.Injective lab)
    (hr : ∀ v, v∉B ↔ ∃ i, lab i=v) (i : W) :
    (outsideEquiv B lab hi hr i).val=lab i := rfl

theorem canonical_trial {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {b K : ℕ} (A : Finset V)
    (lab : Fin b → Option V) (out : W → Option V)
    (hb : Function.Injective lab) (ho : Function.Injective out)
    (hbr : ∀ v, v∈SKGhostAdmissible.distinguished A ↔ ∃ i, lab i=v)
    (hor : ∀ v, v∉SKGhostAdmissible.distinguished A ↔ ∃ i, out i=v)
    (g : Fin b) (hg : lab g=none) (ψ : Option V → Fin K)
    (f : Finset (Option V) → ℝ) (L : ℕ) :
    (SKChargedTrialExecution.trial (fun i => if lab i=none then 0 else 1)
      lab out (ψ ∘ out) f L (SKExtractionCell.accepted g)).value=
    (SKChargedTrialExecution.trial
      (SKChargedPrimitiveCounts.endpointCharge (SKGhostAdmissible.distinguished A))
      (branch (SKGhostAdmissible.distinguished A))
      (Subtype.val : Outside (SKGhostAdmissible.distinguished A) → Option V)
      (ψ ∘ Subtype.val) f L (SKGhostAdmissible.accepted A)).value := by
  let B := SKGhostAdmissible.distinguished A
  let eb := branchEquiv B lab hb hbr
  let eo := outsideEquiv B out ho hor
  have hbv : branch B ∘ eb=lab := funext (branchEquiv_value B lab hb hbr)
  have hov : (Subtype.val : Outside B → Option V) ∘ eo=out := rfl
  have hq : SKChargedPrimitiveCounts.endpointCharge B ∘ eb=
      (fun i => if lab i=none then 0 else 1) := by
    funext i
    simp only [Function.comp_apply,SKChargedPrimitiveCounts.endpointCharge]
    rw [branchEquiv_value]
  have hghost : branch B (eb g)=none := (congrFun hbv g).trans hg
  have hacc := SKRestrictedExtraction.accepted_eq A (eb g) hghost
  have hsep : ∀ a, branch B a ∉ Set.range (Subtype.val : Outside B → Option V) := by
    intro a h
    obtain ⟨v,hv⟩ := h
    exact v.property (hv ▸ branch_mem B a)
  have hout := SKTrialReindex.trial_outside eo
    (SKChargedPrimitiveCounts.endpointCharge B ∘ eb) (branch B ∘ eb)
    (Subtype.val : Outside B → Option V) (ψ ∘ Subtype.val) f L
    (SKExtractionCell.accepted g)
  have hbranch := SKTrialReindex.trial_branch eb g
    (SKChargedPrimitiveCounts.endpointCharge B) (branch B) Subtype.val
    (branch_injective B) (outside_injective B) hsep (ψ ∘ Subtype.val) f L
  rw [hacc] at hbranch
  simpa only [hq,hbv,hov,Function.comp_assoc] using hout.trans hbranch

end Manuscript.SKCanonicalLabels
