import Manuscript.SKCandidateSource
import Manuscript.SKRestrictedCandidateExecution
import Manuscript.SKGeneratedExecution

/-! Raw color words and the prepared physical input are sufficient for one
complete candidate execution. This module composes source preparation with
all cache, primitive, algebra, and extraction instructions. -/
noncomputable section
namespace Manuscript.SKRawCandidate
open RestrictedMachine RestrictedMaskBridge SKGeneratedLabels SpinGlass

def program : Program := .seq SKCandidateSource.program SKRestrictedCandidateExecution.program

def operationBound {N : ℕ} (s : State) (A : Finset (Fin N)) :=
  SKCandidateSource.operationBound s A+SKRestrictedCandidateExecution.operationBound (SKCandidateSource.layout s A)

def vertexColor {N : ℕ} (s : State) (input : Inputs) (hL : 0<s.natReg 512)
    (v : Fin N) : Fin (2*s.natReg 512) :=
  ⟨input.nat (s.natReg 522+v.val)%(2*s.natReg 512),Nat.mod_lt _ (by omega)⟩

def augmentedColor {N : ℕ} (s : State) (input : Inputs) (hL : 0<s.natReg 512) :
    Option (Fin N)→Fin (2*s.natReg 512)
  | some v => vertexColor s input hL v
  | none => ⟨0,by omega⟩

theorem raw_trial_eq {N : ℕ} (s : State) (input : Inputs) (A : Finset (Fin N))
    (hL : 0<s.natReg 512) (h : ℝ) (w : Finset (Fin N)→ℝ) :
    (SKChargedTrialExecution.trial (fun i=>if branch A i=none then 0 else 1)
      (branch A) (outside A) (SKCandidateSource.rawColor s input A hL)
      (SKAugmentFinset.edgeWeight h w) (s.natReg 512) (SKExtractionCell.accepted (ghost A))).value=
      (SKGeneratedExecution.trial (s.natReg 512) A (vertexColor s input hL) (Real.tanh h) w).value := by
  have hc : SKCandidateSource.rawColor s input A hL=augmentedColor s input hL ∘ outside A := rfl
  rw [hc,canonical_trial]
  have ho : augmentedColor s input hL ∘
      (Subtype.val : SKActualEvaluator.Outside (SKGhostAdmissible.distinguished A)→Option (Fin N))=
      SKGhostAdmissible.outsideColor A (vertexColor s input hL) := by
    funext v
    rcases v with ⟨v,hv⟩
    cases v with
    | none => exact False.elim (hv (SKGhostAdmissible.none_mem_distinguished A))
    | some v => rfl
  rw [ho]
  rfl

theorem program_exec {N M : ℕ} (params : Parameters) (input : Inputs)
    (order : Fin M≃Model.Edge N {2}) (aCoeff : ℕ→ℝ) (beta h : ℝ)
    (J : Model.Edge N {2}→ℝ) (s : State) (A : Finset (Fin N))
    (hL : 0<s.natReg 512) (hA : s.natReg 520=encode A)
    (hphysical : SKCandidateSource.PhysicalData order aCoeff beta h J s)
    (hmaskFit : M≤s.natReg 530) (hlayout : RestrictedCandidateLabelPreparation.Layout s) :
    ∃count t,Exec params input program s count t ∧ count≤operationBound s A ∧
      t.realReg 310=(SKGeneratedExecution.trial (s.natReg 512) A (vertexColor s input hL)
        (Real.tanh h) (SKGhostCoefficient.inputWeight N aCoeff beta J)).value ∧
      (∀address,address<s.natReg 530 → t.natMem address=s.natMem address) ∧
      (∀address,address<2*s.natReg 501 → t.realMem address=s.realMem address) ∧
      (∀r,500≤r → r<540 ∨ 550≤r → t.natReg r=s.natReg r) ∧
      (∀r,500≤r → t.realReg r=s.realReg r) := by
  obtain ⟨c1,a,he1,bc1,ha⟩ := SKCandidateSource.program_exec params input order aCoeff beta h J s A hL hA hphysical hmaskFit hlayout
  obtain ⟨c2,t,he2,bc2,hv,hm,hn,hrn,hrr⟩ := SKRestrictedCandidateExecution.program_exec params input
    (SKCandidateSource.layout s A) (by change 1≤2*s.natReg 512;omega)
    (fun i=>if branch A i=none then 0 else 1) (branch A) (outside A)
    (SKCandidateSource.rawColor s input A hL)
    (SKAugmentFinset.edgeWeight h (SKGhostCoefficient.inputWeight N aCoeff beta J)) a
    ha.roots ha.shape ha.charges ha.direct
  refine ⟨c1+c2,t,Exec.seq he1 he2,by dsimp [operationBound];omega,?_,?_,?_,?_,?_⟩
  · exact hv.trans (raw_trial_eq s input A hL h _)
  · intro address haddress
    rw [hn]
    · exact ha.physicalNat address haddress
    · change address<s.natReg 533+s.natReg 500+1
      have h1 := hlayout.branch_before
      have h2 := hlayout.outside_before
      have h3 := hlayout.charge_before
      omega
  · intro address haddress
    rw [hm]
    · exact ha.physicalReal address haddress
    · change address<2*s.natReg 501+outsideCount A*outsideCount A+
        branchCount A*outsideCount A+branchCount A*branchCount A
      omega
  · intro r hr hw;exact (hrn r hr).trans (ha.natFrame r hr hw)
  · intro r hr;exact (hrr r hr).trans (ha.realFrame r hr)

theorem vertexColor_encoded {N M L R : ℕ} (order : Fin M≃Model.Edge N {2})
    (beta h epsilon delta : ℝ) (J : Model.Edge N {2}→ℝ)
    (χ : SKColorEstimator.Colors (Fin N) L R) (A : Finset (Fin N)) (r : Fin R)
    (s : State) (hL : 0<s.natReg 512) (hret : s.natReg 512=L)
    (hptr : s.natReg 522=2*M+2+(encode A*R+r.val)*N) (v : Fin N) :
    (vertexColor s (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ)) hL v).val=
      (χ A r v).val := by
  unfold vertexColor
  dsimp only
  rw [hptr,hret]
  exact SKRawColorTape.input_color (by have := v.isLt;omega) (by have := r.isLt;omega)
    order beta h epsilon delta J χ A r v

/-- With the standard serialization of the random tape, the actual machine
returns exactly the preexisting generated trial for the specified candidate
and repetition. The theorem assumes no value or MSE equality. -/
theorem encoded_program_exec {N M L R : ℕ} (params : Parameters)
    (order : Fin M≃Model.Edge N {2}) (aCoeff : ℕ→ℝ) (beta h epsilon delta : ℝ)
    (J : Model.Edge N {2}→ℝ) (χ : SKColorEstimator.Colors (Fin N) L R)
    (s : State) (A : Finset (Fin N)) (r : Fin R)
    (hL : 0<L) (hret : s.natReg 512=L) (hA : s.natReg 520=encode A)
    (hptr : s.natReg 522=2*M+2+(encode A*R+r.val)*N)
    (hphysical : SKCandidateSource.PhysicalData order aCoeff beta h J s)
    (hmaskFit : M≤s.natReg 530) (hlayout : RestrictedCandidateLabelPreparation.Layout s) :
    ∃count t,Exec params (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
      program s count t ∧ count≤operationBound s A ∧
      t.realReg 310=(SKGeneratedExecution.trial L A (χ A r) (Real.tanh h)
        (SKGhostCoefficient.inputWeight N aCoeff beta J)).value ∧
      (∀address,address<s.natReg 530 → t.natMem address=s.natMem address) ∧
      (∀address,address<2*s.natReg 501 → t.realMem address=s.realMem address) ∧
      (∀r,500≤r → r<540 ∨ 550≤r → t.natReg r=s.natReg r) ∧
      (∀r,500≤r → t.realReg r=s.realReg r) := by
  subst L
  obtain ⟨c,t,he,bc,hv,hn,hm,hrn,hrr⟩ := program_exec params _ order aCoeff beta h J s A hL hA hphysical hmaskFit hlayout
  refine ⟨c,t,he,bc,?_,hn,hm,hrn,hrr⟩
  rw [hv]
  have hc : vertexColor s (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ)) hL=χ A r := by
    funext v
    apply Fin.ext
    exact vertexColor_encoded order beta h epsilon delta J χ A r s hL rfl hptr v
  rw [hc]
end Manuscript.SKRawCandidate
