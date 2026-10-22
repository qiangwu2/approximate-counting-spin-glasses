import Manuscript.SKCandidatePrimitives
import Manuscript.SKCandidateBackend

/-! End-to-end operational refinement of one colorful charged SK trial.
Every cache, basis record, primitive, direct factor, and correction is computed
by the fixed restricted program. Input hypotheses describe only source arrays. -/
noncomputable section
namespace Manuscript.SKRestrictedCandidateExecution
open RestrictedMachine SKCandidateLayout SKBasisEncoding SpinGlass SKFastEvaluator

def program : Program := .seq SKCandidatePrimitives.program SKCandidateBackend.program
def operationBound (d : Layout) := SKCandidatePrimitives.operationBound d+SKCandidateBackend.operationBound d

theorem program_exec {V : Type*} [DecidableEq V] (p : Parameters) (i : RestrictedMachine.Inputs)
    (d : Layout) (hK : 1≤d.root.K) (q : Fin d.root.B→ℕ)
    (branch : Fin d.root.B→V) (outside : Fin d.root.N→V)
    (χ : Fin d.root.N→Fin d.root.K) (f : Finset V→ℝ) (s : State)
    (hs : SKRootCache.InputsReady d.root χ
      (fun x y => pairWeight f (outside x) (outside y))
      (fun x y => pairWeight f (branch x) (outside y)) s)
    (hl : SKCandidateLayout.Inputs d s)
    (hq : ∀x,s.natMem (d.chargeBase+x.val)=q x)
    (hw : ∀a c,s.realMem (d.branchWeightBase+a.val*d.root.B+c.val)=pairWeight f (branch a) (branch c)) :
    ∃ count t, Exec p i program s count t ∧ count≤operationBound d ∧
      t.realReg 310=(SKChargedTrialExecution.trial q branch outside χ f d.retained
        (SKExtractionCell.accepted d.ghost)).value ∧
      (∀address,address<d.root.arena → t.realMem address=s.realMem address) ∧
      (∀address,address<d.metadataBase → t.natMem address=s.natMem address) ∧
      (∀r,500≤r → t.natReg r=s.natReg r) ∧ (∀r,500≤r → t.realReg r=s.realReg r) := by
  obtain ⟨c1,a,he1,bc1,ha,hp,hn,hm,han,har⟩ :=
    SKCandidatePrimitives.program_exec p i d q branch outside χ f s hs hl hq
  have hqa : ∀x,a.natMem (d.chargeBase+x.val)=q x := by intro x; rw [hn]; exact hq x
  have hwa : ∀x y,a.realMem (d.branchWeightBase+x.val*d.root.B+y.val)=pairWeight f (branch x) (branch y) := by
    intro x y
    rw [hm]
    · exact hw x y
    · have hx := x.isLt; have hy := y.isLt; have hfit := d.branchWeightFit
      nlinarith
  obtain ⟨c2,t,he2,bc2,hv,htm,htn,htnr,htrr⟩ := SKCandidateBackend.program_exec p i d hK q branch f
    (SKChargedExecution.primitives q branch outside χ f).coeff a ha hqa hwa hp
  refine ⟨c1+c2,t,Exec.seq he1 he2,by dsimp [operationBound]; omega,?_,?_,?_,?_,?_⟩
  · simpa only [SKChargedTrialExecution.trial,SKChargedAlgebraExecution.evaluator_value,
      SKChargedPrimitiveExecution.primitives_value] using hv
  · intro address haddress; exact (htm address haddress).trans (hm address haddress)
  · intro address haddress; rw [htn address haddress,hn]
  · intro r hr; exact (htnr r hr).trans (han r hr)
  · intro r hr; exact (htrr r hr).trans (har r hr)
end Manuscript.SKRestrictedCandidateExecution
