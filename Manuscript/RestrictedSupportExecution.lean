import Manuscript.RestrictedSupportBridge
import Manuscript.RestrictedSupportCost

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSupportExecution
open RestrictedMachine RestrictedLocalSum RestrictedHigherLayer RestrictedLayerSemantics
open RestrictedMaskBridge SupportEvaluation FieldExpansion

theorem layerValue_core (d : Data) (k l : ℕ) :
    RestrictedLayerSemantics.value (core d) k l=RestrictedLayerSemantics.value d k l := by
  unfold RestrictedLayerSemantics.value
  simp only [core]
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  congr 1
  exact localValue_core d u

theorem totalValue_core (d : Data) (k i m : ℕ) :
    RestrictedSupportProgram.totalValue (core d) k i m=RestrictedSupportProgram.totalValue d k i m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp only [RestrictedSupportProgram.totalValue,layerValue_core,ih]

theorem layerCost_core (d : Data) (k l : ℕ) :
    RestrictedLayerSemantics.cost (core d) k l=RestrictedLayerSemantics.cost d k l := rfl

theorem totalCost_core (d : Data) (k i m : ℕ) :
    RestrictedSupportProgram.totalCost (core d) k i m=RestrictedSupportProgram.totalCost d k i m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih => simp only [RestrictedSupportProgram.totalCost,layerCost_core,ih]

/-- Actual finite-procedure machine execution of the complete support
algorithm. Premises describe only the physical input representation and
scratch separation; output equality and instruction count are conclusions. -/
theorem program_correct (params : Parameters) (input : Inputs) (s : State)
    {E : Type*} [Fintype E] [DecidableEq E]
    (order : Fin (s.natReg 283) ≃ E) (incidence : E→Finset (Fin (s.natReg 282)))
    (w : E→ℝ) (h : ℝ)
    (hE : ∀ e : Fin (s.natReg 283),s.natMem (s.natReg 284+e.val)=encode (incidence (order e)))
    (hW : ∀ e : Fin (s.natReg 283),s.realMem (s.natReg 285+2*e.val)=w (order e))
    (hp : s.realReg 250=spinWeight h false) (hm : s.realReg 251=spinWeight h true)
    (hk : s.natReg 310≤s.natReg 282)
    (hspace : s.natReg 284+s.natReg 283≤s.natReg 312) :
    ∃ c final, RestrictedRecursiveMachine.Exec table params input RestrictedSupportProgram.program s c final ∧
      final.realReg 330=(SupportExecution.supportSum incidence Finset.univ (spinWeight h) w (s.natReg 310)).value ∧
      c≤RestrictedSupportCost.factor (data s)*
        (∑l∈Finset.range (s.natReg 310+1),(s.natReg 282).choose l*2^l)+12 ∧
      core (data final)=core (data s) ∧
      (∀ r,340≤r → final.natReg r=s.natReg r) ∧
      (∀ r,340≤r → final.realReg r=s.realReg r) := by
  obtain ⟨final,he,hv,hd,hn,hr⟩ := RestrictedSupportProgram.program_realized params input s hspace
  rw [totalValue_core] at hv
  rw [totalCost_core] at he
  refine ⟨_,final,he,?_,?_,hd,hn,hr⟩
  · rw [hv]
    exact RestrictedSupportBridge.support_value (data s) order incidence w h hE hW hp hm _ hk
  · exact RestrictedSupportCost.total_bound (data s) hk

end Manuscript.RestrictedSupportExecution
