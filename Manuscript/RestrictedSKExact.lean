import Manuscript.RestrictedSKStart
import Manuscript.RestrictedHigherEndpoint

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSKExact
open RestrictedMachine RestrictedLocalSum RestrictedLayerSemantics Model InputPreparation

def setup : List Instruction :=
  [.ncopy 282 500,.ncopy 283 501,.nconst 284 0,.nconst 285 0,
   .ncopy 310 500,.ncopy 312 501,.rcopy 250 505,.rcopy 251 506]
def program : RestrictedRecursiveMachine.Program 2 :=
  .seq (.base (code setup)) (.seq RestrictedSupportProgram.program (.base (.atom (.rcopy 572 330))))

theorem program_exec {N M : ℕ} (params : Parameters) (input : Inputs)
    (order : Fin M≃Edge N {2}) (a : ℕ→ℝ) (beta h : ℝ) (J : Edge N {2}→ℝ)
    (s : State) (hs : SKCandidateSource.PhysicalData order a beta h J s)
    (hp : s.realReg 505=FieldExpansion.spinWeight h false)
    (hm : s.realReg 506=FieldExpansion.spinWeight h true) :
    ∃ count t,RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table params input program s count t ∧
      t.realReg 572=(SupportExecution.supportSum Subtype.val Finset.univ
        (FieldExpansion.spinWeight h) (fun e=>Real.tanh (coefficient N {2} a beta J e)) N).value ∧
      count≤(59*N+26+(66*N+56)*M+300*(N+1)+400)*
        (∑j∈Finset.range (N+1),N.choose j*2^j)+28 ∧
      t.realReg 600=s.realReg 600 := by
  let ready := runCode params input setup s
  let d := RestrictedHigherEndpoint.physicalData N M h s
  have hd : core (data ready)=core d := by
    simp [ready,setup,runCode,step,data,core,d,RestrictedHigherEndpoint.physicalData,hs.size,hs.count,hp,hm]
  have hkr : ready.natReg 310=N := by simp [ready,setup,runCode,step,hs.size]
  have hspace : ready.natReg 284+ready.natReg 283≤ready.natReg 312 := by
    simp [ready,setup,runCode,step]
  obtain ⟨result,he,hv,hdata,hn,hr⟩ := RestrictedSupportProgram.program_realized params input ready hspace
  rw [hd,hkr,RestrictedSupportExecution.totalCost_core] at he
  rw [hd,hkr,RestrictedSupportExecution.totalValue_core] at hv
  have de : ∀j:Fin M,d.natMemory (d.edgeBase+j.val)=RestrictedMaskBridge.encode (order j).val := by
    simpa [d,RestrictedHigherEndpoint.physicalData] using hs.edges
  have dw : ∀j:Fin M,d.realMemory (d.weightBase+2*j.val)=Real.tanh (coefficient N {2} a beta J (order j)) := by
    simpa [d,RestrictedHigherEndpoint.physicalData] using hs.weights
  let t := step params input (.rcopy 572 330) result
  refine ⟨14+(RestrictedSupportProgram.totalCost d N 0 (N+1)+12+2),t,?_,?_,?_,?_⟩
  · have hh := RestrictedRecursiveMachine.Exec.seq
      (RestrictedRecursiveMachine.Exec.base (exec_code params input setup s))
      (RestrictedRecursiveMachine.Exec.seq he (RestrictedRecursiveMachine.Exec.base (Exec.atom (.rcopy 572 330) result)))
    simpa only [program,setup,codeCost,instrCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hh
  · change result.realReg 330=_
    rw [hv]
    exact RestrictedSupportBridge.support_value d order Subtype.val
      (fun e=>Real.tanh (coefficient N {2} a beta J e)) h de dw rfl rfl N le_rfl
  · have hc := RestrictedSupportCost.total_bound d (show N≤d.N from le_rfl)
    dsimp [RestrictedSupportCost.factor,termCost,d,RestrictedHigherEndpoint.physicalData] at hc ⊢
    omega
  · change result.realReg 600=_
    rw [hr 600 (by omega)]
    simp [ready,setup,runCode,step]

end Manuscript.RestrictedSKExact
