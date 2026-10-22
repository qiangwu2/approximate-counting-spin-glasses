import Manuscript.RestrictedSKExact
import Manuscript.RestrictedSKTruncated
import Manuscript.RestrictedSKFinish
import Manuscript.SKFinalLowerBound
import Manuscript.SKOuterCost
import Manuscript.SKControlDimension

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSKEndpoint
open RestrictedMachine Model InputPreparation

def saveCode : List Instruction :=
  [.nconst 579 2,.nmul 570 579 501,.nadd 570 570 579,.ncopy 576 501,.rcopy 600 510]

/-- A fixed finite program. The input-dependent choice between exact and
truncated summation is made by the previously executed controller. -/
def program (a : ℕ→ℝ) (B rho : ℝ) : RestrictedRecursiveMachine.Program 2 :=
  .seq (.base (RestrictedSKStart.program a B rho))
    (.seq (.base (code saveCode))
      (.seq (.branch 511 RestrictedSKExact.program RestrictedSKTruncated.program)
        (.base RestrictedSKFinish.program)))

theorem program_overhead {N M : ℕ} (hN : 2≤N) (a : ℕ→ℝ) (ha : a 2=1)
    {B rho beta h epsilon delta : ℝ} (hB : 0<B) (hB1 : B<1)
    (he : 0<epsilon) (he1 : epsilon<1) (hd : 0<delta) (hd1 : delta<1)
    (order : Fin M≃Edge N {2}) (χ : SKTheorem.Colors N a B rho epsilon delta)
    (J : Edge N {2}→ℝ) :
    ∃count final,RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
      (RestrictedParameters.sk a B rho)
      (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
      (program a B rho) initial count final ∧
      final.realReg 3=(SKFinal.execute N a B rho beta h epsilon delta
        (SKFinal.constant_pos a ha hB hB1) hd χ J).value ∧
      count≤20000*(N+(SKFinal.execute N a B rho beta h epsilon delta
        (SKFinal.constant_pos a ha hB hB1) hd χ J).operations+1)^6 := by
  let params:=RestrictedParameters.sk a B rho
  let raw:=RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ)
  let u:=LogApprox.mseBudget {2} a B rho epsilon delta
  let inp:=prepareInput N {2} a beta h J
  let old:=SKFinal.execute N a B rho beta h epsilon delta (SKFinal.constant_pos a ha hB hB1) hd χ J
  have hC:=SKFinal.constant_pos a ha (rho:=rho) hB hB1
  have hb : (prepareBudget (LogApprox.constant {2} a B rho) delta epsilon
      (LogApprox.exponent {2} a B)).u=u := prepareBudget_u hC hd
  obtain ⟨start,s,hs,hready,hstart⟩:=RestrictedSKStart.program_exec (by omega : 0<N) a B rho beta h epsilon delta
    order J (SKRawColorTape.encode χ)
  have hbudget : s.realReg 508=u := hready.budget.trans hb
  rw [hb] at hstart
  let ready:=runCode params raw saveCode s
  have hp : SKCandidateSource.PhysicalData order a beta h J ready := by
    constructor
    · simpa [ready,saveCode,runCode,step] using hready.physical.size
    · simpa [ready,saveCode,runCode,step] using hready.physical.count
    · simpa [ready,saveCode,runCode,step] using hready.physical.mean
    · intro j;exact hready.physical.edges j
    · intro j;exact hready.physical.weights j
  have hplus : ready.realReg 505=FieldExpansion.spinWeight h false := by
    simpa [ready,saveCode,runCode,step] using hready.plus
  have hminus : ready.realReg 506=FieldExpansion.spinWeight h true := by
    simpa [ready,saveCode,runCode,step] using hready.minus
  have hlog : ready.realReg 600=logBase N {2} a beta h J := by
    simpa [ready,saveCode,runCode,step] using hready.logBase
  have hx : ready.natReg 511=(SKControl.control N a B rho u).exact.toNat := by
    simpa [ready,saveCode,runCode,step,hbudget] using hready.exact
  have hmcard : M=Fintype.card (Edge N {2}) := by simpa using Fintype.card_congr order
  have hM : M≤old.operations := by
    rw [hmcard];exact SKFinalLowerBound.physical_count N a B rho beta h epsilon delta hC hd χ J
  have hparts:=SKFinalLowerBound.components N a B rho beta h epsilon delta hC hd χ J
  have hctl : (SKControl.control N a B rho u).operations≤old.operations := by
    change inp.operations+(SKControl.control N a B rho u).operations+
      (SKPhysicalExecution.evaluate N a B rho u χ inp).operations≤old.operations at hparts
    omega
  have hvalue : old.value=SpinGlass.logOutput (logBase N {2} a beta h J)
      (SKPhysicalExecution.evaluate N a B rho u χ inp).value :=
    SKFinalLowerBound.output_value (by omega) a B rho beta h epsilon delta hC hd χ J
  by_cases hex : SKAlgorithm.exactBranch N a B rho u
  · have hx' : ready.natReg 511≠0 := by rw [hx,SKControl.control_exact N a B rho u hex];norm_num
    obtain ⟨graph,t,ht,hv,hgraph,hframe⟩:=RestrictedSKExact.program_exec params raw order a beta h J ready hp hplus hminus
    obtain ⟨finish,z,hz,hfinish,hzval⟩:=RestrictedSKFinish.program_exec params raw t
    refine ⟨start+(13+(graph+3+finish)),z,?_,?_,?_⟩
    · have trace:=RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hs)
        (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base (exec_code params raw saveCode s))
          (RestrictedRecursiveMachine.Exec.seq
            (RestrictedRecursiveMachine.Exec.branchNonzero (no:=RestrictedSKTruncated.program) hx' ht)
            (RestrictedRecursiveMachine.Exec.base hz)))
      simpa only [program,saveCode,codeCost,instrCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using trace
    · rw [hzval,hframe,hlog,hv,hvalue,SKPhysicalExecution.evaluate_exact N a B rho u hex]
      have hf : cachedFieldWeight inp=FieldExpansion.spinWeight h := by
        funext b;exact cachedFieldWeight_value N {2} a beta h J b
      have hw : cachedWeight inp=fun e=>Real.tanh (coefficient N {2} a beta J e) := by
        funext e;exact cachedWeight_value (by omega) {2} a beta h J e
      rw [hf,hw]
    · have hweighted:=SKFinalLowerBound.exact_enumeration N a B rho beta h epsilon delta hC hd hex χ J
      apply SKRuntimeNumeric.final_exact N M old.operations (SKControl.control N a B rho u).operations
        (∑j∈Finset.range (N+1),N.choose j*2^j) _ hM hctl hweighted
      omega
  · let D:=SKAlgorithm.branchCutoff N a B rho u
    let L:=SKAlgorithm.edgeLimit a B rho u
    let R:=SKAlgorithm.trials a B rho u
    have hc:=SKControl.control_truncated N a B rho u hex
    have hx' : ready.natReg 511=0 := by rw [hx,hc.1];rfl
    have hrange:=LogApprox.budgets_range {2} a (by simp) (by simpa [ha]) (by simp)
      (rho:=rho) hB (by simpa only [MixedThreshold.betaF_sk a ha] using hB1) he he1 hd hd1
    have hu : 0<u := hrange.2.2.1
    have hu1 : u<1 := by have hh:=hrange.2.2.2;change u<1/8 at hh;linarith
    have hL : 0<L:=SKAlgorithm.edgeLimit_pos a ha hB hB1 hu hu1
    have hR : 0<R:=SKAlgorithm.trials_pos a B rho u
    have hcore : SKCandidateContract.Core order a beta h J D L R ready := by
      refine ⟨hp,?_,?_,?_,?_⟩
      · have hh:=hready.cutoff;rw [hbudget,hc.2.1] at hh
        simpa [ready,saveCode,runCode,step] using hh
      · have hh:=hready.edges;rw [hbudget,hc.2.2.1] at hh
        simpa [ready,saveCode,runCode,step] using hh
      · have hh:=hready.trials;rw [hbudget,hc.2.2.2] at hh
        simpa [ready,saveCode,runCode,step] using hh
      · simp [ready,saveCode,runCode,step,hready.physical.count]
    obtain ⟨graph,t,ht,hv,hgraph,hcore',hn,hr,hm⟩:=RestrictedSKTruncated.program_exec hL params
      order a beta h epsilon delta J χ ready hcore (by simp [ready,saveCode,runCode,step])
    obtain ⟨finish,z,hz,hfinish,hzval⟩:=RestrictedSKFinish.program_exec params raw t
    let W:=(SKGeneratedExecution.estimator D L R χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)).operations
    have hW : W≤old.operations := by
      have hh:=SKFinalLowerBound.estimator N a B rho beta h epsilon delta hC hd hex χ J
      rw [SKPhysicalExecution.preparedWeight_value (by omega)] at hh
      exact hh
    have hg : graph≤10000*(N+W+1)^6:=hgraph.trans (SKOuterCost.cost_bound
      (SKControlDimension.truncated_le N a B rho u hex) hR χ (Real.tanh h) _)
    refine ⟨start+(13+(graph+3+finish)),z,?_,?_,?_⟩
    · have trace:=RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hs)
        (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base (exec_code params raw saveCode s))
          (RestrictedRecursiveMachine.Exec.seq
            (RestrictedRecursiveMachine.Exec.branchZero (yes:=RestrictedSKExact.program) hx' ht)
            (RestrictedRecursiveMachine.Exec.base hz)))
      simpa only [program,saveCode,codeCost,instrCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using trace
    · rw [hzval,hr 600 (by omega),hlog,hv,hvalue,SKPhysicalExecution.evaluate_truncated N a B rho u hex]
      rw [SKPhysicalExecution.preparedWeight_value (by omega)]
      rfl
    · apply SKRuntimeNumeric.final_truncated N M old.operations (SKControl.control N a B rho u).operations W graph _ hM hctl hW hg
      omega

end Manuscript.RestrictedSKEndpoint
