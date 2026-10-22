import Manuscript.RestrictedSKGraphStart
import Manuscript.RestrictedSKEndpoint

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSKGraphEndpoint
open RestrictedMachine Model InputPreparation

def program (a : ℕ→ℝ) (B rho : ℝ) : RestrictedRecursiveMachine.Program 2 :=
  .seq (.base (RestrictedSKGraphStart.program a B rho))
    (.seq (.base (code RestrictedSKEndpoint.saveCode))
      (.branch 511 RestrictedSKExact.program RestrictedSKTruncated.program))

/-- Raw-u GraphApprox, including physical input preparation, all cutoff tests,
and the actually selected exact or truncated branch. -/
theorem program_overhead {N M : ℕ} (hN : 2≤N) (a : ℕ→ℝ) (ha : a 2=1)
    {B rho beta h u : ℝ} (hB : 0<B) (hB1 : B<1) (hu : 0<u) (hu1 : u<1)
    (order : Fin M≃Edge N {2}) (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2}→ℝ) :
    ∃count final,RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
      (RestrictedParameters.sk a B rho)
      (RestrictedInputEncoding.encode order beta h u 1 J (SKRawColorTape.encode χ))
      (program a B rho) initial count final ∧
      final.realReg 572=(SKPhysicalExecution.execute N a B rho beta h u χ J).value ∧
      count≤20000*(N+(SKPhysicalExecution.execute N a B rho beta h u χ J).operations+1)^6 := by
  let params:=RestrictedParameters.sk a B rho
  let raw:=RestrictedInputEncoding.encode order beta h u 1 J (SKRawColorTape.encode χ)
  let inp:=prepareInput N {2} a beta h J
  let old:=SKPhysicalExecution.execute N a B rho beta h u χ J
  obtain ⟨start,s,hs,hready,hstart⟩:=RestrictedSKGraphStart.program_exec (by omega : 0<N) a B rho beta h u
    order J (SKRawColorTape.encode χ)
  let ready:=runCode params raw RestrictedSKEndpoint.saveCode s
  have hp : SKCandidateSource.PhysicalData order a beta h J ready := by
    constructor
    · simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hready.physical.size
    · simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hready.physical.count
    · simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hready.physical.mean
    · intro j;exact hready.physical.edges j
    · intro j;exact hready.physical.weights j
  have hplus : ready.realReg 505=FieldExpansion.spinWeight h false := by
    simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hready.plus
  have hminus : ready.realReg 506=FieldExpansion.spinWeight h true := by
    simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hready.minus
  have hx : ready.natReg 511=(SKControl.control N a B rho u).exact.toNat := by
    simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hready.exact
  have hmcard : M=Fintype.card (Edge N {2}) := by simpa using Fintype.card_congr order
  have hparts : inp.operations+(SKControl.control N a B rho u).operations+
      (SKPhysicalExecution.evaluate N a B rho u χ inp).operations≤old.operations := by
    change _ ≤ inp.operations+(SKControl.control N a B rho u).operations+
      (SKPhysicalExecution.evaluate N a B rho u χ inp).operations+1
    omega
  have hM : M≤old.operations := by
    have hh:=prepareInput_operations N {2} a beta h J
    change inp.operations=_ at hh
    rw [←hmcard] at hh
    omega
  have hctl : (SKControl.control N a B rho u).operations≤old.operations := by omega
  by_cases hex : SKAlgorithm.exactBranch N a B rho u
  · have hx' : ready.natReg 511≠0 := by rw [hx,SKControl.control_exact N a B rho u hex];norm_num
    obtain ⟨graph,t,ht,hv,hgraph,hframe⟩:=RestrictedSKExact.program_exec params raw order a beta h J ready hp hplus hminus
    refine ⟨start+(13+(graph+3)),t,?_,?_,?_⟩
    · have trace:=RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hs)
        (RestrictedRecursiveMachine.Exec.seq
          (RestrictedRecursiveMachine.Exec.base (exec_code params raw RestrictedSKEndpoint.saveCode s))
          (RestrictedRecursiveMachine.Exec.branchNonzero (no:=RestrictedSKTruncated.program) hx' ht))
      simpa only [program,RestrictedSKEndpoint.saveCode,codeCost,instrCost,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,Nat.add_zero] using trace
    · change t.realReg 572=(SKPhysicalExecution.evaluate N a B rho u χ inp).value
      rw [hv,SKPhysicalExecution.evaluate_exact N a B rho u hex]
      have hf : cachedFieldWeight inp=FieldExpansion.spinWeight h := by
        funext b;exact cachedFieldWeight_value N {2} a beta h J b
      have hw : cachedWeight inp=fun e=>Real.tanh (coefficient N {2} a beta J e) := by
        funext e;exact cachedWeight_value (by omega) {2} a beta h J e
      rw [hf,hw]
    · rw [SKPhysicalExecution.evaluate_exact N a B rho u hex] at hparts
      have hh:=RestrictedSupportLowerBound.weighted_le_operations_square
        (Subtype.val : Edge N {2}→Finset (Fin N)) Finset.univ
        (cachedFieldWeight inp) (cachedWeight inp) (k:=N) (by simp)
      simp only [Fintype.card_fin] at hh
      have hweighted : (∑j∈Finset.range (N+1),N.choose j*2^j)≤(old.operations+1)^2 :=
        hh.trans (Nat.pow_le_pow_left (by omega) 2)
      apply SKRuntimeNumeric.final_exact N M old.operations (SKControl.control N a B rho u).operations
        (∑j∈Finset.range (N+1),N.choose j*2^j) _ hM hctl hweighted
      omega
  · let D:=SKAlgorithm.branchCutoff N a B rho u
    let L:=SKAlgorithm.edgeLimit a B rho u
    let R:=SKAlgorithm.trials a B rho u
    have hc:=SKControl.control_truncated N a B rho u hex
    have hx' : ready.natReg 511=0 := by rw [hx,hc.1];rfl
    have hL : 0<L:=SKAlgorithm.edgeLimit_pos a ha hB hB1 hu hu1
    have hR : 0<R:=SKAlgorithm.trials_pos a B rho u
    have hcore : SKCandidateContract.Core order a beta h J D L R ready := by
      refine ⟨hp,?_,?_,?_,?_⟩
      · have hh:=hready.cutoff;rw [hc.2.1] at hh
        simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hh
      · have hh:=hready.edges;rw [hc.2.2.1] at hh
        simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hh
      · have hh:=hready.trials;rw [hc.2.2.2] at hh
        simpa [ready,RestrictedSKEndpoint.saveCode,runCode,step] using hh
      · simp [ready,RestrictedSKEndpoint.saveCode,runCode,step,hready.physical.count]
    obtain ⟨graph,t,ht,hv,hgraph,hcore',hn,hr,hm⟩:=RestrictedSKTruncated.program_exec hL params
      order a beta h u 1 J χ ready hcore (by simp [ready,RestrictedSKEndpoint.saveCode,runCode,step])
    let W:=(SKGeneratedExecution.estimator D L R χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)).operations
    have hW : W≤old.operations := by
      rw [SKPhysicalExecution.evaluate_truncated N a B rho u hex] at hparts
      have hw:=SKPhysicalExecution.preparedWeight_value (by omega : 0<N) a beta h J
      change SKPhysicalExecution.preparedWeight inp=_ at hw
      rw [hw] at hparts
      have hm : inp.field.mean=Real.tanh h:=rfl
      rw [hm] at hparts
      dsimp only [W,D,L,R]
      omega
    have hg : graph≤10000*(N+W+1)^6:=hgraph.trans (SKOuterCost.cost_bound
      (SKControlDimension.truncated_le N a B rho u hex) hR χ (Real.tanh h) _)
    refine ⟨start+(13+(graph+3)),t,?_,?_,?_⟩
    · have trace:=RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hs)
        (RestrictedRecursiveMachine.Exec.seq
          (RestrictedRecursiveMachine.Exec.base (exec_code params raw RestrictedSKEndpoint.saveCode s))
          (RestrictedRecursiveMachine.Exec.branchZero (yes:=RestrictedSKExact.program) hx' ht))
      simpa only [program,RestrictedSKEndpoint.saveCode,codeCost,instrCost,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,Nat.add_zero] using trace
    · change t.realReg 572=(SKPhysicalExecution.evaluate N a B rho u χ inp).value
      rw [hv,SKPhysicalExecution.evaluate_truncated N a B rho u hex]
      rw [SKPhysicalExecution.preparedWeight_value (by omega)]
      rfl
    · apply SKRuntimeNumeric.final_truncated N M old.operations (SKControl.control N a B rho u).operations W graph _ hM hctl hW hg
      omega

end Manuscript.RestrictedSKGraphEndpoint
