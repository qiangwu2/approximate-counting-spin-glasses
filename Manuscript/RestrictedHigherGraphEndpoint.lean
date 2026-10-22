import Manuscript.RestrictedSupportExecution
import Manuscript.RestrictedPhysicalPreparation
import Manuscript.RestrictedHigherControl
import Manuscript.HigherOrderFinal

set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedHigherGraphEndpoint
open RestrictedMachine RestrictedLocalSum RestrictedLayerSemantics
open Model InputPreparation

def setup : List Instruction :=
  [.ncopy 282 500,.ncopy 283 501,.nconst 284 0,.nconst 285 0,
   .ncopy 310 510,.ncopy 312 501,.rcopy 250 505,.rcopy 251 506]
/-- Read the requested GraphApprox accuracy from its raw input slot. -/
def accuracy : List Instruction :=
  [.nconst 550 2,.nadd 550 501 550,.readRealInput 508 550]

def program (pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ) (B rho pmin : ℝ) :
    RestrictedRecursiveMachine.Program 2 :=
  .seq (.base (RestrictedPreparation.program (RestrictedParameters.budgetBase pmax)))
    (.seq (.base (code accuracy))
      (.seq (.base (RestrictedHigherControl.program pmax P a B rho pmin))
        (.seq (.base (code setup)) RestrictedSupportProgram.program)))

def cutoff (N pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ) (B rho pmin h u : ℝ) : ℕ :=
  (HigherOrderExecution.control N pmax P a B rho pmin h u (Real.tanh h)).cutoff

private theorem floor_le (r : ℝ) (n : ℕ) : (CutoffExecution.boundedFloor r n).value≤n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [CutoffExecution.boundedFloor]; split_ifs <;> dsimp <;> omega

private theorem scan_bound (kap A : ℝ) (N : ℕ) (lam : ℝ) (fuel : ℕ) :
    ∀ start, 1≤start → (CutoffExecution.scan kap A N lam start fuel).found.getD 1≤start+fuel := by
  induction fuel with
  | zero => intro start hs; simpa [CutoffExecution.scan] using hs
  | succ fuel ih =>
      intro start hs
      simp only [CutoffExecution.scan]
      split_ifs
      · simp
      · have hh := ih (start+1) (by omega)
        dsimp only
        omega

private theorem search_bound (kapMin kap A : ℝ) (N : ℕ) (lam : ℝ) :
    (CutoffExecution.cutoffSearch kapMin kap A N lam).found.getD 1-1≤N := by
  unfold CutoffExecution.cutoffSearch
  dsimp only
  have hh := scan_bound kap A N lam (CutoffExecution.boundedFloor (Cutoffs.gamma kapMin A*N) N).value 1 (by omega)
  have hf := floor_le (Cutoffs.gamma kapMin A*N) N
  omega

theorem cutoff_le (N pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ) (B rho pmin h u : ℝ) :
    cutoff N pmax P a B rho pmin h u≤N := by
  unfold cutoff HigherOrderExecution.control
  dsimp only
  split_ifs
  · rfl
  · exact search_bound _ _ _ _ _

def physicalData (N M : ℕ) (h : ℝ) (s : State) : Data :=
  ⟨N,M,0,0,0,0,FieldExpansion.spinWeight h false,FieldExpansion.spinWeight h true,s.natMem,s.realMem⟩

/-- The GraphApprox primitive starts from zero registers and ordinary raw
coupling records. Its accuracy is the supplied raw u, with no logarithmic
budget substitution and no final logarithm. -/
theorem program_exec {N M : ℕ} (hN : 0<N) (pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ)
    (hmax : ∀ p∈P,p≤pmax) (B rho pmin beta h u : ℝ)
    (order : Fin M≃Edge N P) (J : Edge N P→ℝ) (tape : ℕ→ℕ) :
    ∃ count final,
      RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
        (RestrictedParameters.higher pmax P a B rho pmin)
        (RestrictedInputEncoding.encode order beta h u 1 J tape)
        (program pmax P a B rho pmin) initial count final ∧
      final.realReg 330=(HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).value ∧
      count≤141*M+78*N+461+
        (59*N+26+(66*N+56)*M+300*(N+1)+400)*
          (∑l∈Finset.range (cutoff N pmax P a B rho pmin h u+1),N.choose l*2^l) := by
  let params := RestrictedParameters.higher pmax P a B rho pmin
  let raw := RestrictedInputEncoding.encode order beta h u 1 J tape
  let k := cutoff N pmax P a B rho pmin h u
  obtain ⟨prep,he,hready⟩ := RestrictedPreparation.program_exec params raw initial (RestrictedParameters.budgetBase pmax)
  obtain ⟨hmask,hweight,hlog⟩ := RestrictedPhysicalPreparation.physical_cache hN order beta h u 1 J tape a params
    (fun p hp => RestrictedParameters.higher_model pmax P a B rho pmin p (hmax p hp)) _ prep hready
  rcases hready.1 with ⟨rN,rM,rh,re,rd,rb,rm,rp,rn,rl,ru,rz⟩
  have fields := RestrictedInputEncoding.real_fields order beta h u 1 J tape
  have rN' : prep.natReg 500=N := by simpa [raw] using rN
  have rM' : prep.natReg 501=M := by simpa [raw] using rM
  have rh' : prep.realReg 500=h := by simpa only [raw,RestrictedInputEncoding.nat_count,fields.1] using rh
  have rm' : prep.realReg 504=Real.tanh h := by simpa only [raw,RestrictedInputEncoding.nat_size,
      RestrictedInputEncoding.nat_count,fields.1,prepareField_mean] using rm
  have rp' : prep.realReg 505=FieldExpansion.spinWeight h false := by
    have hp : prep.realReg 505=(prepareField N h).plusWeight := by
      simpa only [raw,RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,fields.1] using rp
    exact hp.trans (prepareField_weight N h false)
  have rn' : prep.realReg 506=FieldExpansion.spinWeight h true := by
    have hm : prep.realReg 506=(prepareField N h).minusWeight := by
      simpa only [raw,RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,fields.1] using rn
    exact hm.trans (prepareField_weight N h true)
  let requested := runCode params raw accuracy prep
  have requestN : requested.natReg 500=N := by simp [requested,accuracy,runCode,step,rN']
  have requestM : requested.natReg 501=M := by simp [requested,accuracy,runCode,step,rM']
  have requestH : requested.realReg 500=h := by simp [requested,accuracy,runCode,step,rh']
  have requestMean : requested.realReg 504=Real.tanh h := by simp [requested,accuracy,runCode,step,rm']
  have requestU : requested.realReg 508=u := by
    simpa [requested,accuracy,runCode,step,rM',raw] using fields.2.1
  have requestP : requested.realReg 505=FieldExpansion.spinWeight h false := by simp [requested,accuracy,runCode,step,rp']
  have requestMinus : requested.realReg 506=FieldExpansion.spinWeight h true := by simp [requested,accuracy,runCode,step,rn']
  obtain ⟨cc,ctl,hctl,hcc,hk,hn,hr,hrm,hnm⟩ := RestrictedHigherControl.program_exec raw requested pmax P a B rho pmin
  have hk' : ctl.natReg 510=k := by simpa [k,cutoff,requestN,requestH,requestU,requestMean] using hk
  have cn : ctl.natReg 500=N ∧ ctl.natReg 501=M := by
    exact ⟨(hn 500 (by omega) (by omega)).trans requestN,(hn 501 (by omega) (by omega)).trans requestM⟩
  have cp : ctl.realReg 505=FieldExpansion.spinWeight h false := (hr 505 (by omega)).trans requestP
  have cm : ctl.realReg 506=FieldExpansion.spinWeight h true := (hr 506 (by omega)).trans requestMinus
  let ready := runCode params raw setup ctl
  let d := physicalData N M h ctl
  have hd : core (data ready)=core d := by simp [ready,setup,runCode,step,data,core,d,physicalData,cn,cp,cm]
  have hkr : ready.natReg 310=k := by simp [ready,setup,runCode,step,hk']
  have hspace : ready.natReg 284+ready.natReg 283≤ready.natReg 312 := by
    simp [ready,setup,runCode,step]
  obtain ⟨result,hresult,hvalue,hdata,hnf,hrf⟩ := RestrictedSupportProgram.program_realized params raw ready hspace
  rw [hd,hkr,RestrictedSupportExecution.totalCost_core] at hresult
  rw [hd,hkr,RestrictedSupportExecution.totalValue_core] at hvalue
  have de : ∀ j : Fin M,d.natMemory (d.edgeBase+j.val)=RestrictedMaskBridge.encode (order j).val := by
    intro j; simpa [d,physicalData,hnm,requested,accuracy,runCode,step] using hmask j
  have dw : ∀ j : Fin M,d.realMemory (d.weightBase+2*j.val)=Real.tanh (Model.coefficient N P a beta J (order j)) := by
    intro j; simpa [d,physicalData,hrm,requested,accuracy,runCode,step] using hweight j
  have kval : k≤N := cutoff_le N pmax P a B rho pmin h u
  have resultValue : result.realReg 330=(SupportExecution.supportSum Subtype.val Finset.univ
      (FieldExpansion.spinWeight h) (fun e => Real.tanh (Model.coefficient N P a beta J e)) k).value := by
    rw [hvalue]
    exact RestrictedSupportBridge.support_value d order Subtype.val (fun e => Real.tanh (Model.coefficient N P a beta J e)) h de dw rfl rfl k kval
  refine ⟨141*M+186+(8+(cc+(14+(RestrictedSupportProgram.totalCost d k 0 (k+1)+12)))),result,?_,?_,?_⟩
  · have hh := RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base he)
      (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base (exec_code params raw accuracy prep))
        (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hctl)
          (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base (exec_code params raw setup ctl)) hresult)))
    simpa only [program,params,raw,RestrictedInputEncoding.nat_count,setup,accuracy,codeCost,instrCost,
      List.sum_cons,List.map_cons,List.map_nil,List.sum_nil,Nat.add_zero] using hh
  · have hb : cachedFieldWeight (prepareInput N P a beta h J)=FieldExpansion.spinWeight h := by
      funext b; exact cachedFieldWeight_value N P a beta h J b
    have hw : cachedWeight (prepareInput N P a beta h J)=fun e => Real.tanh (Model.coefficient N P a beta J e) := by
      funext e; exact cachedWeight_value hN P a beta h J e
    simp only [HigherOrderExecution.execute]
    rw [hb,hw]
    exact resultValue
  · have hc := RestrictedSupportCost.total_bound d kval
    dsimp only [RestrictedSupportCost.factor,termCost,d,physicalData] at hc
    dsimp only [d,physicalData,k] at hc ⊢
    rw [requestN] at hcc
    omega

end Manuscript.RestrictedHigherGraphEndpoint
