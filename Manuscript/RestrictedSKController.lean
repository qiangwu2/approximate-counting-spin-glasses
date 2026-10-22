import Manuscript.RestrictedParameters
import Manuscript.RestrictedHighFrames

noncomputable section
namespace Manuscript.RestrictedSKController
open RestrictedMachine RestrictedControl RestrictedParameters

def setup : List Instruction := [.ncopy 200 500,.rcopy 200 508]
def finish : List Instruction := [.ncopy 510 201,.ncopy 511 202,.ncopy 512 203,.ncopy 513 204]
def program (a : ℕ→ℝ) (B rho : ℝ) : Program :=
  .seq (code setup) (.seq (skProgram (controlBase 2) (manuscriptSKDesign a B rho).threshold) (code finish))

theorem program_exec (input : Inputs) (s : State) (a : ℕ→ℝ) (B rho : ℝ) :
    ∃ count t,Exec (sk a B rho) input (program a B rho) s count t ∧
      count≤78*s.natReg 500+9*(SKControl.parameters (SKAlgorithm.q a B)
        (Real.log (SKAlgorithm.errorConstant a B rho/s.realReg 508))).operations+172 ∧
      t.natReg 510=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).branchLimit ∧
      t.natReg 511=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).exact.toNat ∧
      t.natReg 512=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).edgeLimit ∧
      t.natReg 513=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).trials ∧
      (∀ r,500≤r → r<510 ∨ 513<r → t.natReg r=s.natReg r) ∧
      (∀ r,500≤r → t.realReg r=s.realReg r) ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let params := sk a B rho
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 4 u := exec_code _ _ _ _
  obtain ⟨c,v,hv,hc,hval,hrm,hnm⟩ := sk_control_execution input u (controlBase 2)
    (background 2 a (LogApprox.constant {2} a B rho) (LogApprox.exponent {2} a B)) a B rho
  have vn (r : ℕ) (hr : 500≤r) : v.natReg r=s.natReg r := by
    apply (hv.natReg_frame (RestrictedHighFrames.sk _ _ r (by omega)).1).trans
    exact hu.natReg_frame (by simp [setup,code,Program.All,Instruction.natDestination]; omega)
  have vr (r : ℕ) (hr : 500≤r) : v.realReg r=s.realReg r := by
    apply (hv.realReg_frame (RestrictedHighFrames.sk _ _ r (by omega)).2).trans
    exact hu.realReg_frame (by simp [setup,code,Program.All,Instruction.realDestination]; omega)
  have hk := congrArg ControlResult.branchLimit hval
  have he := congrArg ControlResult.exact hval
  have hL := congrArg ControlResult.edgeLimit hval
  have hR := congrArg ControlResult.trials hval
  let t := runCode params input finish v
  have ht : Exec params input (code finish) v 8 t := exec_code _ _ _ _
  refine ⟨4+(c+8),t,Exec.seq hu (Exec.seq hv ht),?_,?_,?_,?_,?_,?_,?_,hrm,hnm⟩
  · have hc' : c≤78*s.natReg 500+9*(SKControl.parameters (SKAlgorithm.q a B)
        (Real.log (SKAlgorithm.errorConstant a B rho/s.realReg 508))).operations+160 := by
      simpa [u,setup,runCode,step] using hc
    omega
  · simpa [t,finish,u,setup,runCode,step] using hk
  · simpa [t,finish,u,setup,runCode,step] using he
  · simpa [t,finish,u,setup,runCode,step] using hL
  · simpa [t,finish,u,setup,runCode,step] using hR
  · intro r hr haway
    simp [t,finish,runCode,step,show r≠510 by omega,show r≠511 by omega,
      show r≠512 by omega,show r≠513 by omega,vn r hr]
  · intro r hr; exact vr r hr

end Manuscript.RestrictedSKController
