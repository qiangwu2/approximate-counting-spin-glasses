import Manuscript.RestrictedSKController

noncomputable section
namespace Manuscript.RestrictedControl
open RestrictedMachine

/-- The operational bound follows the branch actually taken. The exact branch
executes only its sixty instructions/dispatch steps and no parameter scans. -/
theorem sk_control_execution_precise (input : Inputs) (s : State) (base : ℕ) (background : Parameters)
    (a : ℕ→ℝ) (B rho : ℝ) :
    let d := manuscriptSKDesign a B rho
    let params := parameterBlock base 5 (skConstants d) background
    ∃ c t, Exec params input (skProgram base d.threshold) s c t ∧
      c≤78*s.natReg 200+9*(SKControl.control (s.natReg 200) a B rho (s.realReg 200)).operations+160 ∧
      (⟨t.natReg 201,t.natReg 202,t.natReg 203,t.natReg 204⟩ : ControlResult)=
        ⟨(SKControl.control (s.natReg 200) a B rho (s.realReg 200)).branchLimit,
         (SKControl.control (s.natReg 200) a B rho (s.realReg 200)).exact.toNat,
         (SKControl.control (s.natReg 200) a B rho (s.realReg 200)).edgeLimit,
         (SKControl.control (s.natReg 200) a B rho (s.realReg 200)).trials⟩ ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  dsimp only
  let d := manuscriptSKDesign a B rho
  let params := parameterBlock base 5 (skConstants d) background
  by_cases hex : SKAlgorithm.exactBranch (s.natReg 200) a B rho (s.realReg 200)
  · let ready := runCode params input (skRead base ++ branchTest d.threshold) s
    let t := runCode params input skExact ready
    have h0 : params base=d.errorConstant := by
      simpa [params,skConstants] using parameterBlock_value base 5 0 (skConstants d) background (by omega)
    have h1 : params (base+1)=d.nu := by
      simpa [params,skConstants] using parameterBlock_value base 5 1 (skConstants d) background (by omega)
    have hc : s.natReg 200<d.threshold ∨ d.nu*s.natReg 200≤Real.log (d.errorConstant/s.realReg 200) := hex
    have hflag : ready.natReg 246≠0 := by
      have hh : ready.natReg 246=0 ↔ ¬(s.natReg 200<d.threshold ∨
          d.nu*s.natReg 200≤Real.log (d.errorConstant/s.realReg 200)) := by
        simp [ready,skRead,branchTest,runCode,step,h0,h1]
      exact fun h=>hh.mp h hc
    have hread : Exec params input (code (skRead base ++ branchTest d.threshold)) s 52 ready := by
      convert exec_code params input (skRead base ++ branchTest d.threshold) s using 1
      simp [skRead,branchTest,codeCost,instrCost]
    have he : Exec params input (skProgram base d.threshold) s 60 t :=
      Exec.seq hread (Exec.branchNonzero hflag (exec_code params input skExact ready))
    refine ⟨60,t,he,by omega,?_,sk_memory_frame params input base d.threshold s t 60 he⟩
    rw [SKControl.control_exact _ _ _ _ _ hex]
    simp [t,ready,skExact,skRead,branchTest,runCode,step]
  · obtain ⟨c,t,he,hb,hv,hm⟩ := sk_control_execution input s base background a B rho
    refine ⟨c,t,he,?_,hv,hm⟩
    have hc : ¬(s.natReg 200<Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho) ∨
        Cutoffs.nu 1 (SKAlgorithm.scale B rho) (SKAlgorithm.c1 a B rho)*s.natReg 200≤
        Real.log (SKAlgorithm.errorConstant a B rho/s.realReg 200)) := hex
    have hp : (SKControl.parameters (SKAlgorithm.q a B)
          (Real.log (SKAlgorithm.errorConstant a B rho/s.realReg 200))).operations≤
        (SKControl.control (s.natReg 200) a B rho (s.realReg 200)).operations := by
      simp only [SKControl.control,InputPreparation.logarithm,InputPreparation.divide,
        SpinGlass.ArithmeticEvaluation.literal,hc,↓reduceIte]
      omega
    omega

end Manuscript.RestrictedControl

namespace Manuscript.RestrictedSKController
open RestrictedMachine RestrictedControl RestrictedParameters

theorem program_exec_precise (input : Inputs) (s : State) (a : ℕ→ℝ) (B rho : ℝ) :
    ∃ count t,Exec (sk a B rho) input (program a B rho) s count t ∧
      count≤78*s.natReg 500+9*(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).operations+172 ∧
      t.natReg 510=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).branchLimit ∧
      t.natReg 511=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).exact.toNat ∧
      t.natReg 512=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).edgeLimit ∧
      t.natReg 513=(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).trials ∧
      (∀ r,500≤r → r<510 ∨ 513<r → t.natReg r=s.natReg r) ∧
      (∀ r,500≤r → t.realReg r=s.realReg r) ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let params := sk a B rho
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 4 u := exec_code _ _ _ _
  obtain ⟨c,v,hv,hc,hval,hrm,hnm⟩ := sk_control_execution_precise input u (controlBase 2)
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
  · have hc' : c≤78*s.natReg 500+9*(SKControl.control (s.natReg 500) a B rho (s.realReg 508)).operations+160 := by
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
