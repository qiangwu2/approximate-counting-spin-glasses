import Manuscript.RestrictedControl

noncomputable section
set_option maxHeartbeats 1600000
namespace Manuscript.RestrictedControl
open RestrictedMachine

structure SKDesign where
  threshold : ℕ
  errorConstant : ℝ
  nu : ℝ
  scale : ℝ
  q : ℝ

def skConstants (d : SKDesign) (j : ℕ) : ℝ :=
  match j with
  | 0 => d.errorConstant
  | 1 => d.nu
  | 2 => d.scale
  | 3 => Cutoffs.gamma 1 d.scale
  | 4 => Real.log (1/d.q)
  | _ => 0

structure ControlResult where
  branchLimit : ℕ
  exact : ℕ
  edgeLimit : ℕ
  trials : ℕ

def skChoice (d : SKDesign) (N : ℕ) (u : ℝ) : ControlResult :=
  let lam := Real.log (d.errorConstant/u)
  if N<d.threshold ∨ d.nu*N≤lam then ⟨N,1,0,1⟩ else
    ⟨(CutoffExecution.cutoffSearch 1 1 d.scale N lam).found.getD 1-1,0,
      (SKControl.parameters d.q lam).edgeLimit,(SKControl.parameters d.q lam).trials⟩

def skRead (base : ℕ) : List Instruction :=
  [.nconst 241 base, .readParam 220 241,
   .nconst 241 (base+1), .readParam 221 241,
   .nconst 241 (base+2), .readParam 225 241,
   .nconst 241 (base+3), .readParam 226 241,
   .nconst 241 (base+4), .readParam 224 241]
def skExact : List Instruction :=
  [.ncopy 201 200, .nconst 202 1, .nconst 203 0, .nconst 204 1]
def skCutoffSetup : List Instruction :=
  [.ncopy 0 200, .rconst 1 1, .rcopy 2 225, .rcopy 3 230, .rcopy 4 226]
def skParameterSetup : List Instruction := [.ncopy 201 20, .rcopy 30 230, .rcopy 31 224]
def skFinish : List Instruction := [.ncopy 203 30, .ncopy 204 31, .nconst 202 0]
def skTruncated : Program := .seq (code skCutoffSetup)
  (.seq RestrictedCutoff.program (.seq (code skParameterSetup)
    (.seq RestrictedSKParameters.program (code skFinish))))
def skProgram (base threshold : ℕ) : Program :=
  .seq (code (skRead base ++ branchTest threshold))
    (.branch 246 (code skExact) skTruncated)

theorem cutoff_high_frame (r : ℕ) (hr : 22≤r) :
    RestrictedCutoff.program.All (fun op => op.realDestination ≠ some r) ∧
    RestrictedCutoff.program.All (fun op => op.natDestination ≠ some r) := by
  simp [RestrictedCutoff.program,RestrictedCutoff.prepareCode,RestrictedCutoff.scanSetup,
    RestrictedCutoff.finishCode,RestrictedFloor.program,RestrictedFloor.loop,RestrictedFloor.bodyCode,
    RestrictedFloor.testCode,RestrictedCutoffScan.program,RestrictedCutoffScan.setupCode,
    RestrictedCutoffScan.loop,RestrictedCutoffScan.body,RestrictedCutoffScan.scoreCode,
    RestrictedCutoffScan.yesCode,RestrictedCutoffScan.noCode,
    Program.All,code,Instruction.realDestination,Instruction.natDestination]
  omega

theorem parameters_high_frame (r : ℕ) (hr : 35≤r) :
    RestrictedSKParameters.program.All (fun op => op.realDestination ≠ some r) ∧
    RestrictedSKParameters.program.All (fun op => op.natDestination ≠ some r) := by
  simp [RestrictedSKParameters.program,RestrictedSKParameters.firstCode,
    RestrictedSKParameters.secondCode,RestrictedSKParameters.lastCode,
    RestrictedCeiling.program,RestrictedCeiling.loop,RestrictedCeiling.bodyCode,
    RestrictedCeiling.testCode,Program.All,code,Instruction.realDestination,Instruction.natDestination]
  omega

theorem sk_execution (params : Parameters) (input : Inputs) (s : State)
    (base : ℕ) (d : SKDesign) (hA : 0<d.scale)
    (hp : ∀ j<5, params (base+j)=skConstants d j) :
    ∃ c t, Exec params input (skProgram base d.threshold) s c t ∧
      c≤78*s.natReg 200+9*(SKControl.parameters d.q (Real.log (d.errorConstant/s.realReg 200))).operations+160 ∧
      (⟨t.natReg 201,t.natReg 202,t.natReg 203,t.natReg 204⟩ : ControlResult)=
        skChoice d (s.natReg 200) (s.realReg 200) := by
  let ready := runCode params input (skRead base ++ branchTest d.threshold) s
  have hread := exec_code params input (skRead base ++ branchTest d.threshold) s
  have hcost : codeCost (skRead base ++ branchTest d.threshold)=52 := by
    simp [skRead,branchTest,codeCost,instrCost]
  rw [hcost] at hread
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  have h4 := hp 4 (by omega)
  simp only [Nat.add_zero] at h0
  have hrN : ready.natReg 200=s.natReg 200 := by simp [ready,skRead,branchTest,runCode,step]
  have hflag : ready.natReg 246=0 ↔
      ¬(s.natReg 200<d.threshold ∨ d.nu*s.natReg 200≤Real.log (d.errorConstant/s.realReg 200)) := by
    simp [ready,skRead,branchTest,runCode,step,h0,h1,skConstants]
  by_cases hex : s.natReg 200<d.threshold ∨ d.nu*s.natReg 200≤Real.log (d.errorConstant/s.realReg 200)
  · have hf : ready.natReg 246≠0 := fun h => (hflag.mp h) hex
    let t := runCode params input skExact ready
    refine ⟨60,t,Exec.seq hread (Exec.branchNonzero hf (exec_code _ _ skExact ready)),by omega,?_⟩
    simp [t,skExact,runCode,step,skChoice,hex,hrN]
  · have hf : ready.natReg 246=0 := hflag.mpr hex
    let cs := runCode params input skCutoffSetup ready
    have hc : Exec params input (code skCutoffSetup) ready 9 cs := exec_code _ _ _ _
    obtain ⟨cc,c,hec,bc,vc,_,_⟩ := RestrictedCutoff.program_exec params input cs 1 1
      d.scale (Real.log (d.errorConstant/s.realReg 200)) (s.natReg 200) hA
      (by simp [cs,skCutoffSetup,ready,skRead,branchTest,runCode,step])
      (by simp [cs,skCutoffSetup,runCode,step])
      (by simp [cs,skCutoffSetup,ready,skRead,branchTest,runCode,step,h2,skConstants])
      (by simp [cs,skCutoffSetup,ready,skRead,branchTest,runCode,step,h0,skConstants])
      (by simp [cs,skCutoffSetup,ready,skRead,branchTest,runCode,step,h3,skConstants])
    have cr (r : ℕ) (hr : 22≤r) : c.realReg r=cs.realReg r := hec.realReg_frame (cutoff_high_frame r hr).1
    let ps := runCode params input skParameterSetup c
    have hpExec : Exec params input (code skParameterSetup) c 6 ps := exec_code _ _ _ _
    obtain ⟨cp,v,hep,bp,vL,vR,_,_⟩ := RestrictedSKParameters.program_exec params input ps d.q
      (Real.log (d.errorConstant/s.realReg 200))
      (by simp [ps,skParameterSetup,runCode,step,cr 230 (by omega),cs,skCutoffSetup,ready,skRead,branchTest,h0,skConstants])
      (by simp [ps,skParameterSetup,runCode,step,cr 224 (by omega),cs,skCutoffSetup,ready,skRead,branchTest,h4,skConstants])
    have vcut : v.natReg 201=c.natReg 20 := by
      rw [hep.natReg_frame (parameters_high_frame 201 (by omega)).2]
      simp [ps,skParameterSetup,runCode,step]
    let t := runCode params input skFinish v
    have hfini : Exec params input (code skFinish) v 5 t := exec_code _ _ _ _
    refine ⟨52+((9+(cc+(6+(cp+5))))+3),t,
      Exec.seq hread (Exec.branchZero hf (Exec.seq hc (Exec.seq hec (Exec.seq hpExec (Exec.seq hep hfini))))),by omega,?_⟩
    simp [t,skFinish,runCode,step,skChoice,hex,vcut,vc,vL,vR]

def manuscriptSKDesign (a : ℕ→ℝ) (B rho : ℝ) : SKDesign :=
  { threshold := Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho)
    errorConstant := SKAlgorithm.errorConstant a B rho
    nu := Cutoffs.nu 1 (SKAlgorithm.scale B rho) (SKAlgorithm.c1 a B rho)
    scale := SKAlgorithm.scale B rho
    q := SKAlgorithm.q a B }

theorem skChoice_eq_control (N : ℕ) (a : ℕ→ℝ) (B rho u : ℝ) :
    skChoice (manuscriptSKDesign a B rho) N u =
      ⟨(SKControl.control N a B rho u).branchLimit,
       (SKControl.control N a B rho u).exact.toNat,
       (SKControl.control N a B rho u).edgeLimit,
       (SKControl.control N a B rho u).trials⟩ := by
  simp only [skChoice,manuscriptSKDesign,SKControl.control,
    InputPreparation.logarithm,InputPreparation.divide,SpinGlass.ArithmeticEvaluation.literal]
  split_ifs <;> rfl

end Manuscript.RestrictedControl
