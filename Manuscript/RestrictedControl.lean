import Manuscript.RestrictedKappa
import Manuscript.RestrictedCutoff
import Manuscript.RestrictedSKParameters

/-! Fixed outer control programs. Model-dependent constants are read from a
fixed parameter block, whose base is part of the program syntax. Runtime N,
budget u, field h, and prepared mean are registers, never program literals. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Manuscript.RestrictedControl
open RestrictedMachine

structure HigherDesign where
  threshold : ℕ
  errorConstant : ℝ
  nu : ℝ
  rho : ℝ
  pmin : ℝ
  kapMin : ℝ
  scale : ℝ

def higherConstants (d : HigherDesign) (j : ℕ) : ℝ :=
  match j with
  | 0 => d.errorConstant
  | 1 => d.nu
  | 2 => d.rho
  | 3 => (d.pmin-2)/d.pmin
  | 4 => -(1/d.pmin)
  | 5 => d.scale
  | 6 => Cutoffs.gamma d.kapMin d.scale
  | _ => 0

def higherChoice (d : HigherDesign) (N : ℕ) (u h mean : ℝ) : ℕ :=
  let lam := Real.log (d.errorConstant/u)
  if N<d.threshold ∨ d.nu*N≤lam then N else
    (CutoffExecution.cutoffSearch d.kapMin
      (HigherOrderExecution.kappaComputation N d.rho d.pmin h mean).value
      d.scale N lam).found.getD 1-1

def higherRead (base : ℕ) : List Instruction :=
  [.nconst 241 base, .readParam 220 241,
   .nconst 241 (base+1), .readParam 221 241,
   .nconst 241 (base+2), .readParam 222 241,
   .nconst 241 (base+3), .readParam 223 241,
   .nconst 241 (base+4), .readParam 224 241,
   .nconst 241 (base+5), .readParam 225 241,
   .nconst 241 (base+6), .readParam 226 241]
def branchTest (threshold : ℕ) : List Instruction :=
  [.rdiv 230 220 200, .rlog 230 230, .natToReal 231 200, .rmul 232 221 231,
   .nconst 241 threshold, .nle 242 241 200, .nconst 243 0, .neq 244 242 243,
   .rle 245 232 230, .nadd 246 244 245]
def higherExact : List Instruction := [.ncopy 201 200, .nconst 202 1]
def kappaSetup : List Instruction :=
  [.rcopy 0 231, .rcopy 1 201, .rcopy 2 202, .rcopy 3 222, .rcopy 4 223, .rcopy 5 224]
def higherCutoffSetup : List Instruction :=
  [.ncopy 0 200, .rcopy 1 20, .rcopy 2 225, .rcopy 3 230, .rcopy 4 226]
def higherFinish : List Instruction := [.ncopy 201 20, .nconst 202 0]
def higherTruncated : Program := .seq (code kappaSetup)
  (.seq RestrictedKappa.program (.seq (code higherCutoffSetup)
    (.seq RestrictedCutoff.program (code higherFinish))))
def higherProgram (base threshold : ℕ) : Program :=
  .seq (code (higherRead base ++ branchTest threshold))
    (.branch 246 (code higherExact) higherTruncated)

theorem kappa_high_frame (r : ℕ) (hr : 21≤r) :
    RestrictedKappa.program.All (fun op => op.realDestination ≠ some r) ∧
    RestrictedKappa.program.All (fun op => op.natDestination ≠ some r) := by
  simp [RestrictedKappa.program, RestrictedKappa.zeroTest, RestrictedKappa.nonzeroProgram,
    RestrictedKappa.absoluteProgram, RestrictedKappa.negativeCode,
    RestrictedKappa.arithmeticCode, RestrictedKappa.minimumProgram,
    Program.All, code, Instruction.realDestination, Instruction.natDestination]
  omega

theorem higher_prefix_spec (params : Parameters) (input : Inputs) (s : State)
    (base : ℕ) (d : HigherDesign)
    (hp : ∀ j<7, params (base+j)=higherConstants d j) :
    let t := runCode params input (higherRead base ++ branchTest d.threshold) s
    t.realReg 230=Real.log (d.errorConstant/s.realReg 200) ∧
    t.natReg 246=0 ↔
      (t.realReg 230=Real.log (d.errorConstant/s.realReg 200) ∧
       ¬(s.natReg 200<d.threshold ∨ d.nu*s.natReg 200≤Real.log (d.errorConstant/s.realReg 200))) := by
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  simp only [Nat.add_zero] at h0
  simp [higherRead, branchTest, runCode, step, h0, h1, higherConstants]

theorem higher_execution (params : Parameters) (input : Inputs) (s : State)
    (base : ℕ) (d : HigherDesign) (hA : 0<d.scale)
    (hp : ∀ j<7, params (base+j)=higherConstants d j) :
    ∃ c t, Exec params input (higherProgram base d.threshold) s c t ∧
      c≤78*s.natReg 200+220 ∧
      t.natReg 201=higherChoice d (s.natReg 200) (s.realReg 200) (s.realReg 201) (s.realReg 202) := by
  let ready := runCode params input (higherRead base ++ branchTest d.threshold) s
  have hread := exec_code params input (higherRead base ++ branchTest d.threshold) s
  have hcost : codeCost (higherRead base ++ branchTest d.threshold)=60 := by
    simp [higherRead,branchTest,codeCost,instrCost]
  rw [hcost] at hread
  have h0 := hp 0 (by omega)
  have h1 := hp 1 (by omega)
  have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  have h4 := hp 4 (by omega)
  have h5 := hp 5 (by omega)
  have h6 := hp 6 (by omega)
  simp only [Nat.add_zero] at h0
  have hrN : ready.natReg 200=s.natReg 200 := by simp [ready,higherRead,branchTest,runCode,step]
  have hflag : ready.natReg 246=0 ↔
      ¬(s.natReg 200<d.threshold ∨ d.nu*s.natReg 200≤Real.log (d.errorConstant/s.realReg 200)) := by
    simp [ready,higherRead,branchTest,runCode,step,h0,h1,higherConstants]
  by_cases hex : s.natReg 200<d.threshold ∨ d.nu*s.natReg 200≤Real.log (d.errorConstant/s.realReg 200)
  · have hf : ready.natReg 246≠0 := fun h => (hflag.mp h) hex
    let t := runCode params input higherExact ready
    refine ⟨66,t,Exec.seq hread (Exec.branchNonzero hf (exec_code _ _ higherExact ready)),by omega,?_⟩
    simp [t,higherExact,runCode,step,higherChoice,hex,hrN]
  · have hf : ready.natReg 246=0 := hflag.mpr hex
    let ks := runCode params input kappaSetup ready
    have hk : Exec params input (code kappaSetup) ready 12 ks := exec_code _ _ _ _
    obtain ⟨ck,k,hek,bk,vk⟩ := RestrictedKappa.program_exec params input ks
      (s.natReg 200) d.rho d.pmin (s.realReg 201) (s.realReg 202)
      (by simp [ks,kappaSetup,ready,higherRead,branchTest,runCode,step])
      (by simp [ks,kappaSetup,ready,higherRead,branchTest,runCode,step])
      (by simp [ks,kappaSetup,ready,higherRead,branchTest,runCode,step])
      (by simp [ks,kappaSetup,ready,higherRead,branchTest,runCode,step,h2,higherConstants])
      (by simp [ks,kappaSetup,ready,higherRead,branchTest,runCode,step,h3,higherConstants])
      (by simp [ks,kappaSetup,ready,higherRead,branchTest,runCode,step,h4,higherConstants])
    have kr (r : ℕ) (hr : 21≤r) : k.realReg r=ks.realReg r := hek.realReg_frame (kappa_high_frame r hr).1
    have kn : k.natReg 200=ks.natReg 200 := hek.natReg_frame (kappa_high_frame 200 (by omega)).2
    let cs := runCode params input higherCutoffSetup k
    have hc : Exec params input (code higherCutoffSetup) k 10 cs := exec_code _ _ _ _
    obtain ⟨cc,c,hec,bc,vc,_,_⟩ := RestrictedCutoff.program_exec params input cs d.kapMin
      (HigherOrderExecution.kappaComputation (s.natReg 200) d.rho d.pmin (s.realReg 201) (s.realReg 202)).value
      d.scale (Real.log (d.errorConstant/s.realReg 200)) (s.natReg 200) hA
      (by simp [cs,higherCutoffSetup,runCode,step,kn,ks,kappaSetup,ready,higherRead,branchTest])
      (by simpa [cs,higherCutoffSetup,runCode,step] using vk)
      (by simp [cs,higherCutoffSetup,runCode,step,kr 225 (by omega),ks,kappaSetup,ready,higherRead,branchTest,h5,higherConstants])
      (by simp [cs,higherCutoffSetup,runCode,step,kr 230 (by omega),ks,kappaSetup,ready,higherRead,branchTest,h0,higherConstants])
      (by simp [cs,higherCutoffSetup,runCode,step,kr 226 (by omega),ks,kappaSetup,ready,higherRead,branchTest,h6,higherConstants])
    let t := runCode params input higherFinish c
    have hfinish : Exec params input (code higherFinish) c 3 t := exec_code _ _ _ _
    refine ⟨60+((12+(ck+(10+(cc+3))))+3),t,
      Exec.seq hread (Exec.branchZero hf (Exec.seq hk (Exec.seq hek (Exec.seq hc (Exec.seq hec hfinish))))),by omega,?_⟩
    simpa [t,higherFinish,runCode,step,higherChoice,hex] using vc

def manuscriptHigherDesign (pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ) (B rho pmin : ℝ) : HigherDesign :=
  { threshold := Cutoffs.sizeThreshold pmax (SupportExponent.kappaMin pmin) (HigherOrderTail.scale P a B rho pmin)
    errorConstant := HigherOrderTail.errorConstant P a B rho
    nu := Cutoffs.nu (SupportExponent.kappaMin pmin) (HigherOrderTail.scale P a B rho pmin)
      (HigherOrderTail.c1 P a B rho pmin pmax)
    rho := max 1 rho
    pmin := pmin
    kapMin := SupportExponent.kappaMin pmin
    scale := HigherOrderTail.scale P a B rho pmin }

theorem higherChoice_eq_control (N pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ) (B rho pmin h u mean : ℝ) :
    higherChoice (manuscriptHigherDesign pmax P a B rho pmin) N u h mean =
      (HigherOrderExecution.control N pmax P a B rho pmin h u mean).cutoff := by
  simp only [higherChoice, manuscriptHigherDesign, HigherOrderExecution.control,
    InputPreparation.logarithm, InputPreparation.divide, SpinGlass.ArithmeticEvaluation.literal]
  split_ifs <;> rfl

end Manuscript.RestrictedControl
