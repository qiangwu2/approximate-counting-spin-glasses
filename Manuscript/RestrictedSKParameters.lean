import Manuscript.RestrictedCeiling
import Manuscript.RestrictedFrames
import Manuscript.SKControl

/-! Both SK integer parameters are computed by the proved increment loop. -/
noncomputable section
namespace Manuscript.RestrictedSKParameters
open RestrictedMachine

/-- Real registers 30,31 hold Lambda and log(1/q). Natural 30,31 return L,R. -/
def firstCode : List Instruction := [.rdiv 0 30 31]
def secondCode : List Instruction :=
  [.ncopy 30 0, .natToReal 32 0, .rconst 33 2, .rmul 34 33 32,
    .radd 0 34 30, .rexp 0 0]
def lastCode : List Instruction := [.ncopy 31 0]
def program : Program := .seq (code firstCode)
  (.seq RestrictedCeiling.program
    (.seq (code secondCode) (.seq RestrictedCeiling.program (code lastCode))))

theorem ceiling_real_frame (r : ℕ) (hr : 2 ≤ r) :
    RestrictedCeiling.program.All (fun op => op.realDestination ≠ some r) := by
  simp [RestrictedCeiling.program, RestrictedCeiling.loop, RestrictedCeiling.bodyCode,
    RestrictedCeiling.testCode, Program.All, code, Instruction.realDestination]
  omega

theorem ceiling_nat_frame (r : ℕ) (hr : 3 ≤ r) :
    RestrictedCeiling.program.All (fun op => op.natDestination ≠ some r) := by
  simp [RestrictedCeiling.program, RestrictedCeiling.loop, RestrictedCeiling.bodyCode,
    RestrictedCeiling.testCode, Program.All, code, Instruction.natDestination]
  omega

theorem program_exec (params : Parameters) (input : Inputs) (s : State)
    (q Lambda : ℝ) (hL : s.realReg 30 = Lambda) (hq : s.realReg 31 = Real.log (1/q)) :
    ∃ cost final, Exec params input program s cost final ∧
      cost ≤ 9 * (SKControl.parameters q Lambda).operations ∧
      final.natReg 30 = (SKControl.parameters q Lambda).edgeLimit ∧
      final.natReg 31 = (SKControl.parameters q Lambda).trials ∧
      final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  let ready := runCode params input firstCode s
  have hfirst : Exec params input (code firstCode) s 4 ready := exec_code _ _ _ _
  have hx : ready.realReg 0 = Lambda / Real.log (1/q) := by
    simp [ready, firstCode, runCode, step, hL, hq]
  obtain ⟨edges, he, hv, hx', hm, hn⟩ := RestrictedCeiling.program_exec params input ready
  have hLe : edges.natReg 0 = SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda := by
    simpa [hx, SpinGlass.AlgorithmBudgets.edgeCutoff] using hv
  have hLambda : edges.realReg 30 = Lambda := by
    rw [he.realReg_frame (ceiling_real_frame 30 (by omega))]
    simp [ready, firstCode, runCode, step, hL]
  let next := runCode params input secondCode edges
  have hsecond : Exec params input (code secondCode) edges 17 next := exec_code _ _ _ _
  have hnL : next.natReg 30 = SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda := by
    simpa [next, secondCode, runCode, step] using hLe
  have hnX : next.realReg 0 = Real.exp
      ((2 : ℝ) * SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda + Lambda) := by
    simp [next, secondCode, runCode, step, hLe, hLambda]
  obtain ⟨trials, ht, hvt, hxt, hmt, hnt⟩ := RestrictedCeiling.program_exec params input next
  let final := runCode params input lastCode trials
  have hlast : Exec params input (code lastCode) trials 2 final := exec_code _ _ _ _
  have hR : trials.natReg 0 = SpinGlass.AlgorithmBudgets.colorTrials
      (2*SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda) Lambda := by
    simpa [hnX, SpinGlass.AlgorithmBudgets.colorTrials] using hvt
  refine ⟨4+((18*Nat.ceil (ready.realReg 0)+16)+
    (17+((18*Nat.ceil (next.realReg 0)+16)+2))), final,
    Exec.seq hfirst (Exec.seq he (Exec.seq hsecond (Exec.seq ht hlast))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx, hnX, SKControl.parameters_operations]
    simp only [SpinGlass.AlgorithmBudgets.edgeCutoff, SpinGlass.AlgorithmBudgets.colorTrials,
      Nat.cast_mul, Nat.cast_ofNat]
    omega
  · rw [SKControl.parameters_edgeLimit]
    have hh := ht.natReg_frame (ceiling_nat_frame 30 (by omega))
    simpa [final, lastCode, runCode, step, hnL] using hh
  · simpa [final, lastCode, runCode, step, SKControl.parameters_trials] using hR
  · exact hmt.trans hm
  · exact hnt.trans hn

end Manuscript.RestrictedSKParameters
