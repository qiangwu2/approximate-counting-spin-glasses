import Manuscript.RestrictedFrames
import Manuscript.HigherOrderExecution

/-! Runtime computation of the external-field-dependent support exponent. -/
noncomputable section
namespace Manuscript.RestrictedKappa
open RestrictedMachine

def zeroTest : List Instruction :=
  [.rconst 10 0, .rle 0 1 10, .rle 1 10 1, .nmul 2 0 1]
def negativeCode : List Instruction := [.rconst 11 (-1), .rmul 12 11 2]
def absoluteProgram : Program := .seq (.atom (.rle 0 2 10))
  (.branch 0 (code negativeCode) (.atom (.rcopy 12 2)))
def arithmeticCode : List Instruction :=
  [.rdiv 13 3 12, .rlog 14 13, .rconst 15 2, .rmul 16 15 14,
    .rlog 17 0, .rdiv 18 16 17, .radd 19 18 5, .rle 0 4 19]
def minimumProgram : Program := .branch 0 (.atom (.rcopy 20 4)) (.atom (.rcopy 20 19))
def nonzeroProgram : Program :=
  .seq absoluteProgram (.seq (code arithmeticCode) minimumProgram)
def program : Program :=
  .seq (code zeroTest) (.branch 2 (.atom (.rcopy 20 4)) nonzeroProgram)

theorem absolute_exec (params : Parameters) (input : Inputs) (s : State)
    (hz : s.realReg 10 = 0) :
    ∃ cost final, Exec params input absoluteProgram s cost final ∧ cost ≤ 12 ∧
      final.realReg 12 = |s.realReg 2| := by
  let tested := step params input (.rle 0 2 10) s
  have ht : Exec params input (.atom (.rle 0 2 10)) s 4 tested := Exec.atom _ _
  by_cases h : s.realReg 2 ≤ 0
  · have hf : tested.natReg 0 ≠ 0 := by simp [tested, step, hz, h]
    let final := runCode params input negativeCode tested
    have hb : Exec params input (code negativeCode) tested 5 final := exec_code _ _ _ _
    refine ⟨12, final, Exec.seq ht (Exec.branchNonzero (no := .atom (.rcopy 12 2)) hf hb),
      by omega, ?_⟩
    simp [final, negativeCode, tested, runCode, step, abs_of_nonpos h]
  · have hf : tested.natReg 0 = 0 := by simp [tested, step, hz, h]
    refine ⟨9, _, Exec.seq ht (Exec.branchZero (yes := code negativeCode) hf
      (Exec.atom (.rcopy 12 2) tested)), by omega, ?_⟩
    simp [step, tested, abs_of_pos (lt_of_not_ge h)]

theorem absolute_keeps (r : ℕ) (h11 : r ≠ 11) (h12 : r ≠ 12) :
    absoluteProgram.All (fun op => op.realDestination ≠ some r) := by
  simp [absoluteProgram, negativeCode, Program.All, code, Instruction.realDestination,
    ne_comm, h11, h12]

theorem nonzero_exec (params : Parameters) (input : Inputs) (s : State)
    (hz : s.realReg 10 = 0) :
    ∃ cost final, Exec params input nonzeroProgram s cost final ∧ cost ≤ 44 ∧
      final.realReg 20 = min (s.realReg 4)
        (2 * Real.log (s.realReg 3 / |s.realReg 2|) / Real.log (s.realReg 0) + s.realReg 5) := by
  obtain ⟨ca, ab, ha, hca, hva⟩ := absolute_exec params input s hz
  have h0 := ha.realReg_frame (absolute_keeps 0 (by omega) (by omega))
  have h3 := ha.realReg_frame (absolute_keeps 3 (by omega) (by omega))
  have h4 := ha.realReg_frame (absolute_keeps 4 (by omega) (by omega))
  have h5 := ha.realReg_frame (absolute_keeps 5 (by omega) (by omega))
  let computed := runCode params input arithmeticCode ab
  have hc : Exec params input (code arithmeticCode) ab 27 computed := exec_code _ _ _ _
  have hv : computed.realReg 19 =
      2 * Real.log (s.realReg 3 / |s.realReg 2|) / Real.log (s.realReg 0) + s.realReg 5 := by
    simp [computed, arithmeticCode, runCode, step, hva, h0, h3, h5]
  have hfour : computed.realReg 4 = s.realReg 4 := by
    simpa [computed, arithmeticCode, runCode, step] using h4
  have hflag : computed.natReg 0 = if computed.realReg 4 ≤ computed.realReg 19 then 1 else 0 := by
    simp [computed, arithmeticCode, runCode, step]
  by_cases h : computed.realReg 4 ≤ computed.realReg 19
  · have hf : computed.natReg 0 ≠ 0 := by simp [hflag, h]
    have hm := Exec.branchNonzero (params := params) (input := input) (no := .atom (.rcopy 20 19)) hf
      (Exec.atom (.rcopy 20 4) computed)
    refine ⟨ca+(27+5), _, Exec.seq ha (Exec.seq hc hm), by omega, ?_⟩
    simp only [step, writeRealReg_realReg]
    rw [← hv, ← hfour, min_eq_left h]
    simp
  · have hf : computed.natReg 0 = 0 := by simp [hflag, h]
    have hm := Exec.branchZero (params := params) (input := input) (yes := .atom (.rcopy 20 4)) hf
      (Exec.atom (.rcopy 20 19) computed)
    refine ⟨ca+(27+5), _, Exec.seq ha (Exec.seq hc hm), by omega, ?_⟩
    simp only [step, writeRealReg_realReg]
    rw [← hv, ← hfour, min_eq_right (le_of_not_ge h)]
    simp

theorem program_exec (params : Parameters) (input : Inputs) (s : State)
    (N : ℕ) (rho p h mean : ℝ)
    (hN : s.realReg 0 = N) (hh : s.realReg 1 = h) (hm : s.realReg 2 = mean)
    (hr : s.realReg 3 = rho) (hk : s.realReg 4 = (p-2)/p) (hp : s.realReg 5 = -(1/p)) :
    ∃ cost final, Exec params input program s cost final ∧ cost ≤ 60 ∧
      final.realReg 20 = (HigherOrderExecution.kappaComputation N rho p h mean).value := by
  let tested := runCode params input zeroTest s
  have ht : Exec params input (code zeroTest) s 13 tested := exec_code _ _ _ _
  have hf : tested.natReg 2 = if h = 0 then 1 else 0 := by
    by_cases hzero : h = 0
    · simp [tested, zeroTest, runCode, step, hh, hzero]
    · by_cases hneg : h ≤ 0
      · have hpos : ¬0 ≤ h := by intro hp; apply hzero; linarith
        simp [tested, zeroTest, runCode, step, hh, hzero, hneg, hpos]
      · simp [tested, zeroTest, runCode, step, hh, hzero, hneg]
  by_cases hzero : h = 0
  · have hf' : tested.natReg 2 ≠ 0 := by simp [hf, hzero]
    refine ⟨18, _, Exec.seq ht (Exec.branchNonzero (no := nonzeroProgram) hf'
      (Exec.atom (.rcopy 20 4) tested)), by omega, ?_⟩
    simp [tested, zeroTest, runCode, step, HigherOrderExecution.kappaComputation, hzero, hk]
  · have hf' : tested.natReg 2 = 0 := by simp [hf, hzero]
    obtain ⟨cost, final, he, hc, hv⟩ := nonzero_exec params input tested (by simp [tested, zeroTest, runCode, step])
    refine ⟨13+(cost+3), final, Exec.seq ht (Exec.branchZero
      (yes := .atom (.rcopy 20 4)) hf' he), by omega, ?_⟩
    simpa [tested, zeroTest, runCode, step, hN, hr, hm, hk, hp,
      HigherOrderExecution.kappaComputation, hzero, HigherOrderExecution.minimum,
      InputPreparation.divide, InputPreparation.logarithm, SpinGlass.ArithmeticEvaluation.add,
      SpinGlass.ArithmeticEvaluation.mul, SpinGlass.ArithmeticEvaluation.literal] using hv

end Manuscript.RestrictedKappa
