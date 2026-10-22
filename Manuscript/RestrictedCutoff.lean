import Manuscript.RestrictedFloor
import Manuscript.RestrictedCutoffScan
import Manuscript.RestrictedFrames

/-! Composition of the bounded floor and score search in the same machine. -/
noncomputable section
namespace Manuscript.RestrictedCutoff
open RestrictedMachine

/-- Initial natural register 0 contains N. Real registers 1,2,3,4 contain
the exponent, scale, logarithmic target, and gamma. Output k is natural 20. -/
def prepareCode : List Instruction :=
  [.ncopy 6 0, .rcopy 10 1, .rcopy 11 2, .rcopy 13 3, .natToReal 12 0, .rmul 0 4 12]
def scanSetup : List Instruction := [.ncopy 11 0, .nconst 10 1]
def finishCode : List Instruction := [.nconst 21 1, .nsub 20 12 21]
def program : Program :=
  .seq (code prepareCode)
    (.seq RestrictedFloor.program
      (.seq (code scanSetup) (.seq RestrictedCutoffScan.program (code finishCode))))

theorem floor_keeps (r : ℕ) (hr : 2 ≤ r) :
    RestrictedFloor.program.All (fun op => op.realDestination ≠ some r) := by
  simp [RestrictedFloor.program, RestrictedFloor.loop, RestrictedFloor.bodyCode,
    RestrictedFloor.testCode, Program.All, code, Instruction.realDestination]
  omega

theorem scanSetup_keeps (r : ℕ) :
    (code scanSetup).All (fun op => op.realDestination ≠ some r) := by
  simp [scanSetup, Program.All, code, Instruction.realDestination]

theorem getD_sub_one (o : Option ℕ) : o.getD 0 - 1 = o.getD 1 - 1 := by
  cases o <;> rfl

theorem program_exec (params : Parameters) (input : Inputs) (s : State)
    (kapMin kap A Lambda : ℝ) (N : ℕ) (hA : 0 < A)
    (hn : s.natReg 0 = N) (hk : s.realReg 1 = kap) (ha : s.realReg 2 = A)
    (hl : s.realReg 3 = Lambda) (hg : s.realReg 4 = Cutoffs.gamma kapMin A) :
    ∃ cost final, Exec params input program s cost final ∧ cost ≤ 78*N+65 ∧
      final.natReg 20 = (CutoffExecution.cutoffSearch kapMin kap A N Lambda).found.getD 1 - 1 ∧
      final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  let prepared := runCode params input prepareCode s
  have hp : Exec params input (code prepareCode) s 15 prepared := exec_code _ _ _ _
  have hpN : prepared.natReg 0 = N := by simp [prepared, prepareCode, runCode, step, hn]
  have hpR : prepared.realReg 0 = Cutoffs.gamma kapMin A * N := by
    simp [prepared, prepareCode, runCode, step, hn, hg]
  obtain ⟨cf, floored, hf, hcf, hvf, hrf, hmf, hnf⟩ := RestrictedFloor.program_exec params input prepared
  let scannedInput := runCode params input scanSetup floored
  have hs : Exec params input (code scanSetup) floored 3 scannedInput := exec_code _ _ _ _
  have hks : scannedInput.realReg 10 = kap := by
    rw [hs.realReg_frame (scanSetup_keeps 10), hf.realReg_frame (floor_keeps 10 (by omega))]
    simp [prepared, prepareCode, runCode, step, hk]
  have has : scannedInput.realReg 11 = A := by
    rw [hs.realReg_frame (scanSetup_keeps 11), hf.realReg_frame (floor_keeps 11 (by omega))]
    simp [prepared, prepareCode, runCode, step, ha]
  have hns : scannedInput.realReg 12 = N := by
    rw [hs.realReg_frame (scanSetup_keeps 12), hf.realReg_frame (floor_keeps 12 (by omega))]
    simp [prepared, prepareCode, runCode, step, hn]
  have hls : scannedInput.realReg 13 = Lambda := by
    rw [hs.realReg_frame (scanSetup_keeps 13), hf.realReg_frame (floor_keeps 13 (by omega))]
    simp [prepared, prepareCode, runCode, step, hl]
  have hstart : scannedInput.natReg 10 = 1 := by simp [scannedInput, scanSetup, runCode, step]
  have hfuel : scannedInput.natReg 11 = floored.natReg 0 := by simp [scannedInput, scanSetup, runCode, step]
  obtain ⟨cs, scanned, hscan, hcs, hvs, hms, hnts⟩ := RestrictedCutoffScan.program_exec params input
    scannedInput kap A N Lambda 1 (floored.natReg 0) hks has hns hls hstart hfuel
  let final := runCode params input finishCode scanned
  have hfinish : Exec params input (code finishCode) scanned 5 final := exec_code _ _ _ _
  have hfb : floored.natReg 0 ≤ N := by
    rw [hvf, hpR, hpN, CutoffExecution.boundedFloor_value]
    · exact Nat.min_le_left _ _
    · have hgamma := Cutoffs.gamma_pos (kapMin := kapMin) hA
      positivity
  refine ⟨15+(cf+(3+(cs+5))), final, Exec.seq hp (Exec.seq hf (Exec.seq hs (Exec.seq hscan hfinish))),
    by rw [hpN] at hcf; omega, ?_, ?_, ?_⟩
  · change scanned.natReg 12 - 1 = _
    rw [hvs, getD_sub_one, hvf, hpR, hpN]
    rfl
  · exact hms.trans hmf
  · exact hnts.trans hnf

end Manuscript.RestrictedCutoff
