import Manuscript.RestrictedMachine
import Manuscript.CutoffExecution

/-! Uniform first-crossing search using the actual score computation and
bounded comparison loop. The output integer is zero when no crossing occurs. -/
noncomputable section
namespace Manuscript.RestrictedCutoffScan
open RestrictedMachine

def scoreCode : List Instruction :=
  [ .natToReal 14 10, .rmul 15 11 14, .rdiv 16 12 15,
    .rlog 17 16, .rmul 18 10 14, .rmul 19 18 17, .rle 15 13 19 ]
def yesCode : List Instruction := [.ncopy 12 10, .nconst 14 0]
def noCode : List Instruction :=
  [.nadd 10 10 13, .nsub 11 11 13, .nle 14 11 16, .nsub 14 13 14]
def body : Program := .seq (code scoreCode) (.branch 15 (code yesCode) (code noCode))
def loop : Program := .while 14 body
def setupCode : List Instruction :=
  [.nconst 12 0, .nconst 13 1, .nconst 16 0, .nle 14 11 16, .nsub 14 13 14]
def program : Program := .seq (code setupCode) loop

structure Ready (s : State) (kap A : ℝ) (N : ℕ) (Lambda : ℝ) (start fuel : ℕ) : Prop where
  kap_eq : s.realReg 10 = kap
  scale_eq : s.realReg 11 = A
  size_eq : s.realReg 12 = N
  budget_eq : s.realReg 13 = Lambda
  current_eq : s.natReg 10 = start
  fuel_eq : s.natReg 11 = fuel
  output_eq : s.natReg 12 = 0
  one_eq : s.natReg 13 = 1
  zero_eq : s.natReg 16 = 0
  flag_eq : s.natReg 14 = if fuel = 0 then 0 else 1

theorem score_cost : codeCost scoreCode = 26 := rfl
theorem yes_cost : codeCost yesCode = 3 := rfl
theorem no_cost : codeCost noCode = 16 := rfl
theorem setup_cost : codeCost setupCode = 11 := rfl

theorem score_flag (params : Parameters) (input : Inputs) (s : State)
    (kap A : ℝ) (N : ℕ) (Lambda : ℝ) (start fuel : ℕ)
    (h : Ready s kap A N Lambda start fuel) :
    (runCode params input scoreCode s).natReg 15 =
      if Lambda ≤ SpinGlass.CutoffTail.phi kap A N start then 1 else 0 := by
  rcases h with ⟨hk, ha, hn, hl, hs, hf, ho, h1, hz, hb⟩
  simp [scoreCode, runCode, step, hk, ha, hn, hl, hs, SpinGlass.CutoffTail.phi]

theorem no_ready (params : Parameters) (input : Inputs) (s : State)
    (kap A : ℝ) (N : ℕ) (Lambda : ℝ) (start fuel : ℕ)
    (h : Ready s kap A N Lambda start (fuel+1)) :
    Ready (runCode params input noCode (runCode params input scoreCode s))
      kap A N Lambda (start+1) fuel := by
  rcases h with ⟨hk, ha, hn, hl, hs, hf, ho, h1, hz, hb⟩
  constructor <;> simp [noCode, scoreCode, runCode, step, hk, ha, hn, hl, hs, hf, ho, h1, hz]
  split_ifs <;> rfl

theorem loop_exec (params : Parameters) (input : Inputs) (kap A : ℝ) (N : ℕ)
    (Lambda : ℝ) (start fuel : ℕ) (s : State) (h : Ready s kap A N Lambda start fuel) :
    ∃ cost final, Exec params input loop s cost final ∧ cost ≤ 48*fuel+3 ∧
      final.natReg 12 = (CutoffExecution.scan kap A N Lambda start fuel).found.getD 0 ∧
      final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  cases fuel with
  | zero =>
    have hz : s.natReg 14 = 0 := by simpa using h.flag_eq
    refine ⟨3, s, Exec.whileZero s hz, by omega, ?_, rfl, rfl⟩
    simpa [CutoffExecution.scan] using h.output_eq
  | succ fuel =>
    let tested := runCode params input scoreCode s
    have ht : Exec params input (code scoreCode) s 26 tested := exec_code _ _ _ _
    have hcontinue : s.natReg 14 ≠ 0 := by simp [h.flag_eq]
    by_cases hcross : Lambda ≤ SpinGlass.CutoffTail.phi kap A N start
    · have hf : tested.natReg 15 ≠ 0 := by
        simp [tested, score_flag params input s kap A N Lambda start (fuel+1) h, hcross]
      let final := runCode params input yesCode tested
      have hy : Exec params input (code yesCode) tested 3 final := exec_code _ _ _ _
      have hz : final.natReg 14 = 0 := by simp [final, yesCode, runCode, step]
      have hb : Exec params input body s 32 final :=
        Exec.seq ht (Exec.branchNonzero (no := code noCode) hf hy)
      have he : Exec params input loop s 38 final :=
        Exec.whileNonzero hcontinue hb (Exec.whileZero final hz)
      refine ⟨38, final, he, by omega, ?_, rfl, rfl⟩
      simp [final, yesCode, tested, scoreCode, runCode, step, h.current_eq,
        CutoffExecution.scan, CutoffExecution.phiComputation_value, hcross]
    · have hf : tested.natReg 15 = 0 := by
        simp [tested, score_flag params input s kap A N Lambda start (fuel+1) h, hcross]
      let next := runCode params input noCode tested
      have hn : Ready next kap A N Lambda (start+1) fuel :=
        no_ready params input s kap A N Lambda start fuel h
      obtain ⟨cost, final, he, hc, hv, hm, hnm⟩ :=
        loop_exec params input kap A N Lambda (start+1) fuel next hn
      have hno : Exec params input (code noCode) tested 16 next := exec_code _ _ _ _
      have hb : Exec params input body s 45 next :=
        Exec.seq ht (Exec.branchZero (yes := code yesCode) hf hno)
      refine ⟨45+cost+3, final, Exec.whileNonzero hcontinue hb he, by omega, ?_, hm, hnm⟩
      simpa [CutoffExecution.scan, CutoffExecution.phiComputation_value, hcross] using hv
termination_by fuel

theorem program_exec (params : Parameters) (input : Inputs) (s : State)
    (kap A : ℝ) (N : ℕ) (Lambda : ℝ) (start fuel : ℕ)
    (hk : s.realReg 10 = kap) (ha : s.realReg 11 = A) (hN : s.realReg 12 = N)
    (hL : s.realReg 13 = Lambda) (hs : s.natReg 10 = start) (hf : s.natReg 11 = fuel) :
    ∃ cost final, Exec params input program s cost final ∧ cost ≤ 48*fuel+14 ∧
      final.natReg 12 = (CutoffExecution.scan kap A N Lambda start fuel).found.getD 0 ∧
      final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  let initialScan := runCode params input setupCode s
  have h : Ready initialScan kap A N Lambda start fuel := by
    constructor <;> simp [initialScan, setupCode, runCode, step, hk, ha, hN, hL, hs, hf]
    split_ifs <;> rfl
  obtain ⟨cost, final, he, hc, hv, hm, hn⟩ := loop_exec params input kap A N Lambda start fuel initialScan h
  have hi : Exec params input (code setupCode) s 11 initialScan := exec_code _ _ _ _
  exact ⟨11+cost, final, Exec.seq hi he, by omega, hv, hm, hn⟩

end Manuscript.RestrictedCutoffScan
