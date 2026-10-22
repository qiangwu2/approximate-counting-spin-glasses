import Manuscript.CountedCeil
import Manuscript.CutoffExecution
import Manuscript.SKAlgorithm

/-! Concrete SK vertex, edge and repetition cutoffs; no floor/ceiling oracle. -/
noncomputable section
namespace Manuscript.SKControl
open SpinGlass.ArithmeticEvaluation Manuscript.InputPreparation

structure Parameters where
  edgeLimit : ℕ
  trials : ℕ
  operations : ℕ

/-- The input is the saved logarithmic budget. The edge cutoff and trial count
are computed by the terminating comparison-and-increment ceiling program. -/
def parameters (q Lambda : ℝ) : Parameters :=
  let ratio := divide (literal Lambda) (literal (Real.log (1/q)))
  let edges := CountedCeil.ceiling ratio.value
  let exponent := add (mul (literal 2) (literal edges.value)) (literal Lambda)
  let threshold := exponential exponent
  let reps := CountedCeil.ceiling threshold.value
  ⟨edges.value,reps.value,ratio.operations+edges.operations+threshold.operations+reps.operations+2⟩

@[simp] theorem parameters_edgeLimit (q Lambda : ℝ) :
    (parameters q Lambda).edgeLimit = SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda := by
  simp [parameters,divide,literal,SpinGlass.AlgorithmBudgets.edgeCutoff]

@[simp] theorem parameters_trials (q Lambda : ℝ) :
    (parameters q Lambda).trials =
      SpinGlass.AlgorithmBudgets.colorTrials (2*SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda) Lambda := by
  simp [parameters,divide,literal,exponential,add,mul,SpinGlass.AlgorithmBudgets.edgeCutoff,
    SpinGlass.AlgorithmBudgets.colorTrials]

@[simp] theorem parameters_operations (q Lambda : ℝ) :
    (parameters q Lambda).operations =
      2*SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda+
      2*SpinGlass.AlgorithmBudgets.colorTrials (2*SpinGlass.AlgorithmBudgets.edgeCutoff q Lambda) Lambda+8 := by
  simp [parameters,divide,literal,exponential,add,mul,SpinGlass.AlgorithmBudgets.edgeCutoff,
    SpinGlass.AlgorithmBudgets.colorTrials]
  omega

structure Control where
  exact : Bool
  branchLimit : ℕ
  edgeLimit : ℕ
  trials : ℕ
  operations : ℕ

/-- Algorithm 4's complete SK control: cache the budget, test the exact branch,
then perform the first crossing and both actual ceiling computations. -/
def control (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ) : Control :=
  let lam := logarithm (divide (literal (SKAlgorithm.errorConstant a B rho)) (literal u))
  if N < Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho) ∨
      Cutoffs.nu 1 (SKAlgorithm.scale B rho) (SKAlgorithm.c1 a B rho)*N ≤ lam.value then
    ⟨true,N,0,1,lam.operations+4⟩
  else
    let scan := CutoffExecution.cutoffSearch 1 1 (SKAlgorithm.scale B rho) N lam.value
    let params := parameters (SKAlgorithm.q a B) lam.value
    ⟨false,scan.found.getD 1-1,params.edgeLimit,params.trials,
      lam.operations+scan.operations+params.operations+7⟩

theorem control_exact (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ)
    (hex : SKAlgorithm.exactBranch N a B rho u) :
    control N a B rho u = ⟨true,N,0,1,6⟩ := by
  unfold control
  have hc : N < Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho) ∨
      Cutoffs.nu 1 (SKAlgorithm.scale B rho) (SKAlgorithm.c1 a B rho)*N ≤
        Real.log (SKAlgorithm.errorConstant a B rho/u) := hex
  simp [logarithm,divide,literal,hc]

theorem control_truncated (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ)
    (hex : ¬SKAlgorithm.exactBranch N a B rho u) :
    (control N a B rho u).exact = false ∧
    (control N a B rho u).branchLimit = SKAlgorithm.branchCutoff N a B rho u ∧
    (control N a B rho u).edgeLimit = SKAlgorithm.edgeLimit a B rho u ∧
    (control N a B rho u).trials = SKAlgorithm.trials a B rho u := by
  unfold control
  have hc : ¬(N < Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho) ∨
      Cutoffs.nu 1 (SKAlgorithm.scale B rho) (SKAlgorithm.c1 a B rho)*N ≤
        Real.log (SKAlgorithm.errorConstant a B rho/u)) := hex
  simp [logarithm,divide,literal,hc,parameters_edgeLimit,parameters_trials,
    CutoffExecution.cutoffSearch_found _ _ _ _ _ (SKAlgorithm.scale_pos B rho),
    SKAlgorithm.branchCutoff,SKAlgorithm.selectedSize,SKAlgorithm.budget,
    SpinGlass.AlgorithmBudgets.logBudget,SKAlgorithm.edgeLimit,SKAlgorithm.trials]

theorem control_operations (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ) :
    (control N a B rho u).operations ≤
      10*N+2*SKAlgorithm.edgeLimit a B rho u+2*SKAlgorithm.trials a B rho u+20 := by
  classical
  by_cases hex : SKAlgorithm.exactBranch N a B rho u
  · rw [control_exact N a B rho u hex]
    dsimp only
    omega
  · have hc : ¬(N < Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho) ∨
        Cutoffs.nu 1 (SKAlgorithm.scale B rho) (SKAlgorithm.c1 a B rho)*N ≤
          Real.log (SKAlgorithm.errorConstant a B rho/u)) := hex
    have hs := CutoffExecution.cutoffSearch_operations (kapMin := 1) (kap := 1)
      (Lambda := SKAlgorithm.budget a B rho u) (N := N) (SKAlgorithm.scale_pos B rho)
    dsimp only [control,logarithm,divide,literal]
    rw [if_neg hc]
    simp only [parameters_operations]
    change _ ≤ 10*N+2*SpinGlass.AlgorithmBudgets.edgeCutoff (SKAlgorithm.q a B) (SKAlgorithm.budget a B rho u)+
      2*SpinGlass.AlgorithmBudgets.colorTrials (2*SpinGlass.AlgorithmBudgets.edgeCutoff (SKAlgorithm.q a B) (SKAlgorithm.budget a B rho u)) (SKAlgorithm.budget a B rho u)+20
    dsimp only [SKAlgorithm.budget,SpinGlass.AlgorithmBudgets.logBudget] at hs ⊢
    omega

end Manuscript.SKControl
