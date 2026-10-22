import Manuscript.SKControl

noncomputable section
namespace Manuscript.SKControlDimension

private theorem floor_le (r : ℝ) (n : ℕ) : (CutoffExecution.boundedFloor r n).value≤n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [CutoffExecution.boundedFloor];split_ifs <;> dsimp <;> omega

private theorem scan_bound (kap A : ℝ) (N : ℕ) (lam : ℝ) (fuel : ℕ) :
    ∀ start,1≤start → (CutoffExecution.scan kap A N lam start fuel).found.getD 1≤start+fuel := by
  induction fuel with
  | zero => intro start hs;simpa [CutoffExecution.scan] using hs
  | succ fuel ih =>
    intro start hs
    simp only [CutoffExecution.scan]
    split_ifs
    · simp
    · have hh:=ih (start+1) (by omega);dsimp only;omega

theorem control_le (N : ℕ) (a : ℕ→ℝ) (B rho u : ℝ) :
    (SKControl.control N a B rho u).branchLimit≤N := by
  unfold SKControl.control
  dsimp only
  split_ifs
  · rfl
  · unfold CutoffExecution.cutoffSearch
    dsimp only
    have hs:=scan_bound 1 (SKAlgorithm.scale B rho) N
      (Real.log (SKAlgorithm.errorConstant a B rho/u))
      (CutoffExecution.boundedFloor (Cutoffs.gamma 1 (SKAlgorithm.scale B rho)*N) N).value 1 (by omega)
    have hf:=floor_le (Cutoffs.gamma 1 (SKAlgorithm.scale B rho)*N) N
    simpa only [InputPreparation.logarithm,InputPreparation.divide,
      SpinGlass.ArithmeticEvaluation.literal] using (show
        (CutoffExecution.scan 1 (SKAlgorithm.scale B rho) N
          (Real.log (SKAlgorithm.errorConstant a B rho/u)) 1
          (CutoffExecution.boundedFloor (Cutoffs.gamma 1 (SKAlgorithm.scale B rho)*N) N).value).found.getD 1-1≤N by omega)

theorem truncated_le (N : ℕ) (a : ℕ→ℝ) (B rho u : ℝ)
    (hex : ¬SKAlgorithm.exactBranch N a B rho u) : SKAlgorithm.branchCutoff N a B rho u≤N := by
  rw [←(SKControl.control_truncated N a B rho u hex).2.1]
  exact control_le N a B rho u

end Manuscript.SKControlDimension
