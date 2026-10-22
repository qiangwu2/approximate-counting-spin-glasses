import Manuscript.SKGlobalLowerBound
import Manuscript.RestrictedSupportLowerBound

noncomputable section
open scoped BigOperators
namespace Manuscript.SKFinalLowerBound
open SpinGlass.ArithmeticEvaluation InputPreparation Model

theorem output_value {N : ℕ} (hN : 0<N) (a : ℕ→ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0<LogApprox.constant {2} a B rho) (hd : 0<delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2}→ℝ) :
    (SKFinal.execute N a B rho beta h epsilon delta hC hd χ J).value=
      SpinGlass.logOutput (logBase N {2} a beta h J)
        (SKPhysicalExecution.evaluate N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta) χ
          (prepareInput N {2} a beta h J)).value := by
  have hcast := SKFinal.evaluate_cast a B rho
    (prepareBudget_u (epsilon:=epsilon) (s:=LogApprox.exponent {2} a B) hC hd) χ
    (prepareInput N {2} a beta h J)
  simp only [SKFinal.execute,SKFinal.budgetColors,LogApprox.finish_value]
  rw [hcast,prepareInput_logPrefactor hN]
  rfl

theorem components (N : ℕ) (a : ℕ→ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0<LogApprox.constant {2} a B rho) (hd : 0<delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2}→ℝ) :
    (prepareInput N {2} a beta h J).operations+
      (SKControl.control N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta)).operations+
      (SKPhysicalExecution.evaluate N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta) χ
        (prepareInput N {2} a beta h J)).operations≤
      (SKFinal.execute N a B rho beta h epsilon delta hC hd χ J).operations := by
  have hcast := SKFinal.evaluate_cast a B rho
    (prepareBudget_u (epsilon:=epsilon) (s:=LogApprox.exponent {2} a B) hC hd) χ
    (prepareInput N {2} a beta h J)
  simp only [SKFinal.execute,SKFinal.budgetColors]
  rw [hcast]
  simp only [prepareBudget_u hC hd,LogApprox.finish,LogApprox.mseBudget]
  omega

theorem physical_count (N : ℕ) (a : ℕ→ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0<LogApprox.constant {2} a B rho) (hd : 0<delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2}→ℝ) :
    Fintype.card (Edge N {2})≤(SKFinal.execute N a B rho beta h epsilon delta hC hd χ J).operations := by
  have hp := prepareInput_operations N {2} a beta h J
  have hc := components N a B rho beta h epsilon delta hC hd χ J
  omega

theorem estimator (N : ℕ) (a : ℕ→ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0<LogApprox.constant {2} a B rho) (hd : 0<delta)
    (hex : ¬SKAlgorithm.exactBranch N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta))
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2}→ℝ) :
    (SKGeneratedExecution.estimator
      (SKAlgorithm.branchCutoff N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta))
      (SKAlgorithm.edgeLimit a B rho (LogApprox.mseBudget {2} a B rho epsilon delta))
      (SKAlgorithm.trials a B rho (LogApprox.mseBudget {2} a B rho epsilon delta)) χ
      (prepareInput N {2} a beta h J).field.mean
      (SKPhysicalExecution.preparedWeight (prepareInput N {2} a beta h J))).operations≤
      (SKFinal.execute N a B rho beta h epsilon delta hC hd χ J).operations := by
  have hc := components N a B rho beta h epsilon delta hC hd χ J
  rw [SKPhysicalExecution.evaluate_truncated _ _ _ _ _ hex] at hc
  omega

theorem exact_enumeration (N : ℕ) (a : ℕ→ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0<LogApprox.constant {2} a B rho) (hd : 0<delta)
    (hex : SKAlgorithm.exactBranch N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta))
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2}→ℝ) :
    (∑j∈Finset.range (N+1),N.choose j*2^j)≤
      ((SKFinal.execute N a B rho beta h epsilon delta hC hd χ J).operations+1)^2 := by
  have hc := components N a B rho beta h epsilon delta hC hd χ J
  rw [SKPhysicalExecution.evaluate_exact _ _ _ _ _ hex] at hc
  have hw := RestrictedSupportLowerBound.weighted_le_operations_square
    (Subtype.val : Edge N {2}→Finset (Fin N)) Finset.univ
    (cachedFieldWeight (prepareInput N {2} a beta h J))
    (cachedWeight (prepareInput N {2} a beta h J)) (k:=N) (by simp)
  simp only [Fintype.card_fin] at hw
  exact hw.trans (Nat.pow_le_pow_left (by omega) 2)

end Manuscript.SKFinalLowerBound
