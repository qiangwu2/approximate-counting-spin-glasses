import Manuscript.SKChargeProjection
import Manuscript.SKFinal

/-!
# The manuscript's projected SK output and its original-law guarantee

This module uses the same concrete cutoff control, prepared input, exact fallback,
accuracy budget, saved color tape, positivity test, and logarithmic correction as
`SKFinal.execute`.  In the truncated branch it calls the independently defined
L-charge/L-iteration projected estimator from `SKChargeProjection`.

The output equality and failure bound below have no evaluator-correctness,
mean-square-error, or desired-output-equality premise.  This is an output and
probability theorem; it does not attach an operation counter to this new program.
-/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKProjectedOutput
open MeasureTheory SpinGlass.Disorder SpinGlass.ArithmeticEvaluation
open Manuscript.Model Manuscript.MixedThreshold Manuscript.InputPreparation
attribute [local instance] Classical.propDecidable

/-- GraphApprox on a prepared input, using the original saved cutoff control.
Only the truncated branch is replaced by the charge-L projected evaluator. -/
def evaluate (N : ℕ) (a : ℕ → ℝ) (B rho u h : ℝ)
    (χ : SKAlgorithm.Colors N a B rho u) (input : PreparedInput N {2}) : ℝ :=
  let ctl := SKControl.control N a B rho u
  if hc : ctl.exact=true then
    (SupportExecution.supportSum Subtype.val Finset.univ
      (cachedFieldWeight input) (cachedWeight input) N).value
  else
    have hex : ¬SKAlgorithm.exactBranch N a B rho u := by
      intro he
      have hh := SKControl.control_exact N a B rho u he
      exact hc (congrArg SKControl.Control.exact hh)
    have hh := SKControl.control_truncated N a B rho u hex
    SKChargeProjection.projectedAlgorithm ctl.branchLimit ctl.edgeLimit ctl.trials
      (SKPhysicalExecution.castColors hh.2.2.1 hh.2.2.2 χ) h
      (SKPhysicalExecution.preparedWeight input)

/-- For actual prepared physical inputs, the projected GraphApprox value equals
that of the existing counted implementation, including its exact fallback. -/
theorem evaluate_prepared (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    evaluate N a B rho u h χ (prepareInput N {2} a beta h J) =
      (SKPhysicalExecution.evaluate N a B rho u χ
        (prepareInput N {2} a beta h J)).value := by
  unfold evaluate SKPhysicalExecution.evaluate
  dsimp only
  split
  · rfl
  · rw [SKChargeProjection.projectedAlgorithm_eq_generated]
    rfl

/-- The projected manuscript GraphApprox on original disorder-array inputs. -/
def graphApprox (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) : ℝ :=
  evaluate N a B rho u h χ (prepareInput N {2} a beta h J)

theorem graphApprox_eq_execute (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    graphApprox N a B rho beta h u χ J =
      (SKPhysicalExecution.execute N a B rho beta h u χ J).value := by
  exact evaluate_prepared N a B rho beta h u χ J

/-- The complete projected logarithmic output. The same computed accuracy budget
and color-tape transport are used, and `logOutput` includes the nonpositive
correction fallback exactly as in the original LogApprox program. -/
def output (N : ℕ) (a : ℕ → ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0 < LogApprox.constant {2} a B rho) (hd : 0 < delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ) : ℝ :=
  let budgets := prepareBudget (LogApprox.constant {2} a B rho) delta epsilon
    (LogApprox.exponent {2} a B)
  let input := prepareInput N {2} a beta h J
  let correction := evaluate N a B rho budgets.u h
    (SKFinal.budgetColors N a B rho epsilon delta hC hd χ) input
  SpinGlass.logOutput input.logPrefactor correction

/-- Pointwise equality for every real disorder input and every saved color tape.
No probabilistic or asymptotic assumption is needed for this program identity. -/
theorem output_eq_execute (N : ℕ) (a : ℕ → ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0 < LogApprox.constant {2} a B rho) (hd : 0 < delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ) :
    output N a B rho beta h epsilon delta hC hd χ J =
      (SKFinal.execute N a B rho beta h epsilon delta hC hd χ J).value := by
  simp only [output, SKFinal.execute, LogApprox.finish_value]
  rw [evaluate_prepared]

/-- The original finite-size failure guarantee for the projected manuscript
program. All graphical, analytic, and evaluator facts are discharged by the
proved output identity and the existing end-to-end theorem. -/
theorem accuracy (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℝ) (ha : a 2=1)
    {beta B h rho epsilon delta : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hB1 : B < 1)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)))
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    ((SKTheorem.colorLaw N a B rho epsilon delta).prod (iidLaw μ)).real
      {χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) | epsilon <
        |output N a B rho beta h epsilon delta (SKFinal.constant_pos a ha hB hB1) hd χJ.1 χJ.2-
          Real.log (Model.partition N {2} a beta h χJ.2)|} ≤
      delta+OriginalLawLowerTail.tau μ N {2} a B (theta {2} a B) := by
  simp_rw [output_eq_execute]
  exact SKFinal.accuracy μ hμ hunit N hN a ha hbeta hbetaB hB hB1 hfield he he1 hd hd1

end Manuscript.SKProjectedOutput
