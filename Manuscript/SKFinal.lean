import Manuscript.SKExecutionCost
import Manuscript.SKTheorem
import Manuscript.LogRuntime

/-! The fully counted randomized SK instance of Theorem 1.1. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKFinal
open MeasureTheory SpinGlass.Disorder SpinGlass.ArithmeticEvaluation
open Manuscript.Model Manuscript.MixedThreshold Manuscript.InputPreparation

 theorem constant_pos (a : ℕ → ℝ) (ha : a 2=1) {B rho : ℝ}
    (hB : 0 < B) (hB1 : B < 1) : 0 < LogApprox.constant {2} a B rho := by
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  have hc := LogApprox.constant_ge_one {2} a (by simp) (by simpa [ha]) (by simp)
    (rho := rho) hB hBT
  linarith

/-- This is only dependent-type transport of a saved color tape. The equality
proof is erased; all numerical cutoffs are computed by the counted control. -/
def budgetColors (N : ℕ) (a : ℕ → ℝ) (B rho epsilon delta : ℝ)
    (hC : 0 < LogApprox.constant {2} a B rho) (hd : 0 < delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) :
    SKAlgorithm.Colors N a B rho
      (prepareBudget (LogApprox.constant {2} a B rho) delta epsilon (LogApprox.exponent {2} a B)).u :=
  cast (congrArg (SKAlgorithm.Colors N a B rho) (prepareBudget_u hC hd)).symm χ

theorem evaluate_cast {N : ℕ} (a : ℕ → ℝ) (B rho : ℝ) {u v : ℝ}
    (hu : u=v) (χ : SKAlgorithm.Colors N a B rho v) (input : PreparedInput N {2}) :
    SKPhysicalExecution.evaluate N a B rho u
      (cast (congrArg (SKAlgorithm.Colors N a B rho) hu).symm χ) input =
        SKPhysicalExecution.evaluate N a B rho v χ input := by
  subst u
  rfl

/-- Algorithm 1 computes its accuracy budget, prepares the physical input
once, executes the counted SK branch, and performs the final test and log. -/
def execute (N : ℕ) (a : ℕ → ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0 < LogApprox.constant {2} a B rho) (hd : 0 < delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ) : Computation :=
  let budgets := prepareBudget (LogApprox.constant {2} a B rho) delta epsilon (LogApprox.exponent {2} a B)
  let input := prepareInput N {2} a beta h J
  let result := SKPhysicalExecution.evaluate N a B rho budgets.u
    (budgetColors N a B rho epsilon delta hC hd χ) input
  let correction : Computation :=
    ⟨result.value,(SKControl.control N a B rho budgets.u).operations+result.operations+1⟩
  let output := LogApprox.finish input correction
  ⟨output.value,budgets.operations+output.operations⟩

 theorem execute_value {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ) (ha : a 2=1)
    {B rho beta h epsilon delta : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1)
    (hC : 0 < LogApprox.constant {2} a B rho)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ) :
    (execute N a B rho beta h epsilon delta hC hd χ J).value =
      SKTheorem.approximation N a B rho beta h epsilon delta χ J := by
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  have hu := LogApprox.budgets_range {2} a (by simp) (by simpa [ha]) (by simp)
    (rho := rho) hB hBT he he1 hd hd1
  have hcast := evaluate_cast a B rho
    (prepareBudget_u (epsilon := epsilon) (s := LogApprox.exponent {2} a B) hC hd) χ
    (prepareInput N {2} a beta h J)
  simp only [execute,LogApprox.finish_value,budgetColors]
  rw [hcast,prepareInput_logPrefactor hN]
  change SpinGlass.logOutput (logBase N {2} a beta h J)
    (SKPhysicalExecution.execute N a B rho beta h
      (LogApprox.mseBudget {2} a B rho epsilon delta) χ J).value = _
  rw [SKPhysicalExecution.execute_value hN a ha hB hB1 hu.2.2.1 (by linarith [hu.2.2.2])]
  rfl

 theorem execute_operations (N : ℕ) (a : ℕ → ℝ) (B rho beta h epsilon delta : ℝ)
    (hC : 0 < LogApprox.constant {2} a B rho) (hd : 0 < delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ) :
    (execute N a B rho beta h epsilon delta hC hd χ J).operations ≤
      (SKPhysicalExecution.execute N a B rho beta h
        (LogApprox.mseBudget {2} a B rho epsilon delta) χ J).operations+13 := by
  let input := prepareInput N {2} a beta h J
  let u := LogApprox.mseBudget {2} a B rho epsilon delta
  let result := SKPhysicalExecution.evaluate N a B rho u χ input
  have hh := LogApprox.finish_operations input
    (⟨result.value,(SKControl.control N a B rho u).operations+result.operations+1⟩ : Computation)
  have hcast := evaluate_cast a B rho
    (prepareBudget_u (epsilon := epsilon) (s := LogApprox.exponent {2} a B) hC hd) χ input
  simp only [execute,budgetColors]
  rw [hcast]
  simp only [prepareBudget_u hC hd,prepareBudget_operations]
  change 10+(LogApprox.finish input
    ⟨result.value,(SKControl.control N a B rho u).operations+result.operations+1⟩).operations ≤
      input.operations+(SKControl.control N a B rho u).operations+result.operations+1+13
  dsimp only at hh
  omega

 theorem colorLaw_probability (N : ℕ) (a : ℕ → ℝ) (ha : a 2=1)
    {B rho epsilon delta : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    IsProbabilityMeasure (SKTheorem.colorLaw N a B rho epsilon delta) := by
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  have hu := LogApprox.budgets_range {2} a (by simp) (by simpa [ha]) (by simp)
    (rho := rho) hB hBT he he1 hd hd1
  have hL := SKAlgorithm.edgeLimit_pos a ha (rho := rho) hB hB1 hu.2.2.1 (by linarith [hu.2.2.2])
  letI : Nonempty (Fin (2*SKAlgorithm.edgeLimit a B rho (LogApprox.mseBudget {2} a B rho epsilon delta))) :=
    ⟨⟨0,by omega⟩⟩
  unfold SKTheorem.colorLaw SKAlgorithm.colorLaw
  infer_instance

 theorem accuracy (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℝ) (ha : a 2=1)
    {beta B h rho epsilon delta : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hB1 : B < 1)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)))
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    ((SKTheorem.colorLaw N a B rho epsilon delta).prod (iidLaw μ)).real
      {χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) | epsilon <
        |(execute N a B rho beta h epsilon delta (constant_pos a ha hB hB1) hd χJ.1 χJ.2).value-
          Real.log (Model.partition N {2} a beta h χJ.2)|} ≤
      delta+OriginalLawLowerTail.tau μ N {2} a B (theta {2} a B) := by
  simp_rw [execute_value (by omega : 0<N) a ha hB hB1 he he1 hd hd1]
  exact SKTheorem.accuracy μ hμ hunit N hN a ha hbeta hbetaB hB hB1 hfield he he1 hd hd1

 theorem polynomial (a : ℕ → ℝ) (ha : a 2=1) {B rho : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ (beta h epsilon delta : ℝ),
      0 < epsilon → epsilon < 1 → ∀ (hd : 0 < delta), delta < 1 →
      ∀ (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ),
      ((execute N a B rho beta h epsilon delta (constant_pos a ha hB hB1) hd χ J).operations : ℝ) ≤
        C*(N : ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨K,hK,hgraph⟩ := SKExecutionCost.execute_polynomial a ha (rho := rho) hB hB1
  let C := LogRuntime.countingConstant (K+13) (LogApprox.constant {2} a B rho)
    (LogApprox.exponent {2} a B) K
  refine ⟨C,LogRuntime.countingConstant_pos _ _ _ _,?_⟩
  intro N hN beta h epsilon delta he he1 hd hd1 χ J
  have hC := constant_pos a ha (rho := rho) hB hB1
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  obtain ⟨hz,hz1,hu,hu1⟩ := LogApprox.budgets_range {2} a (by simp) (by simpa [ha]) (by simp)
    (rho := rho) hB hBT he he1 hd hd1
  have hg := hgraph N hN beta h (LogApprox.mseBudget {2} a B rho epsilon delta) hu (by linarith) χ J
  have hop := execute_operations N a B rho beta h epsilon delta hC hd χ J
  have hopR : ((execute N a B rho beta h epsilon delta hC hd χ J).operations : ℝ) ≤
      (SKPhysicalExecution.execute N a B rho beta h
        (LogApprox.mseBudget {2} a B rho epsilon delta) χ J).operations+13 := by exact_mod_cast hop
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
  have hNp : 1 ≤ (N : ℝ)^K := Real.one_le_rpow hN1 hK.le
  have huPow : 1 ≤ (LogApprox.mseBudget {2} a B rho epsilon delta)^(-K) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu (by linarith) (by linarith)
  have hp1 := one_le_mul_of_one_le_of_one_le hNp huPow
  calc
    _ ≤ (K+13)*(N : ℝ)^K*(LogApprox.mseBudget {2} a B rho epsilon delta)^(-K) := by nlinarith
    _ ≤ _ := LogRuntime.budget_polynomial (by linarith) hC (by omega) hd hd1.le he he1.le

/-- Complete SK Theorem 1.1 endpoint, with one fixed polynomial constant and
all original-law analytic, graphical, estimator, and runtime bounds proved. -/
theorem end_to_end (a : ℕ → ℝ) (ha : a 2=1) {B rho : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (N : ℕ), 2 ≤ N →
      ∀ (beta h epsilon delta : ℝ), 0 ≤ beta → beta ≤ B →
      |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) →
      0 < epsilon → epsilon < 1 → ∀ (hd : 0 < delta), delta < 1 →
      (((SKTheorem.colorLaw N a B rho epsilon delta).prod (iidLaw μ)).real
        {χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) | epsilon <
          |(execute N a B rho beta h epsilon delta (constant_pos a ha hB hB1) hd χJ.1 χJ.2).value-
            Real.log (Model.partition N {2} a beta h χJ.2)|} ≤
        delta+OriginalLawLowerTail.tau μ N {2} a B (theta {2} a B)) ∧
      ∀ (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ),
        ((execute N a B rho beta h epsilon delta (constant_pos a ha hB hB1) hd χ J).operations : ℝ) ≤
          C*(N : ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨C,hC,hcost⟩ := polynomial a ha (rho := rho) hB hB1
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N hN beta h epsilon delta hbeta hbetaB hfield he he1 hd hd1
  letI : IsProbabilityMeasure μ := hprob
  exact ⟨accuracy μ hμ hunit N hN a ha hbeta hbetaB hB hB1 hfield he he1 hd hd1,
    hcost N hN beta h epsilon delta he he1 hd hd1⟩

end Manuscript.SKFinal
