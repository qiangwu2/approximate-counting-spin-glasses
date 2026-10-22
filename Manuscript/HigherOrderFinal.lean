import Manuscript.HigherOrderTheorem
import Manuscript.HigherOrderExecution
import Manuscript.LogRuntime

/-! The fully counted deterministic higher-order instance of Theorem 1.1.
Input preparation is shared by GraphApprox and the final logarithmic output. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.HigherOrderFinal
open MeasureTheory SpinGlass.Disorder SpinGlass.ArithmeticEvaluation
open Manuscript.Model Manuscript.MixedThreshold Manuscript.InputPreparation

/-- Algorithm 1: compute its requested budget, prepare the input once, run the
counted deterministic branch, then perform the final positivity test and log. -/
def execute (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h epsilon delta : ℝ) (J : Edge N P → ℝ) : Computation :=
  let budgets := prepareBudget (LogApprox.constant P a B rho) delta epsilon (LogApprox.exponent P a B)
  let input := prepareInput N P a beta h J
  let ctl := HigherOrderExecution.control N pmax P a B rho pmin h budgets.u input.field.mean
  let localResult := SupportExecution.supportSum Subtype.val Finset.univ
    (cachedFieldWeight input) (cachedWeight input) ctl.cutoff
  let correction : Computation := ⟨localResult.value,ctl.operations+localResult.operations⟩
  let result := LogApprox.finish input correction
  ⟨result.value,budgets.operations+result.operations⟩

theorem execute_value {N : ℕ} (hN : 0 < N) (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h epsilon delta : ℝ) (hp : 0 < pmin)
    (hC : 0 < LogApprox.constant P a B rho) (hd : 0 < delta) (J : Edge N P → ℝ) :
    (execute N pmax P a B rho pmin beta h epsilon delta J).value =
      HigherOrderTheorem.approximation N pmax P a B rho pmin beta h epsilon delta J := by
  simp only [execute,LogApprox.finish_value,prepareBudget_u hC hd]
  rw [prepareInput_logPrefactor hN]
  change SpinGlass.logOutput (logBase N P a beta h J)
    (HigherOrderExecution.execute N pmax P a B rho pmin beta h
      (LogApprox.mseBudget P a B rho epsilon delta) J).value = _
  rw [HigherOrderExecution.execute_value hN pmax P a B rho pmin beta h _ hp J]
  rfl

/-- Exactly one input preparation is charged; the additional budget and final
logarithm use at most thirteen operations. -/
theorem execute_operations (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h epsilon delta : ℝ)
    (hC : 0 < LogApprox.constant P a B rho) (hd : 0 < delta) (J : Edge N P → ℝ) :
    (execute N pmax P a B rho pmin beta h epsilon delta J).operations ≤
      (HigherOrderExecution.execute N pmax P a B rho pmin beta h
        (LogApprox.mseBudget P a B rho epsilon delta) J).operations+13 := by
  let input := prepareInput N P a beta h J
  let u := LogApprox.mseBudget P a B rho epsilon delta
  let ctl := HigherOrderExecution.control N pmax P a B rho pmin h u input.field.mean
  let result := SupportExecution.supportSum Subtype.val Finset.univ
    (cachedFieldWeight input) (cachedWeight input) ctl.cutoff
  have hh := LogApprox.finish_operations input
    (⟨result.value,ctl.operations+result.operations⟩ : Computation)
  simp only [execute,prepareBudget_operations,prepareBudget_u hC hd]
  change 10+(LogApprox.finish input ⟨result.value,ctl.operations+result.operations⟩).operations ≤
    input.operations+ctl.operations+result.operations+13
  dsimp only at hh
  omega

/-- Accuracy for the actual counted output, under the manuscript's original
symmetric independent disorder assumptions. -/
theorem accuracy (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (pmin : ℝ) (hpmin : 3 ≤ pmin)
    (horders : ∀ p ∈ P, pmin ≤ (p : ℝ)) (pmax : ℕ)
    (hmax : ∀ p ∈ P, p ≤ pmax) (hpN : ∀ p ∈ P, p ≤ N)
    {beta B h rho epsilon delta : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)))
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    (iidLaw μ).real {J | epsilon <
      |(execute N pmax P a B rho pmin beta h epsilon delta J).value -
        Real.log (Model.partition N P a beta h J)|} ≤
      delta + OriginalLawLowerTail.tau μ N P a B (theta P a B) := by
  have hp : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have hh := hpmin.trans (horders p hp)
    have h3 : 3 ≤ p := by exact_mod_cast hh
    omega
  have hN : 0 < N := by
    obtain ⟨p,hpP⟩ := hP
    have := hp p hpP
    have := hpN p hpP
    omega
  have hC := LogApprox.constant_ge_one P a hP ha hp (rho := rho) hB hBT
  simp_rw [execute_value hN pmax P a B rho pmin beta h epsilon delta (by linarith) (by linarith) hd]
  exact HigherOrderTheorem.accuracy μ hμ hunit N P a hP ha pmin hpmin horders pmax hmax hpN
    hbeta hbetaB hB hBT hfield he he1 hd hd1

/-- The actual shared computation has the common polynomial exponent stated
in Theorem 1.1, uniformly over every finite input array. -/
theorem polynomial (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (pmin : ℝ) (hpmin : 3 ≤ pmin)
    (horders : ∀ p ∈ P, pmin ≤ (p : ℝ)) (pmax : ℕ)
    (hmax : ∀ p ∈ P, p ≤ pmax) {B rho : ℝ} (hB : 0 < B) (hBT : B < betaF P a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → (∀ p ∈ P, p ≤ N) →
      ∀ (beta h epsilon delta : ℝ), |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) →
      0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 → ∀ J : Edge N P → ℝ,
      ((execute N pmax P a B rho pmin beta h epsilon delta J).operations : ℝ) ≤
        C*(N : ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨K,hK,hgraph⟩ := HigherOrderExecution.execute_polynomial P a hP ha pmin hpmin horders
    pmax hmax (rho := rho) hB hBT
  let C := LogRuntime.countingConstant (K+13) (LogApprox.constant P a B rho)
    (LogApprox.exponent P a B) K
  refine ⟨C,LogRuntime.countingConstant_pos _ _ _ _,?_⟩
  intro N hN hpN beta h epsilon delta hfield he he1 hd hd1 J
  have hp : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have hh := hpmin.trans (horders p hp)
    have h3 : 3 ≤ p := by exact_mod_cast hh
    omega
  have hC := LogApprox.constant_ge_one P a hP ha hp (rho := rho) hB hBT
  have hC0 : 0 < LogApprox.constant P a B rho := by linarith
  obtain ⟨hz,hz1,hu,hu1⟩ := LogApprox.budgets_range P a hP ha hp (rho := rho) hB hBT he he1 hd hd1
  have hg := hgraph N hN hpN beta h (LogApprox.mseBudget P a B rho epsilon delta) hfield hu (by linarith) J
  have hop := execute_operations N pmax P a B rho pmin beta h epsilon delta hC0 hd J
  have hopR : ((execute N pmax P a B rho pmin beta h epsilon delta J).operations : ℝ) ≤
      (HigherOrderExecution.execute N pmax P a B rho pmin beta h
        (LogApprox.mseBudget P a B rho epsilon delta) J).operations+13 := by exact_mod_cast hop
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : 1 ≤ (N : ℝ)^K := Real.one_le_rpow hN1 hK.le
  have huPow : 1 ≤ (LogApprox.mseBudget P a B rho epsilon delta)^(-K) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu (by linarith) (by linarith)
  have hp1 := one_le_mul_of_one_le_of_one_le hNp huPow
  calc
    _ ≤ (K+13)*(N : ℝ)^K*(LogApprox.mseBudget P a B rho epsilon delta)^(-K) := by
      nlinarith
    _ ≤ _ := LogRuntime.budget_polynomial (by linarith) hC0 (by omega) hd hd1.le he he1.le

/-- Complete deterministic higher-order Theorem 1.1 endpoint: one fixed
polynomial constant simultaneously accompanies the exact probability bound.
There are no graph-mass, MSE, lower-tail or runtime estimates as assumptions. -/
theorem end_to_end (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (pmin : ℝ) (hpmin : 3 ≤ pmin)
    (horders : ∀ p ∈ P, pmin ≤ (p : ℝ)) (pmax : ℕ)
    (hmax : ∀ p ∈ P, p ≤ pmax) {B rho : ℝ} (hB : 0 < B) (hBT : B < betaF P a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (N : ℕ), (∀ p ∈ P, p ≤ N) →
      ∀ (beta h epsilon delta : ℝ), 0 ≤ beta → beta ≤ B →
      |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) →
      0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ((iidLaw μ).real {J | epsilon <
        |(execute N pmax P a B rho pmin beta h epsilon delta J).value -
          Real.log (Model.partition N P a beta h J)|} ≤
        delta + OriginalLawLowerTail.tau μ N P a B (theta P a B)) ∧
      ∀ J : Edge N P → ℝ,
        ((execute N pmax P a B rho pmin beta h epsilon delta J).operations : ℝ) ≤
          C*(N : ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨C,hC,hcost⟩ := polynomial P a hP ha pmin hpmin horders pmax hmax (rho := rho) hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N hpN beta h epsilon delta hbeta hbetaB hfield he he1 hd hd1
  letI : IsProbabilityMeasure μ := hprob
  have hN : 0 < N := by
    obtain ⟨p,hpP⟩ := hP
    have h3 := hpmin.trans (horders p hpP)
    have h3' : 3 ≤ p := by exact_mod_cast h3
    have := hpN p hpP
    omega
  exact ⟨accuracy μ hμ hunit N P a hP ha pmin hpmin horders pmax hmax hpN
    hbeta hbetaB hB hBT hfield he he1 hd hd1,
    hcost N hN hpN beta h epsilon delta hfield he he1 hd hd1⟩

/-- The manuscript's canonical smallest and largest active interaction orders. -/
def canonicalExecute (N : ℕ) (P : Finset ℕ) (hP : P.Nonempty) (a : ℕ → ℝ)
    (B rho beta h epsilon delta : ℝ) (J : Edge N P → ℝ) : Computation :=
  execute N (P.max' hP) P a B rho (P.min' hP) beta h epsilon delta J

/-- Canonical higher-order Theorem 1.1: the only order hypothesis is that every
active order is at least three, and the system size is at least their maximum. -/
theorem canonical_end_to_end (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 3 ≤ p)
    {B rho : ℝ} (hB : 0 < B) (hBT : B < betaF P a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (N : ℕ), P.max' hP ≤ N →
      ∀ (beta h epsilon delta : ℝ), 0 ≤ beta → beta ≤ B →
      |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) →
      0 < epsilon → epsilon < 1 → 0 < delta → delta < 1 →
      ((iidLaw μ).real {J | epsilon <
        |(canonicalExecute N P hP a B rho beta h epsilon delta J).value -
          Real.log (Model.partition N P a beta h J)|} ≤
        delta + OriginalLawLowerTail.tau μ N P a B (theta P a B)) ∧
      ∀ J : Edge N P → ℝ,
        ((canonicalExecute N P hP a B rho beta h epsilon delta J).operations : ℝ) ≤
          C*(N : ℝ)^C*epsilon^(-C)*delta^(-C) := by
  have hpmin : (3 : ℝ) ≤ P.min' hP := by
    exact_mod_cast hp _ (Finset.min'_mem P hP)
  have horders : ∀ p ∈ P, (P.min' hP : ℝ) ≤ (p : ℝ) := by
    intro p hpP
    exact_mod_cast Finset.min'_le P p hpP
  obtain ⟨C,hC,hmain⟩ := end_to_end P a hP ha (P.min' hP) hpmin horders
    (P.max' hP) (fun p hpP => Finset.le_max' P p hpP) (rho := rho) hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N hN beta h epsilon delta hbeta hbetaB hfield he he1 hd hd1
  exact hmain μ hprob hμ hunit N (fun p hpP => (Finset.le_max' P p hpP).trans hN)
    beta h epsilon delta hbeta hbetaB hfield he he1 hd hd1

end Manuscript.HigherOrderFinal
