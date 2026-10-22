import Manuscript.MainTheorem
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Explicit measurability of the actual final outputs and their events.
The proofs use the evaluator correctness identities and finite graph sums.
No disorder law, moment, tail, MSE, or runtime premise is needed. -/

noncomputable section
open scoped BigOperators
namespace Manuscript.OutputMeasurability
open MeasureTheory SpinGlass.Disorder Manuscript.Model

theorem partition_measurable (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ) :
    Measurable (Model.partition N P a beta h) := by
  unfold Model.partition Model.hamiltonian
  fun_prop

theorem logBase_measurable (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ) :
    Measurable (InputPreparation.logBase N P a beta h) := by
  unfold InputPreparation.logBase Model.coefficient
  fun_prop

theorem graphWeight_measurable {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (incidence : E → Finset V) (h : ℝ)
    (a : E → ℝ) (Γ : Finset E) :
    Measurable (DisorderOrthogonality.graphWeight incidence h a Γ) := by
  exact measurable_const.mul (continuous_monomial a Γ).measurable

theorem retained_measurable (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (k : ℕ) : Measurable (SupportDisorder.retained N P a beta h k) := by
  unfold SupportDisorder.retained
  apply Finset.measurable_sum
  intro Γ hΓ
  exact graphWeight_measurable _ _ _ _

theorem logOutput_measurable {Ω : Type*} [MeasurableSpace Ω] {base T : Ω → ℝ}
    (hb : Measurable base) (hT : Measurable T) :
    Measurable (fun ω => SpinGlass.logOutput (base ω) (T ω)) := by
  exact hb.add (hT.log.ite (measurableSet_lt measurable_const hT) measurable_const)

theorem higher_approximation_measurable (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h epsilon delta : ℝ) :
    Measurable (HigherOrderTheorem.approximation N pmax P a B rho pmin beta h epsilon delta) := by
  unfold HigherOrderTheorem.approximation
  simp_rw [HigherOrderAlgorithm.run_value]
  exact logOutput_measurable (logBase_measurable _ _ _ _ _) (retained_measurable _ _ _ _ _ _)

theorem higher_execute_measurable {N : ℕ} (hN : 0 < N) (pmax : ℕ)
    (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin beta h epsilon delta : ℝ)
    (hp : 0 < pmin) (hC : 0 < LogApprox.constant P a B rho) (hd : 0 < delta) :
    Measurable (fun J => (HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value) := by
  simp_rw [HigherOrderFinal.execute_value hN pmax P a B rho pmin beta h epsilon delta hp hC hd]
  exact higher_approximation_measurable _ _ _ _ _ _ _ _ _ _ _

theorem higher_canonical_execute_measurable {N : ℕ} (hN : 0 < N)
    (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 3 ≤ p)
    {B rho beta h epsilon delta : ℝ} (hB : 0 < B)
    (hBT : B < MixedThreshold.betaF P a) (hd : 0 < delta) :
    Measurable (fun J =>
      (HigherOrderFinal.canonicalExecute N P hP a B rho beta h epsilon delta J).value) := by
  have hpmin : (0 : ℝ) < P.min' hP := by
    have hh := hp _ (Finset.min'_mem P hP)
    exact_mod_cast (show 0 < P.min' hP by omega)
  have hc := LogApprox.constant_ge_one P a hP ha
    (fun p hpP => by have := hp p hpP; omega) (rho := rho) hB hBT
  exact higher_execute_measurable hN (P.max' hP) P a B rho (P.min' hP)
    beta h epsilon delta hpmin (by linarith) hd

theorem sk_estimator_measurable {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (incidence : E → Finset V) (edges : Finset E)
    (D L R : ℕ) (h : ℝ) (a : E → ℝ) :
    Measurable (fun χJ : SKColorEstimator.Colors V L R × (E → ℝ) =>
      SKColorEstimator.estimator incidence edges D L R h a χJ.1 χJ.2) := by
  unfold SKColorEstimator.estimator
  apply Finset.measurable_sum
  intro Γ hΓ
  exact ((measurable_of_countable (SKColorEstimator.coefficient incidence L R · Γ)).comp
    measurable_fst).mul ((graphWeight_measurable incidence h a Γ).comp measurable_snd)

theorem sk_run_measurable (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ) :
    Measurable (fun χJ : SKAlgorithm.Colors N a B rho u × (Edge N {2} → ℝ) =>
      SKAlgorithm.run N a B rho beta h u χJ.1 χJ.2) := by
  classical
  by_cases he : SKAlgorithm.exactBranch N a B rho u
  · simp only [SKAlgorithm.run, if_pos he, HigherOrderTail.evaluator_value]
    exact (retained_measurable _ _ _ _ _ _).comp measurable_snd
  · simp only [SKAlgorithm.run, if_neg he]
    exact sk_estimator_measurable _ _ _ _ _ _ _

theorem sk_approximation_measurable (N : ℕ) (a : ℕ → ℝ)
    (B rho beta h epsilon delta : ℝ) :
    Measurable (fun χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) =>
      SKTheorem.approximation N a B rho beta h epsilon delta χJ.1 χJ.2) := by
  exact logOutput_measurable ((logBase_measurable _ _ _ _ _).comp measurable_snd)
    (sk_run_measurable _ _ _ _ _ _ _)

theorem sk_execute_measurable {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ) (ha : a 2 = 1)
    {B rho beta h epsilon delta : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1)
    (hC : 0 < LogApprox.constant {2} a B rho) :
    Measurable (fun χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) =>
      (SKFinal.execute N a B rho beta h epsilon delta hC hd χJ.1 χJ.2).value) := by
  simp_rw [SKFinal.execute_value hN a ha hB hB1 he he1 hd hd1 hC]
  exact sk_approximation_measurable _ _ _ _ _ _ _ _

theorem logarithmic_failure_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ell Z : Ω → ℝ} (hl : Measurable ell) (hZ : Measurable Z) (epsilon : ℝ) :
    MeasurableSet {ω | epsilon < |ell ω - Real.log (Z ω)|} :=
  measurableSet_lt measurable_const (continuous_abs.measurable.comp (hl.sub hZ.log))

theorem logarithmic_success_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ell Z : Ω → ℝ} (hl : Measurable ell) (hZ : Measurable Z) (epsilon : ℝ) :
    MeasurableSet {ω | |ell ω - Real.log (Z ω)| ≤ epsilon} :=
  measurableSet_le (continuous_abs.measurable.comp (hl.sub hZ.log)) measurable_const

theorem relative_success_measurable {Ω : Type*} [MeasurableSpace Ω]
    {ell Z : Ω → ℝ} (hl : Measurable ell) (hZ : Measurable Z) (epsilon : ℝ) :
    MeasurableSet {ω | 1-epsilon ≤ Real.exp (ell ω)/Z ω ∧
      Real.exp (ell ω)/Z ω ≤ 1+epsilon} :=
  (measurableSet_le measurable_const (hl.exp.div hZ)).inter
    (measurableSet_le (hl.exp.div hZ) measurable_const)

section HigherEvents
variable {N : ℕ} (hN : 0 < N) (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
  (B rho pmin beta h epsilon delta : ℝ) (hp : 0 < pmin)
  (hC : 0 < LogApprox.constant P a B rho) (hd : 0 < delta)
include hN hp hC hd

theorem higher_failure_measurable :
    MeasurableSet {J | epsilon <
      |(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value -
        Real.log (Model.partition N P a beta h J)|} :=
  logarithmic_failure_measurable
    (higher_execute_measurable hN pmax P a B rho pmin beta h epsilon delta hp hC hd)
    (partition_measurable _ _ _ _ _) epsilon

theorem higher_success_measurable :
    MeasurableSet {J |
      |(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value -
        Real.log (Model.partition N P a beta h J)| ≤ epsilon} :=
  logarithmic_success_measurable
    (higher_execute_measurable hN pmax P a B rho pmin beta h epsilon delta hp hC hd)
    (partition_measurable _ _ _ _ _) epsilon

theorem higher_relative_success_measurable (tolerance : ℝ) :
    MeasurableSet {J | 1-tolerance ≤
      Real.exp (HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value /
        Model.partition N P a beta h J ∧
      Real.exp (HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value /
        Model.partition N P a beta h J ≤ 1+tolerance} :=
  relative_success_measurable
    (higher_execute_measurable hN pmax P a B rho pmin beta h epsilon delta hp hC hd)
    (partition_measurable _ _ _ _ _) tolerance
end HigherEvents

section SKEvents
variable {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ) (ha : a 2 = 1)
  {B rho beta h epsilon delta : ℝ} (hB : 0 < B) (hB1 : B < 1)
  (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1)
  (hC : 0 < LogApprox.constant {2} a B rho)
include hN ha hB hB1 he he1 hd1

theorem sk_failure_measurable :
    MeasurableSet {χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) |
      epsilon < |(SKFinal.execute N a B rho beta h epsilon delta hC hd χJ.1 χJ.2).value -
        Real.log (Model.partition N {2} a beta h χJ.2)|} :=
  logarithmic_failure_measurable
    (sk_execute_measurable hN a ha hB hB1 he he1 hd hd1 hC)
    ((partition_measurable _ _ _ _ _).comp measurable_snd) epsilon

theorem sk_success_measurable :
    MeasurableSet {χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) |
      |(SKFinal.execute N a B rho beta h epsilon delta hC hd χJ.1 χJ.2).value -
        Real.log (Model.partition N {2} a beta h χJ.2)| ≤ epsilon} :=
  logarithmic_success_measurable
    (sk_execute_measurable hN a ha hB hB1 he he1 hd hd1 hC)
    ((partition_measurable _ _ _ _ _).comp measurable_snd) epsilon

theorem sk_relative_success_measurable (tolerance : ℝ) :
    MeasurableSet {χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2} → ℝ) |
      1-tolerance ≤ Real.exp (SKFinal.execute N a B rho beta h epsilon delta hC hd χJ.1 χJ.2).value /
        Model.partition N {2} a beta h χJ.2 ∧
      Real.exp (SKFinal.execute N a B rho beta h epsilon delta hC hd χJ.1 χJ.2).value /
        Model.partition N {2} a beta h χJ.2 ≤ 1+tolerance} :=
  relative_success_measurable
    (sk_execute_measurable hN a ha hB hB1 he he1 hd hd1 hC)
    ((partition_measurable _ _ _ _ _).comp measurable_snd) tolerance
end SKEvents

end Manuscript.OutputMeasurability
