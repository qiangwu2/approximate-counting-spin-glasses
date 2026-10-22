import Manuscript.HigherOrderFinal
import Manuscript.CountingConsequences

/-! Remark 1.2 for the actual deterministic higher-order implementation. -/

noncomputable section
open scoped Topology
namespace Manuscript.HigherOrderCorollaries
open MeasureTheory Filter SpinGlass.Disorder SpinGlass.ArithmeticEvaluation
open Manuscript.Model Manuscript.MixedThreshold Manuscript.CountingConsequences

def relativeExecute (N : ℕ) (P : Finset ℕ) (hP : P.Nonempty) (a : ℕ → ℝ)
    (B rho beta h epsilon : ℝ) (J : Edge N P → ℝ) : Computation :=
  let eta := relativeToleranceComputation epsilon
  let delta := confidenceComputation N 1
  let result := HigherOrderFinal.canonicalExecute N P hP a B rho beta h eta.value delta.value J
  ⟨Real.exp result.value,result.operations+eta.operations+delta.operations+1⟩

theorem relativeExecute_value {N : ℕ} (hN : 0 < N) (P : Finset ℕ) (hP : P.Nonempty)
    (a : ℕ → ℝ) (B rho beta h epsilon : ℝ) (J : Edge N P → ℝ) :
    (relativeExecute N P hP a B rho beta h epsilon J).value =
      Real.exp (HigherOrderFinal.canonicalExecute N P hP a B rho beta h
        (relativeTolerance epsilon) (confidence N 1) J).value := by
  simp only [relativeExecute,relativeToleranceComputation_value,confidenceComputation_value hN]

theorem relativeExecute_operations {N : ℕ} (hN : 0 < N) (P : Finset ℕ) (hP : P.Nonempty)
    (a : ℕ → ℝ) (B rho beta h epsilon : ℝ) (J : Edge N P → ℝ) :
    (relativeExecute N P hP a B rho beta h epsilon J).operations =
      (HigherOrderFinal.canonicalExecute N P hP a B rho beta h
        (relativeTolerance epsilon) (confidence N 1) J).operations+7 := by
  simp only [relativeExecute,relativeToleranceComputation_value,confidenceComputation_value hN,
    relativeToleranceComputation_operations,confidenceComputation_operations]

/-- The relative-counting guarantee and its uniform polynomial operation bound,
including the exponentiation and the computation of both requested tolerances. -/
theorem relative_counting (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 3 ≤ p)
    {B rho : ℝ} (hB : 0 < B) (hBT : B < betaF P a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (N : ℕ), P.max' hP ≤ N →
      ∀ (beta h epsilon : ℝ), 0 ≤ beta → beta ≤ B →
      |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) → 0 < epsilon → epsilon < 1 →
      (1-OriginalLawLowerTail.tau μ N P a B (theta P a B)-confidence N 1 ≤
        (iidLaw μ).real {J | 1-epsilon ≤
          (relativeExecute N P hP a B rho beta h epsilon J).value/Model.partition N P a beta h J ∧
          (relativeExecute N P hP a B rho beta h epsilon J).value/Model.partition N P a beta h J ≤ 1+epsilon}) ∧
      ∀ J : Edge N P → ℝ,
        0 < (relativeExecute N P hP a B rho beta h epsilon J).value ∧
        ((relativeExecute N P hP a B rho beta h epsilon J).operations : ℝ) ≤
          C*(N : ℝ)^C*epsilon^(-C) := by
  obtain ⟨C,hC,hmain⟩ := HigherOrderFinal.canonical_end_to_end P a hP ha hp (rho := rho) hB hBT
  refine ⟨relativeCostConstant C 7,polynomialConstant_pos _ _ _,?_⟩
  intro μ hprob hμ hunit N hN beta h epsilon hbeta hbetaB hfield he he1
  letI : IsProbabilityMeasure μ := hprob
  have hNpos : 0 < N := by
    have := hp _ (Finset.max'_mem P hP)
    omega
  obtain ⟨heta,heta1,_⟩ := relativeTolerance_range he he1
  obtain ⟨hd,hd1⟩ := confidence_range hNpos (by norm_num : (0:ℝ)≤1)
  obtain ⟨herror,hcost⟩ := hmain μ hprob hμ hunit N hN beta h (relativeTolerance epsilon)
    (confidence N 1) hbeta hbetaB hfield heta heta1 hd hd1
  constructor
  · simp_rw [relativeExecute_value hNpos]
    have hs := success_probability (iidLaw μ)
      (fun J => (HigherOrderFinal.canonicalExecute N P hP a B rho beta h
        (relativeTolerance epsilon) (confidence N 1) J).value)
      (Model.partition N P a beta h) (Model.partition_pos N P a beta h) he herror
    linarith
  · intro J
    constructor
    · rw [relativeExecute_value hNpos]
      exact Real.exp_pos _
    · rw [relativeExecute_operations hNpos,Nat.cast_add,Nat.cast_ofNat]
      have hh := hcost J
      have hf := relative_polynomial hC (by norm_num : (0:ℝ)≤7) hNpos he he1
      linarith

/-- The success allowance in relative_counting tends to one whenever the
common disorder law has a finite fourth moment. -/
theorem relative_allowance_tendsto_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 < a p)
    (hp : ∀ p ∈ P, 3 ≤ p) {B : ℝ} (hB : 0 < B) (hBT : B < betaF P a)
    (h4 : Integrable (fun x : ℝ => |x|^(4 : ℕ)) μ) :
    Tendsto (fun N : ℕ => 1-OriginalLawLowerTail.tau μ N P a B (theta P a B)-confidence N 1)
      atTop (𝓝 1) := by
  have ht := UniformTau.tau_tendsto_zero_fourth μ P a ha (fun p hpP => by have := hp p hpP; omega)
    hB (theta_range P a hB hBT).1 (theta_range P a hB hBT).2 h4
  have hc : Tendsto (fun N : ℕ => confidence N 1) atTop (𝓝 0) := by
    have hh : Tendsto (fun N : ℕ => (N : ℝ)^(-(1 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp tendsto_natCast_atTop_atTop
    simpa only [confidence,mul_zero] using hh.const_mul (1/2 : ℝ)
  simpa only [sub_zero] using (tendsto_const_nhds.sub ht).sub hc

def confidenceExecute (N : ℕ) (P : Finset ℕ) (hP : P.Nonempty) (a : ℕ → ℝ)
    (B rho beta h epsilon b : ℝ) (J : Edge N P → ℝ) : Computation :=
  let delta := confidenceComputation N b
  let result := HigherOrderFinal.canonicalExecute N P hP a B rho beta h epsilon delta.value J
  ⟨result.value,result.operations+delta.operations⟩

theorem confidenceExecute_value {N : ℕ} (hN : 0 < N) (P : Finset ℕ) (hP : P.Nonempty)
    (a : ℕ → ℝ) (B rho beta h epsilon b : ℝ) (J : Edge N P → ℝ) :
    (confidenceExecute N P hP a B rho beta h epsilon b J).value =
      (HigherOrderFinal.canonicalExecute N P hP a B rho beta h epsilon (confidence N b) J).value := by
  simp only [confidenceExecute,confidenceComputation_value hN]

theorem confidenceExecute_operations {N : ℕ} (hN : 0 < N) (P : Finset ℕ) (hP : P.Nonempty)
    (a : ℕ → ℝ) (B rho beta h epsilon b : ℝ) (J : Edge N P → ℝ) :
    (confidenceExecute N P hP a B rho beta h epsilon b J).operations =
      (HigherOrderFinal.canonicalExecute N P hP a B rho beta h epsilon (confidence N b) J).operations+4 := by
  simp only [confidenceExecute,confidenceComputation_value hN,confidenceComputation_operations]

/-- Remark 1.2(ii), including its equality endpoint for the real moment order.
The eventual lower size threshold is shared by all allowed beta, h and epsilon. -/
theorem polynomial_confidence (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 3 ≤ p)
    {B rho b : ℝ} (hB : 0 < B) (hBT : B < betaF P a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (m : ℝ),
      2*((P.min' hP : ℝ)+b)/((P.min' hP : ℝ)-1) ≤ m →
      Integrable (fun x : ℝ => |x|^m) μ →
      ∀ᶠ N : ℕ in atTop, ∀ (beta h epsilon : ℝ), 0 ≤ beta → beta ≤ B →
      |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) → 0 < epsilon → epsilon < 1 →
      ((iidLaw μ).real {J | epsilon <
        |(confidenceExecute N P hP a B rho beta h epsilon b J).value-
          Real.log (Model.partition N P a beta h J)|} ≤ (N : ℝ)^(-b)) ∧
      ∀ J : Edge N P → ℝ,
        ((confidenceExecute N P hP a B rho beta h epsilon b J).operations : ℝ) ≤
          C*(N : ℝ)^C*epsilon^(-C) := by
  obtain ⟨C,hC,hmain⟩ := HigherOrderFinal.canonical_end_to_end P a hP ha hp (rho := rho) hB hBT
  refine ⟨confidenceCostConstant C 4 b,polynomialConstant_pos _ _ _,?_⟩
  intro μ hprob hμ hunit m hm hint
  letI : IsProbabilityMeasure μ := hprob
  have hpm : 2 ≤ P.min' hP := by have := hp _ (Finset.min'_mem P hP); omega
  have ht := UniformTau.tau_eventually_le_half_power μ P a ha (P.min' hP) hpm
    (fun p hpP => Finset.min'_le P p hpP) hB (theta_range P a hB hBT).1
    (theta_range P a hB hBT).2 hb hm hint
  filter_upwards [ht,eventually_ge_atTop (P.max' hP)] with N htail hN
  intro beta h epsilon hbeta hbetaB hfield he he1
  have hNpos : 0 < N := by have := hp _ (Finset.max'_mem P hP); omega
  obtain ⟨hd,hd1⟩ := confidence_range hNpos hb.le
  obtain ⟨herror,hcost⟩ := hmain μ hprob hμ hunit N hN beta h epsilon (confidence N b)
    hbeta hbetaB hfield he he1 hd hd1
  constructor
  · simp_rw [confidenceExecute_value hNpos]
    apply herror.trans
    unfold confidence
    linarith
  · intro J
    rw [confidenceExecute_operations hNpos,Nat.cast_add,Nat.cast_ofNat]
    have hh := hcost J
    have hf := confidence_overhead_polynomial hC (by norm_num : (0:ℝ)≤4) hb.le hNpos he he1.le
    linarith

end Manuscript.HigherOrderCorollaries
