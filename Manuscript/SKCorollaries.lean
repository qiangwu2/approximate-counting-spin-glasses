import Manuscript.SKFinal
import Manuscript.CountingConsequences

/-! Remark 1.2 for the actual randomized weak-field SK implementation. -/

noncomputable section
open scoped Topology
namespace Manuscript.SKCorollaries
open MeasureTheory Filter SpinGlass.Disorder SpinGlass.ArithmeticEvaluation
open Manuscript.Model Manuscript.MixedThreshold Manuscript.CountingConsequences


/-- Changing a requested confidence by a proved equality only transports the
finite color type; it leaves the complete counted computation unchanged. -/
theorem execute_cast_delta (N : ℕ) (a : ℕ → ℝ) (B rho beta h epsilon : ℝ)
    {delta delta' : ℝ} (heq : delta'=delta)
    (hC : 0 < LogApprox.constant {2} a B rho) (hd' : 0 < delta') (hd : 0 < delta)
    (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ) :
    SKFinal.execute N a B rho beta h epsilon delta' hC hd'
      (cast (congrArg (SKTheorem.Colors N a B rho epsilon) heq).symm χ) J =
      SKFinal.execute N a B rho beta h epsilon delta hC hd χ J := by
  subst delta'
  rfl

abbrev RelativeColors (N : ℕ) (a : ℕ → ℝ) (B rho epsilon : ℝ) :=
  SKTheorem.Colors N a B rho (relativeTolerance epsilon) (confidence N 1)

/-- The computed tolerances select the finite color tape; rewriting its type
uses the proved numerical equality and changes no random coordinate. -/
def relativeExecute (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ)
    (B rho beta h epsilon : ℝ) (hC : 0 < LogApprox.constant {2} a B rho)
    (χ : RelativeColors N a B rho epsilon)
    (J : Edge N {2} → ℝ) : Computation :=
  let eta := relativeToleranceComputation epsilon
  let delta := confidenceComputation N 1
  let χ' : SKTheorem.Colors N a B rho eta.value delta.value :=
    cast (congrArg (SKTheorem.Colors N a B rho eta.value) (confidenceComputation_value hN 1)).symm χ
  have hd : 0 < delta.value := by
    simpa only [delta,confidenceComputation_value hN] using
      (confidence_range hN (by norm_num : (0:ℝ)≤1)).1
  let result := SKFinal.execute N a B rho beta h eta.value delta.value hC hd χ' J
  ⟨Real.exp result.value,result.operations+eta.operations+delta.operations+1⟩

theorem relativeExecute_value (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ)
    (B rho beta h epsilon : ℝ) (hC : 0 < LogApprox.constant {2} a B rho)
    (χ : RelativeColors N a B rho epsilon)
    (J : Edge N {2} → ℝ) :
    (relativeExecute N hN a B rho beta h epsilon hC χ J).value =
      Real.exp (SKFinal.execute N a B rho beta h
        (relativeTolerance epsilon) (confidence N 1) hC (confidence_range hN (by norm_num : (0:ℝ)≤1)).1 χ J).value := by
  simp only [relativeExecute,relativeToleranceComputation_value]
  rw [execute_cast_delta N a B rho beta h _ (confidenceComputation_value hN 1)]

theorem relativeExecute_operations (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ)
    (B rho beta h epsilon : ℝ) (hC : 0 < LogApprox.constant {2} a B rho)
    (χ : RelativeColors N a B rho epsilon)
    (J : Edge N {2} → ℝ) :
    (relativeExecute N hN a B rho beta h epsilon hC χ J).operations =
      (SKFinal.execute N a B rho beta h
        (relativeTolerance epsilon) (confidence N 1) hC (confidence_range hN (by norm_num : (0:ℝ)≤1)).1 χ J).operations+7 := by
  simp only [relativeExecute,relativeToleranceComputation_value,
    relativeToleranceComputation_operations,confidenceComputation_operations]
  rw [execute_cast_delta N a B rho beta h _ (confidenceComputation_value hN 1)]

/-- The relative-counting success probability and its uniform polynomial cost,
including the two tolerance computations and the final exponentiation. -/
theorem relative_counting (a : ℕ → ℝ) (ha : a 2=1)
    {B rho : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (N : ℕ) (hN : 2 ≤ N),
      ∀ (beta h epsilon : ℝ), 0 ≤ beta → beta ≤ B →
      |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) → 0 < epsilon → epsilon < 1 →
      (1-OriginalLawLowerTail.tau μ N {2} a B (theta {2} a B)-confidence N 1 ≤
        ((SKTheorem.colorLaw N a B rho (relativeTolerance epsilon) (confidence N 1)).prod (iidLaw μ)).real
          {χJ : RelativeColors N a B rho epsilon × (Edge N {2} → ℝ) |
            1-epsilon ≤ (relativeExecute N (by omega) a B rho beta h epsilon (SKFinal.constant_pos a ha hB hB1) χJ.1 χJ.2).value /
              Model.partition N {2} a beta h χJ.2 ∧
            (relativeExecute N (by omega) a B rho beta h epsilon (SKFinal.constant_pos a ha hB hB1) χJ.1 χJ.2).value /
              Model.partition N {2} a beta h χJ.2 ≤ 1+epsilon}) ∧
      ∀ (χ : RelativeColors N a B rho epsilon) (J : Edge N {2} → ℝ),
        0 < (relativeExecute N (by omega) a B rho beta h epsilon (SKFinal.constant_pos a ha hB hB1) χ J).value ∧
        ((relativeExecute N (by omega) a B rho beta h epsilon (SKFinal.constant_pos a ha hB hB1) χ J).operations : ℝ) ≤
          C*(N : ℝ)^C*epsilon^(-C) := by
  obtain ⟨C,hC,hmain⟩ := SKFinal.end_to_end a ha (rho := rho) hB hB1
  refine ⟨relativeCostConstant C 7,polynomialConstant_pos _ _ _,?_⟩
  intro μ hprob hμ hunit N hN beta h epsilon hbeta hbetaB hfield he he1
  letI : IsProbabilityMeasure μ := hprob
  have hNpos : 0 < N := by omega
  obtain ⟨heta,heta1,_⟩ := relativeTolerance_range he he1
  obtain ⟨hd,hd1⟩ := confidence_range hNpos (by norm_num : (0:ℝ)≤1)
  letI := SKFinal.colorLaw_probability N a ha (rho := rho) hB hB1 heta heta1 hd hd1
  obtain ⟨herror,hcost⟩ := hmain μ hprob hμ hunit N hN beta h (relativeTolerance epsilon)
    (confidence N 1) hbeta hbetaB hfield heta heta1 hd hd1
  constructor
  · simp_rw [relativeExecute_value]
    have hs := success_probability
      ((SKTheorem.colorLaw N a B rho (relativeTolerance epsilon) (confidence N 1)).prod (iidLaw μ))
      (fun χJ : RelativeColors N a B rho epsilon × (Edge N {2} → ℝ) =>
        (SKFinal.execute N a B rho beta h (relativeTolerance epsilon) (confidence N 1) (SKFinal.constant_pos a ha hB hB1) hd χJ.1 χJ.2).value)
      (fun χJ => Model.partition N {2} a beta h χJ.2)
      (fun χJ => Model.partition_pos N {2} a beta h χJ.2) he herror
    linarith
  · intro χ J
    constructor
    · rw [relativeExecute_value]
      exact Real.exp_pos _
    · rw [relativeExecute_operations,Nat.cast_add,Nat.cast_ofNat]
      have hh := hcost χ J
      have hf := relative_polynomial hC (by norm_num : (0:ℝ)≤7) hNpos he he1
      linarith

/-- The allowance tends to one at the fourth-moment endpoint, including SK. -/
theorem relative_allowance_tendsto_one (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℕ → ℝ) (ha : a 2=1) {B : ℝ} (hB : 0 < B) (hB1 : B < 1)
    (h4 : Integrable (fun x : ℝ => |x|^(4 : ℕ)) μ) :
    Tendsto (fun N : ℕ => 1-OriginalLawLowerTail.tau μ N {2} a B (theta {2} a B)-confidence N 1)
      atTop (𝓝 1) := by
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  have ht := UniformTau.tau_tendsto_zero_fourth μ {2} a (by simp [ha]) (by simp)
    hB (theta_range {2} a hB hBT).1 (theta_range {2} a hB hBT).2 h4
  have hc : Tendsto (fun N : ℕ => confidence N 1) atTop (𝓝 0) := by
    have hh : Tendsto (fun N : ℕ => (N : ℝ)^(-(1 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp tendsto_natCast_atTop_atTop
    simpa only [confidence,mul_zero] using hh.const_mul (1/2 : ℝ)
  simpa only [sub_zero] using (tendsto_const_nhds.sub ht).sub hc

abbrev ConfidenceColors (N : ℕ) (a : ℕ → ℝ) (B rho epsilon b : ℝ) :=
  SKTheorem.Colors N a B rho epsilon (confidence N b)

def confidenceExecute (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ)
    (B rho beta h epsilon b : ℝ) (hb : 0 ≤ b)
    (hC : 0 < LogApprox.constant {2} a B rho) (χ : ConfidenceColors N a B rho epsilon b)
    (J : Edge N {2} → ℝ) : Computation :=
  let delta := confidenceComputation N b
  let χ' : SKTheorem.Colors N a B rho epsilon delta.value :=
    cast (congrArg (SKTheorem.Colors N a B rho epsilon) (confidenceComputation_value hN b)).symm χ
  have hd : 0 < delta.value := by
    simpa only [delta,confidenceComputation_value hN] using (confidence_range hN hb).1
  let result := SKFinal.execute N a B rho beta h epsilon delta.value hC hd χ' J
  ⟨result.value,result.operations+delta.operations⟩

theorem confidenceExecute_value (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ)
    (B rho beta h epsilon b : ℝ) (hb : 0 ≤ b)
    (hC : 0 < LogApprox.constant {2} a B rho) (χ : ConfidenceColors N a B rho epsilon b)
    (J : Edge N {2} → ℝ) :
    (confidenceExecute N hN a B rho beta h epsilon b hb hC χ J).value =
      (SKFinal.execute N a B rho beta h epsilon (confidence N b) hC (confidence_range hN hb).1 χ J).value := by
  simp only [confidenceExecute]
  rw [execute_cast_delta N a B rho beta h epsilon (confidenceComputation_value hN b)]

theorem confidenceExecute_operations (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ)
    (B rho beta h epsilon b : ℝ) (hb : 0 ≤ b)
    (hC : 0 < LogApprox.constant {2} a B rho) (χ : ConfidenceColors N a B rho epsilon b)
    (J : Edge N {2} → ℝ) :
    (confidenceExecute N hN a B rho beta h epsilon b hb hC χ J).operations =
      (SKFinal.execute N a B rho beta h epsilon (confidence N b) hC (confidence_range hN hb).1 χ J).operations+4 := by
  simp only [confidenceExecute,confidenceComputation_operations]
  rw [execute_cast_delta N a B rho beta h epsilon (confidenceComputation_value hN b)]

/-- Remark 1.2(ii) for SK, including equality at the real moment threshold
m>=4+2b. The eventual size threshold is uniform over beta, h, and epsilon. -/
theorem polynomial_confidence (a : ℕ → ℝ) (ha : a 2=1)
    {B rho b : ℝ} (hB : 0 < B) (hB1 : B < 1) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ (m : ℝ), 4+2*b ≤ m →
      Integrable (fun x : ℝ => |x|^m) μ →
      ∀ᶠ N : ℕ in atTop, ∃ hN : 2 ≤ N, ∀ (beta h epsilon : ℝ), 0 ≤ beta → beta ≤ B →
      |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) → 0 < epsilon → epsilon < 1 →
      (((SKTheorem.colorLaw N a B rho epsilon (confidence N b)).prod (iidLaw μ)).real
        {χJ : ConfidenceColors N a B rho epsilon b × (Edge N {2} → ℝ) | epsilon <
          |(confidenceExecute N (by omega) a B rho beta h epsilon b hb.le (SKFinal.constant_pos a ha hB hB1) χJ.1 χJ.2).value-
            Real.log (Model.partition N {2} a beta h χJ.2)|} ≤ (N : ℝ)^(-b)) ∧
      ∀ (χ : ConfidenceColors N a B rho epsilon b) (J : Edge N {2} → ℝ),
        ((confidenceExecute N (by omega) a B rho beta h epsilon b hb.le (SKFinal.constant_pos a ha hB hB1) χ J).operations : ℝ) ≤
          C*(N : ℝ)^C*epsilon^(-C) := by
  obtain ⟨C,hC,hmain⟩ := SKFinal.end_to_end a ha (rho := rho) hB hB1
  refine ⟨confidenceCostConstant C 4 b,polynomialConstant_pos _ _ _,?_⟩
  intro μ hprob hμ hunit m hm hint
  letI : IsProbabilityMeasure μ := hprob
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  have ht := UniformTau.tau_eventually_le_half_power μ {2} a (by simp [ha]) 2 (by omega)
    (by simp) hB (theta_range {2} a hB hBT).1 (theta_range {2} a hB hBT).2 hb
    (by norm_num; linarith) hint
  filter_upwards [ht,eventually_ge_atTop (2 : ℕ)] with N htail hN
  refine ⟨hN,?_⟩
  intro beta h epsilon hbeta hbetaB hfield he he1
  have hNpos : 0 < N := by omega
  obtain ⟨hd,hd1⟩ := confidence_range hNpos hb.le
  obtain ⟨herror,hcost⟩ := hmain μ hprob hμ hunit N hN beta h epsilon (confidence N b)
    hbeta hbetaB hfield he he1 hd hd1
  constructor
  · simp_rw [confidenceExecute_value]
    apply herror.trans
    unfold confidence
    linarith
  · intro χ J
    rw [confidenceExecute_operations,Nat.cast_add,Nat.cast_ofNat]
    have hh := hcost χ J
    have hf := confidence_overhead_polynomial hC (by norm_num : (0:ℝ)≤4) hb.le hNpos he he1.le
    linarith

end Manuscript.SKCorollaries
