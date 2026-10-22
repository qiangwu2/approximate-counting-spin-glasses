import Manuscript.LogRuntime
import Manuscript.UniformTau
import Manuscript.InputPreparation

/-! Exact logarithmic-to-relative conversion and the polynomial confidence
substitutions in Remark 1.2. -/

noncomputable section
open scoped Topology
namespace Manuscript.CountingConsequences
open MeasureTheory Filter

def relativeTolerance (epsilon : ℝ) : ℝ := Real.log (1+epsilon)
def confidence (N : ℕ) (b : ℝ) : ℝ := (1/2 : ℝ)*(N : ℝ)^(-b)

open SpinGlass.ArithmeticEvaluation Manuscript.InputPreparation

def relativeToleranceComputation (epsilon : ℝ) : Computation :=
  logarithm (add (literal 1) (literal epsilon))
def confidenceComputation (N : ℕ) (b : ℝ) : Computation :=
  divide (exponential (mul (literal (-b)) (logarithm (literal N)))) (literal 2)

@[simp] theorem relativeToleranceComputation_value (epsilon : ℝ) :
    (relativeToleranceComputation epsilon).value = relativeTolerance epsilon := rfl
@[simp] theorem relativeToleranceComputation_operations (epsilon : ℝ) :
    (relativeToleranceComputation epsilon).operations = 2 := rfl
@[simp] theorem confidenceComputation_operations (N : ℕ) (b : ℝ) :
    (confidenceComputation N b).operations = 4 := rfl
theorem confidenceComputation_value {N : ℕ} (hN : 0 < N) (b : ℝ) :
    (confidenceComputation N b).value = confidence N b := by
  unfold confidenceComputation divide exponential mul logarithm literal confidence
  dsimp only
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hN : (0:ℝ)<N)]
  congr 1 <;> ring

theorem relativeTolerance_range {epsilon : ℝ} (he : 0 < epsilon) (he1 : epsilon < 1) :
    0 < relativeTolerance epsilon ∧ relativeTolerance epsilon < 1 ∧
      epsilon/2 ≤ relativeTolerance epsilon := by
  have hpos : 0 < 1+epsilon := by linarith
  have hlo := Real.le_log_one_add_of_nonneg he.le
  have hupper := Real.log_le_sub_one_of_pos hpos
  have hden : 0 < epsilon+2 := by linarith
  have hhalf : epsilon/2 ≤ 2*epsilon/(epsilon+2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  exact ⟨Real.log_pos (by linarith),by unfold relativeTolerance; linarith,hhalf.trans hlo⟩

theorem relative_of_log_error {ell Z epsilon : ℝ} (hZ : 0 < Z) (he : 0 < epsilon)
    (herr : |ell-Real.log Z| ≤ relativeTolerance epsilon) :
    1-epsilon ≤ Real.exp ell/Z ∧ Real.exp ell/Z ≤ 1+epsilon := by
  have he1 : 0 < 1+epsilon := by linarith
  have hr : Real.exp ell/Z = Real.exp (ell-Real.log Z) := by
    rw [Real.exp_sub,Real.exp_log hZ]
  rw [hr]
  obtain ⟨hl,hu⟩ := abs_le.mp herr
  constructor
  · have hexp := Real.exp_le_exp.mpr hl
    have hinv : Real.exp (-relativeTolerance epsilon) = (1+epsilon)⁻¹ := by
      rw [Real.exp_neg,relativeTolerance,Real.exp_log he1]
    rw [hinv] at hexp
    apply le_trans _ hexp
    rw [inv_eq_one_div]
    apply (le_div_iff₀ he1).mpr
    nlinarith [sq_nonneg epsilon]
  · have hexp := Real.exp_le_exp.mpr hu
    simpa only [relativeTolerance,Real.exp_log he1] using hexp

/-- A lower bound on success follows even without introducing an unnecessary
measurability premise for a numerical implementation. -/
theorem success_probability {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ell Z : Ω → ℝ)
    {epsilon d : ℝ} (hZ : ∀ ω, 0 < Z ω) (he : 0 < epsilon)
    (herr : Q.real {ω | relativeTolerance epsilon < |ell ω-Real.log (Z ω)|} ≤ d) :
    1-d ≤ Q.real {ω | 1-epsilon ≤ Real.exp (ell ω)/Z ω ∧
      Real.exp (ell ω)/Z ω ≤ 1+epsilon} := by
  let S := {ω | 1-epsilon ≤ Real.exp (ell ω)/Z ω ∧ Real.exp (ell ω)/Z ω ≤ 1+epsilon}
  have hsub : Sᶜ ⊆ {ω | relativeTolerance epsilon < |ell ω-Real.log (Z ω)|} := by
    intro ω hω
    by_contra hn
    exact hω (relative_of_log_error (hZ ω) he (le_of_not_gt hn))
  have hc := (measureReal_mono hsub).trans herr
  have hh := measureReal_union_le (μ := Q) S Sᶜ
  simp only [Set.union_compl_self,measureReal_univ_eq_one] at hh
  change 1-d ≤ Q.real S
  linarith

theorem confidence_range {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    0 < confidence N b ∧ confidence N b < 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp := Real.rpow_le_rpow_of_exponent_le hN1 (neg_nonpos.mpr hb)
  have hpos := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN : (0 : ℝ)<N) (-b)
  simp only [Real.rpow_zero] at hp
  unfold confidence
  constructor <;> linarith

theorem confidence_inverse {N : ℕ} (hN : 0 < N) (b C : ℝ) :
    confidence N b ^ (-C) = (2 : ℝ)^C*(N : ℝ)^(b*C) := by
  have hNR : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hp := Real.rpow_pos_of_pos hNR (-b)
  rw [Real.rpow_def_of_pos (show 0 < confidence N b by unfold confidence; positivity),
    confidence,Real.log_mul (by norm_num) hp.ne',Real.log_rpow hNR,
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos hNR,← Real.exp_add]
  simp only [one_div,Real.log_inv]
  congr 1
  ring

def polynomialConstant (A d e : ℝ) : ℝ := max 1 (max A (max d e))
theorem polynomialConstant_pos (A d e : ℝ) : 0 < polynomialConstant A d e :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem absorb_polynomial {A d e epsilon : ℝ} {N : ℕ}
    (hA : 0 ≤ A) (hN : 0 < N) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    A*(N : ℝ)^d*epsilon^(-e) ≤
      polynomialConstant A d e*(N : ℝ)^(polynomialConstant A d e)*epsilon^(-polynomialConstant A d e) := by
  let D := polynomialConstant A d e
  have hD : 0 < D := polynomialConstant_pos _ _ _
  have hAD : A ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hdD : d ≤ D := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have heD : e ≤ D := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hNp := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ)≤N) hdD
  have hep := Real.rpow_le_rpow_of_exponent_ge he he1 (neg_le_neg heD)
  exact mul_le_mul (mul_le_mul hAD hNp (Real.rpow_nonneg (Nat.cast_nonneg _) _) hD.le)
    hep (Real.rpow_nonneg he.le _) (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem confidence_polynomial {C epsilon b : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 0 < N) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    C*(N : ℝ)^C*epsilon^(-C)*(confidence N b)^(-C) ≤
      polynomialConstant (C*2^C) ((1+b)*C) C *
        (N : ℝ)^(polynomialConstant (C*2^C) ((1+b)*C) C) *
        epsilon^(-polynomialConstant (C*2^C) ((1+b)*C) C) := by
  rw [confidence_inverse hN]
  have hid : C*(N : ℝ)^C*epsilon^(-C)*((2 : ℝ)^C*(N : ℝ)^(b*C)) =
      (C*2^C)*(N : ℝ)^((1+b)*C)*epsilon^(-C) := by
    rw [show (1+b)*C=C+b*C by ring,Real.rpow_add (Nat.cast_pos.mpr hN : (0:ℝ)<N)]
    ring
  rw [hid]
  exact absorb_polynomial (by positivity) hN he he1

theorem overhead_le {C eta delta k : ℝ} {N : ℕ}
    (hC : 0 ≤ C) (hk : 0 ≤ k) (hN : 0 < N)
    (he : 0 < eta) (he1 : eta ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    C*(N : ℝ)^C*eta^(-C)*delta^(-C)+k ≤
      (C+k)*(N : ℝ)^C*eta^(-C)*delta^(-C) := by
  have hn := Real.one_le_rpow (by exact_mod_cast hN : (1:ℝ)≤N) hC
  have hp := Real.rpow_le_rpow_of_exponent_ge he he1 (neg_nonpos.mpr hC)
  have hq := Real.rpow_le_rpow_of_exponent_ge hd hd1 (neg_nonpos.mpr hC)
  simp only [Real.rpow_zero] at hp hq
  have hf1 : 1 ≤ (N : ℝ)^C*eta^(-C) :=
    (by norm_num : (1:ℝ) = 1*1).le.trans (mul_le_mul hn hp (by norm_num) (by linarith))
  have hf : 1 ≤ (N : ℝ)^C*eta^(-C)*delta^(-C) :=
    (by norm_num : (1:ℝ) = 1*1).le.trans (mul_le_mul hf1 hq (by norm_num) (by linarith))
  nlinarith [mul_le_mul_of_nonneg_left hf hk]

theorem relative_inverse {epsilon C : ℝ} (he : 0 < epsilon) (he1 : epsilon < 1) (hC : 0 ≤ C) :
    relativeTolerance epsilon ^ (-C) ≤ (2 : ℝ)^C*epsilon^(-C) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<epsilon/2)
    (relativeTolerance_range he he1).2.2 (neg_nonpos.mpr hC)
  rw [Real.div_rpow he.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul] at hh
  simpa only [mul_comm] using hh

def relativeCostConstant (C k : ℝ) : ℝ :=
  polynomialConstant ((C+k)*2^C*2^C) (2*C) C

theorem relative_polynomial {C epsilon k : ℝ} {N : ℕ}
    (hC : 0 < C) (hk : 0 ≤ k) (hN : 0 < N) (he : 0 < epsilon) (he1 : epsilon < 1) :
    C*(N : ℝ)^C*(relativeTolerance epsilon)^(-C)*(confidence N 1)^(-C)+k ≤
      relativeCostConstant C k*(N : ℝ)^(relativeCostConstant C k)*epsilon^(-relativeCostConstant C k) := by
  obtain ⟨heta,heta1,hhalf⟩ := relativeTolerance_range he he1
  obtain ⟨hd,hd1⟩ := confidence_range hN (by norm_num : (0:ℝ)≤1)
  apply (overhead_le hC.le hk hN heta heta1.le hd hd1.le).trans
  have hi := relative_inverse he he1 hC.le
  rw [confidence_inverse hN,one_mul]
  calc
    _ ≤ (C+k)*(N : ℝ)^C*((2 : ℝ)^C*epsilon^(-C))*((2 : ℝ)^C*(N : ℝ)^C) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hi (by positivity)
    _ = ((C+k)*2^C*2^C)*(N : ℝ)^(2*C)*epsilon^(-C) := by
      rw [show 2*C=C+C by ring,Real.rpow_add (Nat.cast_pos.mpr hN : (0:ℝ)<N)]
      ring
    _ ≤ _ := absorb_polynomial (by positivity) hN he he1.le

def confidenceCostConstant (C k b : ℝ) : ℝ :=
  polynomialConstant ((C+k)*2^C) ((1+b)*C) C

theorem confidence_overhead_polynomial {C epsilon k b : ℝ} {N : ℕ}
    (hC : 0 < C) (hk : 0 ≤ k) (hb : 0 ≤ b) (hN : 0 < N)
    (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    C*(N : ℝ)^C*epsilon^(-C)*(confidence N b)^(-C)+k ≤
      confidenceCostConstant C k b*(N : ℝ)^(confidenceCostConstant C k b)*epsilon^(-confidenceCostConstant C k b) := by
  obtain ⟨hd,hd1⟩ := confidence_range hN hb
  apply (overhead_le hC.le hk hN he he1 hd hd1.le).trans
  rw [confidence_inverse hN]
  have hid : (C+k)*(N : ℝ)^C*epsilon^(-C)*((2 : ℝ)^C*(N : ℝ)^(b*C)) =
      ((C+k)*2^C)*(N : ℝ)^((1+b)*C)*epsilon^(-C) := by
    rw [show (1+b)*C=C+b*C by ring,Real.rpow_add (Nat.cast_pos.mpr hN : (0:ℝ)<N)]
    ring
  rw [hid]
  exact absorb_polynomial (by positivity) hN he he1

end Manuscript.CountingConsequences
