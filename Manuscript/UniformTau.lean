import Manuscript.UniformTailMoments

/-! The actual finite-mixture tail remainder and its fourth/real-moment
consequences. The real-moment threshold includes equality. -/
noncomputable section
open scoped BigOperators Topology
namespace Manuscript.UniformTau
open MeasureTheory Filter Manuscript.OriginalLawLowerTail Manuscript.UniformTailMoments

def orderRemainder (μ : Measure ℝ) (N p : ℕ) (ap c : ℝ) : ℝ :=
  (N.choose p : ℝ) * μ.real {x : ℝ | c * Model.scaleDenominator N p < |ap * x|}

theorem orderRemainder_nonneg (μ : Measure ℝ) (N p : ℕ) (ap c : ℝ) :
    0 ≤ orderRemainder μ N p ap c :=
  mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg

theorem scaled_tail_event (N p : ℕ) {ap : ℝ} (ha : 0 < ap) (c : ℝ) :
    {x : ℝ | c * Model.scaleDenominator N p < |ap * x|} =
      {x : ℝ | (c / ap) * (N : ℝ) ^ (((p : ℝ)-1)/2) < |x|} := by
  ext x
  simp only [Set.mem_setOf_eq, Model.scaleDenominator, abs_mul, abs_of_pos ha]
  rw [div_mul_eq_mul_div, div_lt_iff₀ ha]
  rw [mul_comm |x| ap]

/-- Each order contributes the sharp little-o rate at the critical moment
exponent, with the exact unordered-edge count. -/
theorem orderRemainder_weighted_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2 ≤ p) {ap c q b : ℝ} (ha : 0 < ap) (hc : 0 < c)
    (hq : 0 ≤ q) (hint : Integrable (fun x : ℝ => |x| ^ q) μ)
    (hm : (p : ℝ) + b ≤ (((p : ℝ)-1)/2) * q) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ b * orderRemainder μ N p ap c) atTop (𝓝 0) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < ((p : ℝ)-1)/2 := by linarith
  have hz := scaled_abs_tail_tendsto_zero μ hq hint (div_pos hc ha) hd hm
  apply squeeze_zero' _ _ hz
  · exact Eventually.of_forall (fun N =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) b)
        (orderRemainder_nonneg μ N p ap c))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN' : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    unfold orderRemainder
    rw [scaled_tail_event N p ha c]
    have hcount : (N.choose p : ℝ) ≤ (N : ℝ) ^ (p : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.choose_le_pow N p
    calc
      _ ≤ (N : ℝ) ^ b * ((N : ℝ) ^ (p : ℝ) *
          μ.real {x : ℝ | c / ap * (N : ℝ) ^ (((p : ℝ)-1)/2) < |x|}) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcount measureReal_nonneg)
          (Real.rpow_nonneg hN'.le b)
      _ = _ := by rw [Real.rpow_add hN']; ring

/-- Uniform finite-mixture polynomial decay of the actual τ_N. -/
theorem tau_weighted_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 < a p)
    (hp : ∀ p ∈ P, 2 ≤ p) {B θ q b : ℝ}
    (hB : 0 < B) (hθ : 0 < θ) (hθ1 : θ < 1) (hq : 0 ≤ q)
    (hint : Integrable (fun x : ℝ => |x| ^ q) μ)
    (hm : ∀ p ∈ P, (p : ℝ) + b ≤ (((p : ℝ)-1)/2) * q) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ b * tau μ N P a B θ) atTop (𝓝 0) := by
  have heq : (fun N : ℕ => (N : ℝ) ^ b * tau μ N P a B θ) =
      fun N : ℕ => ∑ p ∈ P, (N : ℝ) ^ b * orderRemainder μ N p (a p) (rawConstant B θ) := by
    funext N
    simp only [tau, Finset.mul_sum, orderRemainder]
  rw [heq]
  have ht := tendsto_finset_sum P (fun p hpP => orderRemainder_weighted_tendsto_zero μ
    (hp p hpP) (ha p hpP) (rawConstant_pos hB hθ hθ1) hq hint (hm p hpP))
  simpa using ht

/-- A finite fourth moment makes τ_N vanish, including SK at its critical
moment endpoint. No quantitative rate is assumed for the law. -/
theorem tau_tendsto_zero_fourth (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 < a p)
    (hp : ∀ p ∈ P, 2 ≤ p) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < θ) (hθ1 : θ < 1)
    (h4 : Integrable (fun x : ℝ => |x| ^ (4 : ℕ)) μ) :
    Tendsto (fun N : ℕ => tau μ N P a B θ) atTop (𝓝 0) := by
  have h4r : Integrable (fun x : ℝ => |x| ^ (4 : ℝ)) μ := by
    simpa only [Real.rpow_ofNat] using h4
  have hm : ∀ p ∈ P, (p : ℝ) + 0 ≤ (((p : ℝ)-1)/2) * 4 := by
    intro p hpP
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp p hpP
    linarith
  simpa only [Real.rpow_zero, one_mul] using
    tau_weighted_tendsto_zero μ P a ha hp hB hθ hθ1 (by norm_num : (0 : ℝ) ≤ 4) h4r hm

/-- The moment threshold stated using the minimum interaction order implies
all orderwise inequalities, including its equality endpoint. -/
theorem moment_threshold_all_orders {pm p : ℕ} {m b : ℝ}
    (hpm : 2 ≤ pm) (hpp : pm ≤ p) (hb : 0 < b)
    (hm : 2 * ((pm : ℝ) + b) / ((pm : ℝ)-1) ≤ m) :
    0 ≤ m ∧ (p : ℝ) + b ≤ (((p : ℝ)-1)/2) * m := by
  have hpm' : (2 : ℝ) ≤ pm := by exact_mod_cast hpm
  have hpp' : (pm : ℝ) ≤ p := by exact_mod_cast hpp
  have hd : 0 < (pm : ℝ)-1 := by linarith
  have hm' := (div_le_iff₀ hd).mp hm
  have hm2 : 2 ≤ m := by nlinarith
  constructor
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hpp') (sub_nonneg.mpr hm2)]

/-- Remark 1.2(ii): finite real m-th moment at the stated threshold implies
τ_N=o(N⁻ᵇ) for every finite mixture in the theorem. -/
theorem tau_polynomial_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 < a p)
    (pm : ℕ) (hpm : 2 ≤ pm) (hpp : ∀ p ∈ P, pm ≤ p)
    {B θ m b : ℝ} (hB : 0 < B) (hθ : 0 < θ) (hθ1 : θ < 1) (hb : 0 < b)
    (hm : 2 * ((pm : ℝ)+b) / ((pm : ℝ)-1) ≤ m)
    (hint : Integrable (fun x : ℝ => |x| ^ m) μ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ b * tau μ N P a B θ) atTop (𝓝 0) := by
  exact tau_weighted_tendsto_zero μ P a ha (fun p hp => hpm.trans (hpp p hp))
    hB hθ hθ1 (moment_threshold_all_orders hpm le_rfl hb hm).1 hint
    (fun p hp => (moment_threshold_all_orders hpm (hpp p hp) hb hm).2)

/-- The asymptotic estimate yields the explicit eventual probability budget. -/
theorem tau_eventually_le_half_power (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 < a p)
    (pm : ℕ) (hpm : 2 ≤ pm) (hpp : ∀ p ∈ P, pm ≤ p)
    {B θ m b : ℝ} (hB : 0 < B) (hθ : 0 < θ) (hθ1 : θ < 1) (hb : 0 < b)
    (hm : 2 * ((pm : ℝ)+b) / ((pm : ℝ)-1) ≤ m)
    (hint : Integrable (fun x : ℝ => |x| ^ m) μ) :
    ∀ᶠ N : ℕ in atTop, tau μ N P a B θ ≤ (1/2 : ℝ) * (N : ℝ) ^ (-b) := by
  have hz := tau_polynomial_tendsto_zero μ P a ha pm hpm hpp hB hθ hθ1 hb hm hint
  filter_upwards [hz.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  rw [Real.rpow_neg hNr.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hNr b)).mpr
  simpa only [mul_comm] using hN

theorem orderRemainder_eventually_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p : ℕ} (hp : 2 ≤ p) {ap c M : ℝ} (ha : 0 < ap) (hc : 0 < c)
    (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ M) :
    ∀ᶠ N : ℕ in atTop, orderRemainder μ N p ap c = 0 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : 0 < ((p : ℝ)-1)/2 := by linarith
  have ht : Tendsto (fun N : ℕ => (c/ap)*(N : ℝ)^(((p : ℝ)-1)/2)) atTop atTop :=
    Tendsto.const_mul_atTop (div_pos hc ha)
      ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually (eventually_ge_atTop M)] with N hNM
  unfold orderRemainder
  rw [scaled_tail_event N p ha c]
  have hz : μ {x : ℝ | c/ap*(N : ℝ)^(((p : ℝ)-1)/2) < |x|} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hbound] with x hx
    exact not_lt_of_ge (hx.trans hNM)
  rw [(measureReal_eq_zero_iff (measure_ne_top μ _)).mpr hz, mul_zero]

/-- Bounded disorder makes the entire finite-mixture remainder zero eventually. -/
theorem tau_eventually_zero_of_bounded (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 < a p)
    (hp : ∀ p ∈ P, 2 ≤ p) {B θ M : ℝ}
    (hB : 0 < B) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hbound : ∀ᵐ x : ℝ ∂μ, |x| ≤ M) :
    ∀ᶠ N : ℕ in atTop, tau μ N P a B θ = 0 := by
  have hall : ∀ p ∈ P, ∀ᶠ N : ℕ in atTop,
      orderRemainder μ N p (a p) (rawConstant B θ) = 0 := by
    intro p hpP
    exact orderRemainder_eventually_zero μ (hp p hpP) (ha p hpP)
      (rawConstant_pos hB hθ hθ1) hbound
  have hh := (Filter.eventually_all_finset P).mpr hall
  filter_upwards [hh] with N hN
  exact Finset.sum_eq_zero hN

end Manuscript.UniformTau
