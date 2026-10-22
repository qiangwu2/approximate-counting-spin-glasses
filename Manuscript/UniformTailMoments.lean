import Manuscript.OriginalLawLowerTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Sharp absolute-moment tails, including the endpoint critical exponent. -/
noncomputable section
namespace Manuscript.UniformTailMoments
open MeasureTheory Filter
open scoped Topology

/-- The moment integral on a moving absolute tail vanishes at infinity. -/
theorem abs_tail_integral_tendsto_zero (μ : Measure ℝ) {q : ℝ}
    (hint : Integrable (fun x : ℝ => |x|^q) μ) :
    Tendsto (fun t : ℝ => ∫ x in {x : ℝ | t< |x|}, |x|^q ∂μ) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone
    (μ:=μ) (f:=fun x : ℝ => |x|^q) (s:=fun t : ℝ => {x : ℝ | t< |x|})
    (fun t => measurableSet_lt measurable_const continuous_abs.measurable)
    (fun s t hst x hx => lt_of_le_of_lt hst hx) ⟨0,hint.integrableOn⟩
  have hempty : (⋂ t : ℝ, {x : ℝ | t< |x|})=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact lt_irrefl |x| ((Set.mem_iInter.mp hx) |x|)
  simpa only [hempty, Measure.restrict_empty, integral_zero_measure] using h

/-- The sharp tail-moment inequality retains the truncated moment on the right. -/
theorem rpow_mul_abs_tail_le_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ)
    {t : ℝ} (ht : 0≤t) :
    t^q * μ.real {x : ℝ | t< |x|} ≤ ∫ x in {x : ℝ | t< |x|}, |x|^q ∂μ := by
  have hs : MeasurableSet {x : ℝ | t< |x|} := measurableSet_lt measurable_const continuous_abs.measurable
  calc
    _ = ∫ _x in {x : ℝ | t< |x|}, t^q ∂μ := by rw [setIntegral_const]; simp [mul_comm]
    _ ≤ _ := integral_mono_ae (integrable_const _) hint.integrableOn
      ((ae_restrict_mem hs).mono (fun x hx => Real.rpow_le_rpow ht hx.le hq))

/-- Finite real q-th moment implies the strict little-o tail estimate t^q P(|J|>t)→0. -/
theorem rpow_mul_abs_tail_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ) :
    Tendsto (fun t : ℝ => t^q * μ.real {x : ℝ | t< |x|}) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (abs_tail_integral_tendsto_zero μ hint)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht _) MeasureTheory.measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact rpow_mul_abs_tail_le_integral μ hq hint ht

/-- Ordinary Markov inequality for a genuinely real absolute moment exponent. -/
theorem abs_tail_le_real_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ)
    {t : ℝ} (ht : 0<t) :
    μ.real {x : ℝ | t< |x|} ≤ (∫ x, |x|^q ∂μ)/t^q := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ:=μ) (f:=fun x : ℝ => |x|^q)
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _) hint (t^q)
  have hs : {x : ℝ | t< |x|} ⊆ {x : ℝ | t^q≤|x|^q} :=
    fun x hx => Real.rpow_le_rpow ht.le hx.le hq
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht _)).mpr
  calc
    μ.real {x : ℝ | t< |x|} * t^q ≤ μ.real {x : ℝ | t^q≤|x|^q} * t^q :=
      mul_le_mul_of_nonneg_right (measureReal_mono hs (measure_ne_top μ _))
        (Real.rpow_nonneg ht.le _)
    _ ≤ _ := by simpa only [mul_comm] using hm

/-- Polynomially rescaled tails vanish even at the critical moment exponent. -/
theorem scaled_abs_tail_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q c d r : ℝ} (hq : 0≤q) (hint : Integrable (fun x : ℝ => |x|^q) μ)
    (hc : 0<c) (hd : 0<d) (hr : r≤d*q) :
    Tendsto (fun N : ℕ => (N:ℝ)^r * μ.real {x : ℝ | c*(N:ℝ)^d < |x|}) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => c*(N:ℝ)^d) atTop atTop :=
    Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop)
  have hz := ((rpow_mul_abs_tail_tendsto_zero μ hq hint).comp ht).const_mul (c^(-q))
  simp only [mul_zero] at hz
  apply squeeze_zero' _ _ hz
  · exact Filter.Eventually.of_forall (fun N =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) MeasureTheory.measureReal_nonneg)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
    have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
    have hcancel : c^(-q)*(c*(N:ℝ)^d)^q=(N:ℝ)^(d*q) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hN0 _), Real.rpow_neg hc.le,
        ← Real.rpow_mul hN0, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hc q)), one_mul]
    calc
      (N:ℝ)^r * μ.real {x : ℝ | c*(N:ℝ)^d < |x|} ≤
          (N:ℝ)^(d*q) * μ.real {x : ℝ | c*(N:ℝ)^d < |x|} :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hr)
          MeasureTheory.measureReal_nonneg
      _ = c^(-q)*((c*(N:ℝ)^d)^q*μ.real {x : ℝ | c*(N:ℝ)^d < |x|}) := by
        rw [← mul_assoc,hcancel]


end Manuscript.UniformTailMoments
