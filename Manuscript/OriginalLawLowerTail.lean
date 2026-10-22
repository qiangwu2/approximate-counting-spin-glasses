import Manuscript.DisorderLowerTail
import Mathlib.Analysis.SpecialFunctions.Artanh

/-! Lower-tail probabilities and the raw-disorder cutoff under the original
real iid law, including arbitrary atoms and zero interaction temperature. -/

noncomputable section
open scoped BigOperators
namespace Manuscript.OriginalLawLowerTail
open MeasureTheory SpinGlass.Disorder Manuscript.DisorderLowerTail

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem normalizedGraph_lower_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) {θ z : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) :
    (iidLaw μ).real {J | normalizedGraph incidence edges h a J < z} ≤
      (∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
        ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2) * z ^ ConditionalLowerTail.exponent θ +
      (iidLaw μ).real (inflationCutoff edges a θ)ᶜ := by
  classical
  let s := ConditionalLowerTail.exponent θ
  let F := {J | normalizedGraph incidence edges h a J < z}.indicator
    (1 : (E → ℝ) → ℝ)
  let B := (inflationCutoff edges a θ)ᶜ.indicator (1 : (E → ℝ) → ℝ)
  have hs : 0 < s := ConditionalLowerTail.exponent_pos hθ hθ1
  have hFe : MeasurableSet {J | normalizedGraph incidence edges h a J < z} :=
    measurableSet_lt (continuous_normalizedGraph incidence edges h a).measurable measurable_const
  have hFi : Integrable F (iidLaw μ) := (integrable_const (1 : ℝ)).indicator hFe
  have hBi : Integrable B (iidLaw μ) := (integrable_const (1 : ℝ)).indicator
    (measurableSet_inflationCutoff edges a θ).compl
  have hRi := integrable_restrictedNegativeMoment μ incidence edges h a hθ hθ1
  have hpoint (J : E → ℝ) : F J ≤
      restrictedNegativeMoment incidence edges h a θ J * z ^ s + B J := by
    by_cases hJ : J ∈ inflationCutoff edges a θ
    · have hpos := normalizedGraph_pos incidence edges h a J
      by_cases hsmall : normalizedGraph incidence edges h a J < z
      · have hp := Real.rpow_le_rpow_of_nonpos hpos hsmall.le (neg_nonpos.mpr hs.le)
        have hm := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hz.le s)
        have hc : z ^ (-s) * z ^ s = 1 := by
          rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
        rw [hc] at hm
        simpa [F, B, Set.indicator, restrictedNegativeMoment, hJ, hsmall, s] using hm
      · simp only [F, B, Set.indicator_apply, Set.mem_setOf_eq, hsmall, ite_false,
          Set.mem_compl_iff, hJ, not_true_eq_false, restrictedNegativeMoment, ite_true, add_zero]
        exact mul_nonneg (Real.rpow_nonneg hpos.le _) (Real.rpow_nonneg hz.le _)
    · simp only [F, B, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_compl_iff,
        hJ, not_false_eq_true, ite_true, restrictedNegativeMoment, ite_false, zero_mul, zero_add]
      split_ifs <;> norm_num
  have hi := integral_mono hFi ((hRi.mul_const _).add hBi) hpoint
  have hFint : (∫ J, F J ∂iidLaw μ) =
      (iidLaw μ).real {J | normalizedGraph incidence edges h a J < z} :=
    integral_indicator_one hFe
  have hBint : (∫ J, B J ∂iidLaw μ) = (iidLaw μ).real (inflationCutoff edges a θ)ᶜ :=
    integral_indicator_one (measurableSet_inflationCutoff edges a θ).compl
  simp only [Pi.add_apply] at hi
  rw [hFint, integral_add (hRi.mul_const _) hBi, integral_mul_const, hBint] at hi
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_right
    (restricted_negative_moment μ hμ incidence edges h a hθ hθ1)
      (Real.rpow_nonneg hz.le s)) le_rfl)

theorem tanh_monotone : Monotone Real.tanh := by
  intro x y hxy
  have h := (Real.artanh_le_artanh_iff
    (show Real.tanh x ∈ Set.Ioo (-1) 1 from ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩)
    (show Real.tanh y ∈ Set.Ioo (-1) 1 from ⟨Real.neg_one_lt_tanh y, Real.tanh_lt_one y⟩)).mp
  exact h (by simpa only [Real.artanh_tanh] using hxy)

theorem abs_tanh_eq_tanh_abs (x : ℝ) : |Real.tanh x| = Real.tanh |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg]
    simpa using tanh_monotone hx
  · have hs : Real.tanh x ≤ 0 := by
      simpa using tanh_monotone hx
    rw [abs_of_nonpos hx, Real.tanh_neg, abs_of_nonpos hs]

theorem inflation_le_half_of_coefficient_bound {θ x : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hx : |x| ≤ Real.artanh (θ / 2)) :
    |Real.tanh x / θ| ≤ 1 / 2 := by
  have ht : |Real.tanh x| ≤ θ / 2 := by
    rw [abs_tanh_eq_tanh_abs]
    have ht := tanh_monotone hx
    rwa [Real.tanh_artanh (show θ / 2 ∈ Set.Ioo (-1) 1 from ⟨by linarith, by linarith⟩)] at ht
  rw [abs_div, abs_of_pos hθ]
  exact (div_le_iff₀ hθ).mpr (by linarith)

/-- The proof event for a general mixed input: its thresholds are unscaled
physical disorder thresholds, so temperature zero causes no division by zero. -/
def rawCutoff (edges : Finset E) (amplitude threshold : E → ℝ) : Set (E → ℝ) :=
  {J | ∀ e ∈ edges, |amplitude e * J e| ≤ threshold e}

theorem measurableSet_rawCutoff (edges : Finset E) (amplitude threshold : E → ℝ) :
    MeasurableSet (rawCutoff edges amplitude threshold) := by
  unfold rawCutoff
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun _ =>
    measurableSet_le ((show Continuous (fun J : E → ℝ => J e) from
      continuous_apply e).const_mul (amplitude e)).abs.measurable measurable_const

theorem rawCutoff_failure_le_sum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (edges : Finset E) (amplitude threshold : E → ℝ) :
    (iidLaw μ).real (rawCutoff edges amplitude threshold)ᶜ ≤
      ∑ e ∈ edges, μ.real {x : ℝ | threshold e < |amplitude e * x|} := by
  classical
  have heq : (rawCutoff edges amplitude threshold)ᶜ =
      ⋃ e ∈ edges, {J : E → ℝ | threshold e < |amplitude e * J e|} := by
    ext J
    simp [rawCutoff, not_forall, not_le]
  rw [heq]
  apply (measureReal_biUnion_finset_le edges _).trans
  apply Finset.sum_le_sum
  intro e he
  have hp := measurePreserving_eval (μ := fun _ : E => μ) e
  have hm : MeasurableSet {x : ℝ | threshold e < |amplitude e * x|} :=
    measurableSet_lt measurable_const (continuous_id.const_mul (amplitude e)).abs.measurable
  have h := map_measureReal_apply (μ := iidLaw μ) (measurable_pi_apply e) hm
  rw [show (iidLaw μ).map (Function.eval e) = μ from hp.map_eq] at h
  exact h.symm.le

def rawConstant (beta0 θ : ℝ) : ℝ := Real.artanh (θ / 2) / beta0

def physicalRawCutoff (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta0 θ : ℝ) :
    Set (Model.Edge N P → ℝ) :=
  rawCutoff Finset.univ (fun e => a e.val.card)
    (fun e => rawConstant beta0 θ * Model.scaleDenominator N e.val.card)

/-- The exact remainder in Theorem 1.1, summed over active interaction orders. -/
def tau (μ : Measure ℝ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta0 θ : ℝ) : ℝ :=
  ∑ p ∈ P, (N.choose p : ℝ) * μ.real {x : ℝ |
    rawConstant beta0 θ * Model.scaleDenominator N p < |a p * x|}

theorem rawConstant_pos {beta0 θ : ℝ} (hB : 0 < beta0)
    (hθ : 0 < θ) (hθ1 : θ < 1) : 0 < rawConstant beta0 θ :=
  div_pos (Real.artanh_pos ⟨by linarith, by linarith⟩) hB

theorem scaleDenominator_pos {N : ℕ} (hN : 0 < N) (p : ℕ) :
    0 < Model.scaleDenominator N p := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _

/-- Exact regrouping of distinct unordered edges by their order. -/
theorem sum_physical_orders (N : ℕ) (P : Finset ℕ) (f : ℕ → ℝ) :
    (∑ e : Model.Edge N P, f e.val.card) = ∑ p ∈ P, (N.choose p : ℝ) * f p := by
  classical
  rw [← Finset.sum_subtype (Model.physicalEdges N P) (fun _ => Iff.rfl)
    (fun e => f e.card)]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun e he => Model.mem_physicalEdges.mp he)]
  apply Finset.sum_congr rfl
  intro p hp
  have heq : (Model.physicalEdges N P).filter (fun e => e.card = p) =
      (Finset.univ : Finset (Fin N)).powersetCard p := by
    ext e
    simp only [Finset.mem_filter, Model.mem_physicalEdges, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact ⟨fun he => he.2, fun he => ⟨he ▸ hp, he⟩⟩
  rw [heq]
  calc
    _ = ∑ _e ∈ (Finset.univ : Finset (Fin N)).powersetCard p, f p := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(Finset.mem_powersetCard.mp he).2]
    _ = _ := by simp

theorem physicalRawCutoff_failure_le_tau (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta0 θ : ℝ) :
    (iidLaw μ).real (physicalRawCutoff N P a beta0 θ)ᶜ ≤ tau μ N P a beta0 θ := by
  have h := rawCutoff_failure_le_sum μ (Finset.univ : Finset (Model.Edge N P))
    (fun e => a e.val.card)
    (fun e => rawConstant beta0 θ * Model.scaleDenominator N e.val.card)
  exact h.trans_eq (sum_physical_orders N P (fun p => μ.real {x : ℝ |
    rawConstant beta0 θ * Model.scaleDenominator N p < |a p * x|}))

theorem physicalRawCutoff_subset_inflation {N : ℕ} (hN : 0 < N)
    (P : Finset ℕ) (a : ℕ → ℝ) {beta beta0 θ : ℝ}
    (hβ : 0 ≤ beta) (hβB : beta ≤ beta0) (hB : 0 < beta0)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    physicalRawCutoff N P a beta0 θ ⊆
      inflationCutoff Finset.univ (DisorderOrthogonality.physicalScale N P a beta) θ := by
  intro J hJ e he
  apply inflation_le_half_of_coefficient_bound hθ hθ1
  have hd := scaleDenominator_pos hN e.val.card
  have hc := rawConstant_pos hB hθ hθ1
  have hraw := hJ e he
  have hid : |DisorderOrthogonality.physicalScale N P a beta e * J e| =
      beta * |a e.val.card * J e| / Model.scaleDenominator N e.val.card := by
    unfold DisorderOrthogonality.physicalScale
    rw [div_mul_eq_mul_div, mul_assoc, abs_div, abs_mul, abs_of_nonneg hβ, abs_of_pos hd]
  rw [hid]
  calc
    _ ≤ beta * (rawConstant beta0 θ * Model.scaleDenominator N e.val.card) /
        Model.scaleDenominator N e.val.card :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hraw hβ) hd.le
    _ = beta * rawConstant beta0 θ := by field_simp
    _ ≤ beta0 * rawConstant beta0 θ := mul_le_mul_of_nonneg_right hβB hc.le
    _ = Real.artanh (θ / 2) := by unfold rawConstant; field_simp

/-- Proposition 5.4's probability reduction with the manuscript's literal raw
tail remainder; only the separate uniform graphical-mass estimate remains to
be inserted into the explicit finite sum on the right. -/
theorem physical_lower_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) {N : ℕ} (hN : 0 < N)
    (P : Finset ℕ) (a : ℕ → ℝ) (h : ℝ) {beta beta0 θ z : ℝ}
    (hβ : 0 ≤ beta) (hβB : beta ≤ beta0) (hB : 0 < beta0)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z) :
    (iidLaw μ).real {J | Model.normalizedPartition N P a beta h J < z} ≤
      (∑ Γ ∈ (Finset.univ : Finset (Model.Edge N P)).powerset,
        Real.tanh h ^ (2 * (FieldExpansion.boundary Subtype.val Γ).card) *
          ∏ e ∈ Γ, secondMoment μ (DisorderOrthogonality.physicalScale N P a beta e) / θ ^ 2) *
        z ^ ConditionalLowerTail.exponent θ + tau μ N P a beta0 θ := by
  have hb := normalizedGraph_lower_tail μ hμ
    (Subtype.val : Model.Edge N P → Finset (Fin N)) Finset.univ h
    (DisorderOrthogonality.physicalScale N P a beta) hθ hθ1 hz
  simp_rw [normalizedGraph_physical] at hb
  apply hb.trans
  apply add_le_add le_rfl
  apply (measureReal_mono (Set.compl_subset_compl.mpr
    (physicalRawCutoff_subset_inflation hN P a hβ hβB hB hθ hθ1))
      (measure_ne_top _ _)).trans
  exact physicalRawCutoff_failure_le_tau μ N P a beta0 θ

end Manuscript.OriginalLawLowerTail
