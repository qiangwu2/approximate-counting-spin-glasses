import Manuscript.ConditionalLowerTail
import Manuscript.DisorderOrthogonality
import SpinGlass.DisorderSigns

/-!
# Restricted negative moments under actual symmetric iid real disorder

The finite-sign estimate is integrated against the original probability law.
Integrability is proved by domination, including laws with atoms at zero.
The explicit averaged inflated graphical mass remains on the right; no uniform
second-moment constant or final manuscript lower-tail bound is assumed.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.DisorderLowerTail
open MeasureTheory SpinGlass.Expansion SpinGlass.Disorder

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The actual field-dependent normalized exponential partition function. -/
def normalizedGraph (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (J : E → ℝ) : ℝ :=
  FieldExpansion.normalizedPartition incidence edges h (fun e => a e * J e)

theorem normalizedGraph_eq_sum (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (J : E → ℝ) :
    normalizedGraph incidence edges h a J = ∑ Γ ∈ edges.powerset,
      Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card * monomial a Γ J := by
  rw [normalizedGraph, FieldExpansion.normalizedPartition_eq_graph_sum]
  rfl

theorem normalizedGraph_pos (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (J : E → ℝ) : 0 < normalizedGraph incidence edges h a J :=
  FieldExpansion.normalizedPartition_pos _ _ _ _

theorem continuous_normalizedGraph (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) : Continuous (normalizedGraph incidence edges h a) := by
  have heq : normalizedGraph incidence edges h a = fun J => ∑ Γ ∈ edges.powerset,
      Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card * monomial a Γ J :=
    funext (normalizedGraph_eq_sum incidence edges h a)
  rw [heq]
  exact continuous_finsetSum _ fun Γ _ => (continuous_monomial a Γ).const_mul _

/-- The actual measurable inflation event. -/
def inflationCutoff (edges : Finset E) (a : E → ℝ) (θ : ℝ) : Set (E → ℝ) :=
  {J | ∀ e ∈ edges, |weight (a e) (J e) / θ| ≤ 1 / 2}

theorem measurableSet_inflationCutoff (edges : Finset E) (a : E → ℝ) (θ : ℝ) :
    MeasurableSet (inflationCutoff edges a θ) := by
  unfold inflationCutoff
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun _ => measurableSet_le
    ((((continuous_weight (a e)).comp (continuous_apply e)).div_const θ).abs.measurable)
    measurable_const

theorem weight_signedArray (a : E → ℝ) (J : E → ℝ) (η : E → Bool) (e : E) :
    weight (a e) (signedArray J η e) = weight (a e) (J e) * spinSign (η e) := by
  cases hη : η e <;> simp [signedArray, weight, spinSign, hη]

theorem inflationCutoff_signedArray_iff (edges : Finset E) (a : E → ℝ)
    (θ : ℝ) (J : E → ℝ) (η : E → Bool) :
    signedArray J η ∈ inflationCutoff edges a θ ↔ J ∈ inflationCutoff edges a θ := by
  simp only [inflationCutoff, Set.mem_setOf_eq, weight_signedArray,
    abs_div, abs_mul, abs_spinSign, mul_one]

/-- The random inflated all-graph mass; the field factor is retained. -/
def inflatedMass (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (θ : ℝ) (J : E → ℝ) : ℝ :=
  ∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
    ∏ e ∈ Γ, (weight (a e) (J e) / θ) ^ 2

theorem inflatedMass_nonneg (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (θ : ℝ) (J : E → ℝ) :
    0 ≤ inflatedMass incidence edges h a θ J := by
  apply Finset.sum_nonneg
  intro Γ hΓ
  apply mul_nonneg
  · rw [pow_mul]
    positivity
  · exact Finset.prod_nonneg (fun e he => sq_nonneg _)

private theorem integrable_inflated_product (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : E → ℝ) (θ : ℝ) (Γ : Finset E) :
    Integrable (fun J => ∏ e ∈ Γ, (weight (a e) (J e) / θ) ^ 2) (iidLaw μ) := by
  have hi : Integrable (fun J => monomial a Γ J ^ 2) (iidLaw μ) := by
    simpa only [sq] using integrable_monomial_mul μ a Γ Γ
  convert hi.div_const ((θ ^ Γ.card) ^ 2) using 1
  funext J
  simp only [monomial, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
    Finset.prod_const, ← pow_mul]

theorem integrable_inflatedMass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (a : E → ℝ) (θ : ℝ) :
    Integrable (inflatedMass incidence edges h a θ) (iidLaw μ) := by
  exact integrable_finsetSum _ fun Γ _ => (integrable_inflated_product μ a θ Γ).const_mul _

/-- The expected inflated mass is exactly its true edge-variance graphical sum. -/
theorem integral_inflatedMass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (θ : ℝ) :
    (∫ J, inflatedMass incidence edges h a θ J ∂iidLaw μ) =
      ∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
        ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2 := by
  unfold inflatedMass
  rw [integral_finsetSum _ (fun Γ _ => (integrable_inflated_product μ a θ Γ).const_mul _)]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [integral_const_mul]
  congr 1
  calc
    _ = (∫ J, monomial a Γ J ^ 2 ∂iidLaw μ) / (θ ^ Γ.card) ^ 2 := by
      rw [← integral_div]
      congr 1
      funext J
      simp only [monomial, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
        Finset.prod_const, ← pow_mul]
    _ = (∏ e ∈ Γ, secondMoment μ (a e)) / (θ ^ Γ.card) ^ 2 := by
      have hd := SpinGlass.Disorder.monomial_orthogonality μ hμ a Γ Γ
      simpa only [ite_true, ← sq] using congrArg (fun t => t / (θ ^ Γ.card) ^ 2) hd
    _ = _ := by
      simp only [Finset.prod_div_distrib, Finset.prod_const, ← pow_mul, Nat.mul_comm]

/-- The inverse power restricted to the actual inflation event. -/
def restrictedNegativeMoment (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (θ : ℝ) (J : E → ℝ) : ℝ := by
  classical
  exact if J ∈ inflationCutoff edges a θ then
    normalizedGraph incidence edges h a J ^ (-ConditionalLowerTail.exponent θ) else 0

theorem restricted_negative_signMean_le (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (J : E → ℝ) :
    spinMean (fun η => restrictedNegativeMoment incidence edges h a θ (signedArray J η)) ≤
      inflatedMass incidence edges h a θ J := by
  classical
  unfold restrictedNegativeMoment
  by_cases hJ : J ∈ inflationCutoff edges a θ
  · have hη (η : E → Bool) : signedArray J η ∈ inflationCutoff edges a θ :=
      (inflationCutoff_signedArray_iff edges a θ J η).mpr hJ
    simp only [hη, ite_true]
    have heq (η : E → Bool) : normalizedGraph incidence edges h a (signedArray J η) =
        FieldExpansion.normalizedPartition incidence edges h
          (fun e => (a e * J e) * spinSign (η e)) := by
      simp only [normalizedGraph, signedArray, mul_assoc]
    simp_rw [heq]
    exact ConditionalLowerTail.partition_negative_moment_le_graph_mass incidence edges h
      (fun e => a e * J e) hθ hθ1 hJ
  · have hη (η : E → Bool) : signedArray J η ∉ inflationCutoff edges a θ :=
      fun hi => hJ ((inflationCutoff_signedArray_iff edges a θ J η).mp hi)
    simp only [hη, ite_false, spinMean, Finset.sum_const_zero, mul_zero]
    exact inflatedMass_nonneg incidence edges h a θ J

/-- The restricted inverse power is integrable; this is proved, not a premise. -/
theorem integrable_restrictedNegativeMoment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (a : E → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    Integrable (restrictedNegativeMoment incidence edges h a θ) (iidLaw μ) := by
  classical
  let F := restrictedNegativeMoment incidence edges h a θ
  have hFnonneg (J : E → ℝ) : 0 ≤ F J := by
    dsimp [F, restrictedNegativeMoment]
    split_ifs
    · exact Real.rpow_nonneg (normalizedGraph_pos incidence edges h a J).le _
    · exact le_rfl
  have hFmeas : Measurable F :=
    ((continuous_normalizedGraph incidence edges h a).measurable.pow_const _).ite
      (measurableSet_inflationCutoff edges a θ) measurable_const
  refine ((integrable_inflatedMass μ incidence edges h a θ).const_mul
    ((2 : ℝ) ^ Fintype.card E)).mono' hFmeas.aestronglyMeasurable ?_
  apply ae_of_all
  intro J
  rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg J)]
  have hsingle := Finset.single_le_sum
    (s := (Finset.univ : Finset (E → Bool))) (f := fun η => F (signedArray J η))
    (fun η _ => hFnonneg _) (Finset.mem_univ (fun _ : E => false))
  have hid : signedArray J (fun _ : E => false) = J := by
    funext e
    simp [signedArray, spinSign]
  rw [hid] at hsingle
  have hmean := mul_le_mul_of_nonneg_left
    (restricted_negative_signMean_le incidence edges h a hθ hθ1 J)
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Fintype.card E))
  have hscale : (2 : ℝ) ^ Fintype.card E * spinMean (fun η => F (signedArray J η)) =
      ∑ η : E → Bool, F (signedArray J η) := by
    rw [spinMean, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt (pow_pos (by norm_num) _)), one_mul]
  exact hsingle.trans (by simpa only [F, ← hscale] using hmean)

/-- Restricted negative moment under the original symmetric iid law, with the
actual averaged all-graph mass and no integrability or mass-bound assumption. -/
theorem restricted_negative_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ J, restrictedNegativeMoment incidence edges h a θ J ∂iidLaw μ) ≤
      ∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
        ∏ e ∈ Γ, secondMoment μ (a e) / θ ^ 2 := by
  rw [← integral_signMean_eq_of_integrable μ hμ _
    (integrable_restrictedNegativeMoment μ incidence edges h a hθ hθ1)]
  rw [← integral_inflatedMass μ hμ incidence edges h a θ]
  apply integral_mono_of_nonneg _ (integrable_inflatedMass μ incidence edges h a θ)
    (ae_of_all _ (restricted_negative_signMean_le incidence edges h a hθ hθ1))
  apply ae_of_all
  intro J
  unfold spinMean
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro η hη
  unfold restrictedNegativeMoment
  split_ifs
  · exact Real.rpow_nonneg (normalizedGraph_pos incidence edges h a _).le _
  · exact le_rfl


/-- The generic normalized graph is exactly the physical mixed-input model. -/
theorem normalizedGraph_physical (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Model.Edge N P → ℝ) :
    normalizedGraph Subtype.val Finset.univ h
      (DisorderOrthogonality.physicalScale N P a beta) J =
        Model.normalizedPartition N P a beta h J := by
  unfold normalizedGraph
  rw [Model.normalizedPartition_eq_fieldNormalized]
  congr 1
  funext e
  exact (DisorderOrthogonality.coefficient_eq_physicalScale N P a beta J e).symm

/-- The restricted inverse moment for the literal mixed-field partition on
its actual physical iid input array. The inflation-event restriction is explicit. -/
theorem physical_restricted_negative_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ J in inflationCutoff Finset.univ (DisorderOrthogonality.physicalScale N P a beta) θ,
      Model.normalizedPartition N P a beta h J ^ (-ConditionalLowerTail.exponent θ)
        ∂iidLaw μ) ≤
      ∑ Γ ∈ (Finset.univ : Finset (Model.Edge N P)).powerset,
        Real.tanh h ^ (2 * (FieldExpansion.boundary Subtype.val Γ).card) *
          ∏ e ∈ Γ, secondMoment μ (DisorderOrthogonality.physicalScale N P a beta e) / θ ^ 2 := by
  classical
  have hm := restricted_negative_moment μ hμ
    (Subtype.val : Model.Edge N P → Finset (Fin N)) Finset.univ h
    (DisorderOrthogonality.physicalScale N P a beta) hθ hθ1
  rw [← integral_indicator (measurableSet_inflationCutoff Finset.univ
    (DisorderOrthogonality.physicalScale N P a beta) θ)]
  simpa only [Set.indicator_apply, restrictedNegativeMoment, normalizedGraph_physical] using hm

end Manuscript.DisorderLowerTail
