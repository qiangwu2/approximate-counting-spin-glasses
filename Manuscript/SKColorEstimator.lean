import Manuscript.SKGraphBasics
import Manuscript.DisorderOrthogonality
import SpinGlass.ColoringEstimator
import SpinGlass.FiniteProbability

/-!
# The weak-field SK color estimator on its actual probability space

Every candidate branching set has its own repeated uniform vertex coloring.
The palette has `2L` colors, while `L` bounds original edges. The coefficients
here are the inverse-inclusion coefficients used by Algorithm 3. The subsequent
evaluator-correctness bridge connects these graph sums to coefficient arrays.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKColorEstimator

open MeasureTheory SpinGlass.Disorder
open SpinGlass.ColoringEstimator SpinGlass.ColoringProbability SpinGlass.ColoringRepetitions
open Manuscript.SKGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev Colors (V : Type*) (L R : ℕ) :=
  SpinGlass.ColoringEstimator.Colors V (Finset V) (2 * L) R

def colorLaw (V : Type*) [Fintype V] [DecidableEq V] (L R : ℕ) :
    Measure (Colors V L R) := SpinGlass.FiniteProbability.uniformLaw (Colors V L R)

instance colorLaw_probability {L R : ℕ} [Nonempty (Fin (2 * L))] :
    IsProbabilityMeasure (colorLaw V L R) := by
  unfold colorLaw
  infer_instance

def retained (incidence : E → Finset V) (edges : Finset E) (D L : ℕ) :
    Finset (Finset E) := edges.powerset.filter (Retained incidence D L)

def coefficient (incidence : E → Finset V) (L R : ℕ)
    (χ : Colors V L R) (Γ : Finset E) : ℝ :=
  graphCoefficient (outside incidence) (branch incidence) (2 * L) R χ Γ

def retainedSum (incidence : E → Finset V) (edges : Finset E)
    (D L : ℕ) (h : ℝ) (a : E → ℝ) (J : E → ℝ) : ℝ :=
  ∑ Γ ∈ retained incidence edges D L,
    DisorderOrthogonality.graphWeight incidence h a Γ J

def estimator (incidence : E → Finset V) (edges : Finset E) (D L R : ℕ)
    (h : ℝ) (a : E → ℝ) (χ : Colors V L R) (J : E → ℝ) : ℝ :=
  ∑ Γ ∈ retained incidence edges D L,
    coefficient incidence L R χ Γ * DisorderOrthogonality.graphWeight incidence h a Γ J

def graphMass (μ : Measure ℝ) (incidence : E → Finset V)
    (h : ℝ) (a : E → ℝ) (Γ : Finset E) : ℝ :=
  Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
    ∏ e ∈ Γ, secondMoment μ (a e)

theorem graphMass_nonneg (μ : Measure ℝ) (incidence : E → Finset V)
    (h : ℝ) (a : E → ℝ) (Γ : Finset E) : 0 ≤ graphMass μ incidence h a Γ := by
  unfold graphMass
  apply mul_nonneg
  · rw [mul_comm 2, pow_mul]
    exact sq_nonneg _
  · exact Finset.prod_nonneg (fun e he => secondMoment_nonneg μ (a e))

theorem outside_card_of_mem_retained (incidence : E → Finset V) (edges : Finset E)
    (D L : ℕ) (hp : ∀ e ∈ edges, (incidence e).card = 2)
    (Γ : Finset E) (hΓ : Γ ∈ retained incidence edges D L) :
    (outside incidence Γ).card ≤ 2 * L := by
  obtain ⟨hsub, hkeep⟩ := Finset.mem_filter.mp hΓ
  exact retained_outside_card incidence D L Γ
    (fun e he => hp e (Finset.mem_powerset.mp hsub he)) hkeep

/-- The actual color average is conditionally unbiased for every real input. -/
theorem estimator_unbiased (incidence : E → Finset V) (edges : Finset E)
    (D : ℕ) {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hp : ∀ e ∈ edges, (incidence e).card = 2)
    (h : ℝ) (a : E → ℝ) (J : E → ℝ) :
    mean (fun χ : Colors V L R => estimator incidence edges D L R h a χ J) =
      retainedSum incidence edges D L h a J := by
  unfold estimator retainedSum coefficient
  rw [mean_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [mean_mul_const, mean_graphCoefficient
    (outside incidence) (branch incidence) (by omega) hR Γ
      (outside_card_of_mem_retained incidence edges D L hp Γ hΓ)]
  exact one_mul _

/-- The same unbiasedness under the actual finite uniform probability measure. -/
theorem estimator_integral (incidence : E → Finset V) (edges : Finset E)
    (D : ℕ) {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hp : ∀ e ∈ edges, (incidence e).card = 2)
    (h : ℝ) (a : E → ℝ) (J : E → ℝ) :
    (∫ χ, estimator incidence edges D L R h a χ J ∂colorLaw V L R) =
      retainedSum incidence edges D L h a J := by
  rw [colorLaw, SpinGlass.FiniteProbability.integral_uniformLaw]
  exact estimator_unbiased incidence edges D hL hR hp h a J

theorem coefficient_variance (incidence : E → Finset V) {L R : ℕ}
    (hL : 0 < L) (hR : 0 < R) (Γ : Finset E)
    (hΓ : (outside incidence Γ).card ≤ 2 * L) :
    (∫ χ : Colors V L R, (coefficient incidence L R χ Γ - 1) ^ 2
      ∂colorLaw V L R) =
      (1 - probability (2 * L) (outside incidence Γ).card) /
        ((R : ℝ) * probability (2 * L) (outside incidence Γ).card) := by
  rw [colorLaw, SpinGlass.FiniteProbability.integral_uniformLaw]
  exact mean_graphCoefficient_variance (outside incidence) (branch incidence)
    (by omega) hR Γ hΓ

/-- The repeated-color coefficient has variance at most `exp(2L)/R`. -/
theorem coefficient_variance_le (incidence : E → Finset V) {L R : ℕ}
    (hL : 0 < L) (hR : 0 < R) (Γ : Finset E)
    (hΓ : (outside incidence Γ).card ≤ 2 * L) :
    (1 - probability (2 * L) (outside incidence Γ).card) /
      ((R : ℝ) * probability (2 * L) (outside incidence Γ).card) ≤
        Real.exp (2 * (L : ℝ)) / (R : ℝ) := by
  have hb := mean_graphCoefficient_variance_le (outside incidence) (branch incidence)
    (by omega : 0 < 2 * L) hR Γ hΓ
  rw [mean_graphCoefficient_variance (outside incidence) (branch incidence)
    (by omega) hR Γ hΓ] at hb
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hb

/-- The squared error is a genuinely integrable function of colors and disorder. -/
theorem error_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (edges : Finset E) (D : ℕ)
    {L R : ℕ} (hL : 0 < L) (h : ℝ) (a : E → ℝ) :
    Integrable (fun χJ : Colors V L R × (E → ℝ) =>
      (estimator incidence edges D L R h a χJ.1 χJ.2 -
        retainedSum incidence edges D L h a χJ.2) ^ 2)
          ((colorLaw V L R).prod (iidLaw μ)) := by
  letI : Nonempty (Fin (2 * L)) := ⟨⟨0, by omega⟩⟩
  have heq (χJ : Colors V L R × (E → ℝ)) :
      estimator incidence edges D L R h a χJ.1 χJ.2 -
        retainedSum incidence edges D L h a χJ.2 =
      ∑ Γ ∈ retained incidence edges D L,
        (coefficient incidence L R χJ.1 Γ - 1) *
          DisorderOrthogonality.graphWeight incidence h a Γ χJ.2 := by
    simp only [estimator, retainedSum, sub_mul, one_mul, Finset.sum_sub_distrib]
  simp_rw [heq]
  exact DisorderOrthogonality.integrable_independent_graph_square μ (colorLaw V L R)
    incidence h a (retained incidence edges D L)
    (fun χ Γ => coefficient incidence L R χ Γ - 1)
    (fun Γ hΓ => measurable_of_countable _) (fun Γ hΓ => Integrable.of_finite)

/-- Exact color-error MSE on independent colors and the original symmetric iid law.
Shared coloring indicators may be correlated; disorder orthogonality removes their cross terms. -/
theorem coloring_mse_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (incidence : E → Finset V) (edges : Finset E) (D : ℕ)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hp : ∀ e ∈ edges, (incidence e).card = 2) (h : ℝ) (a : E → ℝ) :
    (∫ χJ : Colors V L R × (E → ℝ),
      (estimator incidence edges D L R h a χJ.1 χJ.2 -
        retainedSum incidence edges D L h a χJ.2) ^ 2
        ∂(colorLaw V L R).prod (iidLaw μ)) =
      ∑ Γ ∈ retained incidence edges D L,
        ((1 - probability (2 * L) (outside incidence Γ).card) /
          ((R : ℝ) * probability (2 * L) (outside incidence Γ).card)) *
            graphMass μ incidence h a Γ := by
  letI : Nonempty (Fin (2 * L)) := ⟨⟨0, by omega⟩⟩
  have hid := DisorderOrthogonality.independent_coefficient_error_second_moment
    μ hμ (colorLaw V L R) incidence h a (retained incidence edges D L)
    (fun χ Γ => coefficient incidence L R χ Γ) (fun _ _ => 1)
    (fun Γ hΓ => measurable_of_countable _) (fun Γ hΓ => Integrable.of_finite)
  calc
    _ = ∑ Γ ∈ retained incidence edges D L,
        (∫ χ : Colors V L R, (coefficient incidence L R χ Γ - 1) ^ 2
          ∂colorLaw V L R) * graphMass μ incidence h a Γ := by
      simpa only [estimator, retainedSum, one_mul, graphMass, mul_assoc] using hid
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Γ hΓ
      rw [coefficient_variance incidence hL hR Γ
        (outside_card_of_mem_retained incidence edges D L hp Γ hΓ)]

/-- The color-error bound before the separate uniform graph-mass estimate. -/
theorem coloring_mse_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (incidence : E → Finset V) (edges : Finset E) (D : ℕ)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hp : ∀ e ∈ edges, (incidence e).card = 2) (h : ℝ) (a : E → ℝ) :
    (∫ χJ : Colors V L R × (E → ℝ),
      (estimator incidence edges D L R h a χJ.1 χJ.2 -
        retainedSum incidence edges D L h a χJ.2) ^ 2
        ∂(colorLaw V L R).prod (iidLaw μ)) ≤
      (Real.exp (2 * (L : ℝ)) / (R : ℝ)) *
        ∑ Γ ∈ edges.powerset, graphMass μ incidence h a Γ := by
  rw [coloring_mse_eq μ hμ incidence edges D hL hR hp h a]
  calc
    _ ≤ ∑ Γ ∈ retained incidence edges D L,
        (Real.exp (2 * (L : ℝ)) / (R : ℝ)) * graphMass μ incidence h a Γ := by
      exact Finset.sum_le_sum (fun Γ hΓ => mul_le_mul_of_nonneg_right
        (coefficient_variance_le incidence hL hR Γ
          (outside_card_of_mem_retained incidence edges D L hp Γ hΓ))
        (graphMass_nonneg μ incidence h a Γ))
    _ = (Real.exp (2 * (L : ℝ)) / (R : ℝ)) *
        ∑ Γ ∈ retained incidence edges D L, graphMass μ incidence h a Γ := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun Γ _ _ => graphMass_nonneg μ incidence h a Γ))
      exact div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg R)

end Manuscript.SKColorEstimator
