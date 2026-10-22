import Manuscript.SKColorEstimator

/-! Exact orthogonal addition of truncation and color-averaging errors. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKColorEstimator
open MeasureTheory SpinGlass.Disorder
open SpinGlass.ColoringProbability Manuscript.SKGraph
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def fullCoefficient (incidence : E → Finset V) (D L R : ℕ)
    (χ : Colors V L R) (Γ : Finset E) : ℝ :=
  if Retained incidence D L Γ then coefficient incidence L R χ Γ else 0

theorem estimator_eq_all (incidence : E → Finset V) (edges : Finset E) (D L R : ℕ)
    (h : ℝ) (a : E → ℝ) (χ : Colors V L R) (J : E → ℝ) :
    estimator incidence edges D L R h a χ J =
      ∑ Γ ∈ edges.powerset,
        fullCoefficient incidence D L R χ Γ * DisorderOrthogonality.graphWeight incidence h a Γ J := by
  simp only [estimator,retained,Finset.sum_filter,fullCoefficient,ite_mul,zero_mul]

theorem partition_error_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (edges : Finset E) (D : ℕ)
    {L R : ℕ} (hL : 0 < L) (h : ℝ) (a : E → ℝ) :
    Integrable (fun χJ : Colors V L R × (E → ℝ) =>
      (estimator incidence edges D L R h a χJ.1 χJ.2 -
        FieldExpansion.normalizedPartition incidence edges h (fun e => a e * χJ.2 e)) ^ 2)
      ((colorLaw V L R).prod (iidLaw μ)) := by
  letI : Nonempty (Fin (2 * L)) := ⟨⟨0,by omega⟩⟩
  have heq (χJ : Colors V L R × (E → ℝ)) :
      estimator incidence edges D L R h a χJ.1 χJ.2 -
        FieldExpansion.normalizedPartition incidence edges h (fun e => a e * χJ.2 e) =
      ∑ Γ ∈ edges.powerset, (fullCoefficient incidence D L R χJ.1 Γ - 1) *
        DisorderOrthogonality.graphWeight incidence h a Γ χJ.2 := by
    rw [estimator_eq_all,FieldExpansion.normalizedPartition_eq_graph_sum]
    simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
    rfl
  simp_rw [heq]
  exact DisorderOrthogonality.integrable_independent_graph_square μ (colorLaw V L R)
    incidence h a edges.powerset (fun χ Γ => fullCoefficient incidence D L R χ Γ - 1)
    (fun Γ hΓ => measurable_of_countable _) (fun Γ hΓ => Integrable.of_finite)

/-- The independent coloring error and omitted-family error add exactly; no
triangle-inequality loss or independent color indicators are presumed. -/
theorem partition_mse_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (incidence : E → Finset V) (edges : Finset E) (D : ℕ)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hp : ∀ e ∈ edges, (incidence e).card = 2) (h : ℝ) (a : E → ℝ) :
    (∫ χJ : Colors V L R × (E → ℝ),
      (estimator incidence edges D L R h a χJ.1 χJ.2 -
        FieldExpansion.normalizedPartition incidence edges h (fun e => a e * χJ.2 e)) ^ 2
      ∂(colorLaw V L R).prod (iidLaw μ)) =
      (∫ χJ : Colors V L R × (E → ℝ),
        (estimator incidence edges D L R h a χJ.1 χJ.2 -
          retainedSum incidence edges D L h a χJ.2) ^ 2
        ∂(colorLaw V L R).prod (iidLaw μ)) +
      ∑ Γ ∈ edges.powerset.filter (fun Γ => ¬Retained incidence D L Γ),
        graphMass μ incidence h a Γ := by
  letI : Nonempty (Fin (2 * L)) := ⟨⟨0,by omega⟩⟩
  have hi := DisorderOrthogonality.independent_coefficient_error_second_moment
    μ hμ (colorLaw V L R) incidence h a edges.powerset
    (fullCoefficient incidence D L R) (fun _ _ => 1)
    (fun Γ hΓ => measurable_of_countable _) (fun Γ hΓ => Integrable.of_finite)
  have heq (χJ : Colors V L R × (E → ℝ)) :
      estimator incidence edges D L R h a χJ.1 χJ.2 -
        FieldExpansion.normalizedPartition incidence edges h (fun e => a e * χJ.2 e) =
      (∑ Γ ∈ edges.powerset, fullCoefficient incidence D L R χJ.1 Γ *
        DisorderOrthogonality.graphWeight incidence h a Γ χJ.2) -
      (∑ Γ ∈ edges.powerset, (1 : ℝ) * DisorderOrthogonality.graphWeight incidence h a Γ χJ.2) := by
    rw [estimator_eq_all,FieldExpansion.normalizedPartition_eq_graph_sum]
    simp only [one_mul]
    rfl
  simp_rw [heq]
  rw [hi,coloring_mse_eq μ hμ incidence edges D hL hR hp h a]
  simp only [retained,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hk : Retained incidence D L Γ
  · simp only [fullCoefficient,hk,if_true,not_true_eq_false,if_false,add_zero]
    rw [coefficient_variance incidence hL hR Γ
      (outside_card_of_mem_retained incidence edges D L hp Γ (Finset.mem_filter.mpr ⟨hΓ,hk⟩))]
    simp only [graphMass,mul_assoc]
  · simp [fullCoefficient,hk,graphMass]

/-- Total MSE is the actual truncation mass plus the uniform palette factor. -/
theorem partition_mse_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (incidence : E → Finset V) (edges : Finset E) (D : ℕ)
    {L R : ℕ} (hL : 0 < L) (hR : 0 < R)
    (hp : ∀ e ∈ edges, (incidence e).card = 2) (h : ℝ) (a : E → ℝ) :
    (∫ χJ : Colors V L R × (E → ℝ),
      (estimator incidence edges D L R h a χJ.1 χJ.2 -
        FieldExpansion.normalizedPartition incidence edges h (fun e => a e * χJ.2 e)) ^ 2
      ∂(colorLaw V L R).prod (iidLaw μ)) ≤
      (Real.exp (2 * (L : ℝ)) / (R : ℝ)) *
        ∑ Γ ∈ edges.powerset, graphMass μ incidence h a Γ +
      ∑ Γ ∈ edges.powerset.filter (fun Γ => ¬Retained incidence D L Γ),
        graphMass μ incidence h a Γ := by
  rw [partition_mse_eq μ hμ incidence edges D hL hR hp h a]
  exact add_le_add (coloring_mse_le μ hμ incidence edges D hL hR hp h a) le_rfl

end Manuscript.SKColorEstimator
