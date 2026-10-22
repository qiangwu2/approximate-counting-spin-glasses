import Manuscript.SKChargedEvaluatorCorrect
import Manuscript.SKGhostColors

/-! The charged evaluator coefficient is exactly the original weak-field graph sum. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKGhostCoefficient
open SpinGlass SKRing SKActualEvaluator SKChargedMonomial
open SKAugmentFinset SKGhostAdmissible SKChargedPrimitiveCounts
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def evaluate {K : ℕ} (A : Finset V) (χ : V → Fin K) (h : ℝ) (w : Finset V → ℝ) :
    SKCoefficient.Coefficients (distinguished A).card K :=
  SKChargedExecution.evaluate (endpointCharge (distinguished A)) (branch (distinguished A))
    Subtype.val (outsideColor A χ) (edgeWeight h w)

/-- Coefficient extraction accepts precisely the even ghost state and original
branch degrees at least four. -/
theorem coefficient_augmented {K : ℕ} (A : Finset V) (χ : V → Fin K) (hK : 0 < K)
    (h : ℝ) (w : Finset V → ℝ) (k : Fin (K+1)) (S : Finset (Fin K)) :
    (∑ d ∈ accepted A, evaluate A χ h w (target k S d)) =
      ∑ Δ ∈ (Finset.univ : Finset (Finset (Finset (Option V)))).filter (Admissible A),
        if edgeCount charge Δ = k.val ∧
          colors id (distinguished A) (totalColor (distinguished A) (outsideColor A χ) hK) Δ = S ∧
          Colorful id (distinguished A) (totalColor (distinguished A) (outsideColor A χ) hK) Δ
        then weight (edgeWeight h w) Δ else 0 := by
  unfold evaluate
  rw [SKChargedEvaluatorCorrect.evaluate_eq_graph_sum (distinguished A)
    (none_mem_distinguished A) (outsideColor A χ) hK (edgeWeight h w)]
  simp only [coeff_sum,Finset.sum_apply]
  rw [Finset.sum_comm]
  simp_rw [value_coefficient_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Δ hΔ
  by_cases hcond : SKColorfulGraphSum.GraphCondition (distinguished A) Δ
  · by_cases hd : degrees id (branch (distinguished A)) Δ ∈ accepted A
    · simp [Admissible,hcond,hd]
    · simp [Admissible,hcond,hd]
  · simp [Admissible,hcond]

/-- The coefficient identity of Proposition 4.4, now on actual original graphs.
The field factor, original-edge count, color set and branching set are all exact. -/
theorem coefficient_original {K : ℕ} (A : Finset V) (χ : V → Fin K) (hK : 0 < K)
    (h : ℝ) (w : Finset V → ℝ) (k : Fin (K+1)) (S : Finset (Fin K)) :
    (∑ d ∈ accepted A, evaluate A χ h w (target k S d)) =
      ∑ Γ ∈ SKBranching.branchFamily A,
        if Γ.card = k.val ∧ (SKGraph.outside id Γ).image χ = S ∧
          Set.InjOn χ (SKGraph.outside id Γ)
        then FieldExpansion.graphWeight id h w Γ else 0 := by
  rw [coefficient_augmented A χ hK h w k S,admissible_family,
    Finset.sum_image (fun _ _ _ _ heq => augment_injective heq)]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  have hb := (Finset.mem_filter.mp hΓ).2
  rw [edgeCount_augment,colors_augment_branch A Γ hb χ hK,
    colorful_augment_branch A Γ hb χ hK]
  congr 1
  exact weight_augment Γ h w

end Manuscript.SKGhostCoefficient
