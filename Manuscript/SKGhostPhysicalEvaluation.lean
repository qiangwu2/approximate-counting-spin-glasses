import Manuscript.SKGhostAggregation
import Manuscript.UniformSKTransport

/-! The charged evaluator consumes exactly the physical SK interaction array. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKGhostCoefficient
open SpinGlass Manuscript.Model UniformSKTransport
attribute [local instance] Classical.propDecidable

/-- Total lookup extension of the physical input. Only pair edges are ever
queried by the recurrence; values on other finite subsets are zero. -/
def inputWeight (N : ℕ) (a : ℕ → ℝ) (beta : ℝ) (J : Edge N {2} → ℝ)
    (e : Finset (Fin N)) : ℝ :=
  if he : e ∈ physicalEdges N {2} then Real.tanh (Model.coefficient N {2} a beta J ⟨e,he⟩) else 0

@[simp] theorem inputWeight_physical (N : ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (J : Edge N {2} → ℝ) (e : Edge N {2}) :
    inputWeight N a beta J e.val = Real.tanh (Model.coefficient N {2} a beta J e) := by
  simp [inputWeight,e.property]

@[simp] theorem forget_support (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P)) :
    SupportEvaluation.support id (forget N P Γ) = SupportEvaluation.support Subtype.val Γ := by
  ext v
  simp [SupportEvaluation.support,forget]

@[simp] theorem forget_outside (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P)) :
    SKGraph.outside id (forget N P Γ) = SKGraph.outside Subtype.val Γ := by
  simp [SKGraph.outside]

theorem coefficient_forget (N L R : ℕ) (P : Finset ℕ)
    (χ : SKColorEstimator.Colors (Fin N) L R) (Γ : Finset (Edge N P)) :
    SKColorEstimator.coefficient id L R χ (forget N P Γ) =
      SKColorEstimator.coefficient Subtype.val L R χ Γ := by
  simp only [SKColorEstimator.coefficient,ColoringEstimator.graphCoefficient,
    forget_outside,forget_branch]

theorem weight_forget (N : ℕ) (a : ℕ → ℝ) (beta h : ℝ) (J : Edge N {2} → ℝ)
    (Γ : Finset (Edge N {2})) :
    FieldExpansion.graphWeight id h (inputWeight N a beta J) (forget N {2} Γ) =
      DisorderOrthogonality.graphWeight Subtype.val h
        (DisorderOrthogonality.physicalScale N {2} a beta) Γ J := by
  unfold FieldExpansion.graphWeight DisorderOrthogonality.graphWeight
  rw [forget_boundary,forget_product]
  simp only [inputWeight_physical,DisorderOrthogonality.coefficient_eq_physicalScale]
  rfl

/-- Complete evaluator correctness on exactly the physical typed input, including
all candidate sets, repetitions and inverse colorful probabilities. -/
theorem algorithm_eq_physical (N D L R : ℕ) (hL : 0 < L)
    (χ : SKColorEstimator.Colors (Fin N) L R) (a : ℕ → ℝ) (beta h : ℝ)
    (J : Edge N {2} → ℝ) :
    algorithm D L R χ h (inputWeight N a beta J) =
      SKColorEstimator.estimator Subtype.val Finset.univ D L R h
        (DisorderOrthogonality.physicalScale N {2} a beta) χ J := by
  rw [algorithm_eq_graph_estimator D L R hL,← forget_pairGraphs N,Finset.filter_image,
    Finset.sum_image (fun _ _ _ _ heq => forget_injective N {2} heq)]
  unfold SKColorEstimator.estimator SKColorEstimator.retained
  simp only [SKGraph.Retained,forget_branch,forget_card]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [coefficient_forget,weight_forget]

end Manuscript.SKGhostCoefficient
