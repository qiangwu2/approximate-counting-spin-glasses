import Manuscript.SKChargedPrimitiveAssembly
import Manuscript.SKChargedGraphSum

/-! The implemented charged primitive recurrence computes the actual graph sum. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKChargedEvaluatorCorrect
open SpinGlass SKRing SKActualEvaluator SKDirectCatalog SKCatalogSelection
open SKAugmentFinset SKChargedMonomial SKChargedPrimitiveCounts SKChargedPrimitiveValues
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

theorem direct_product {K : ℕ} (A : Finset (Option V)) (χ : Outside A → Fin K) (hK : 0 < K)
    (f : Finset (Option V) → ℝ) :
    (∏ p ∈ SKChargedExecution.directPairs A.card,
      (1 + SKChargedExecution.direct (L := K) (endpointCharge A) (branch A) f p.1 p.2)) =
    ∏ E ∈ directCatalog A, (1 + value charge id A (branch A) (totalColor A χ hK) f E) := by
  rw [directCatalog,Finset.prod_image (directGraph_injOn A)]
  apply Finset.prod_congr rfl
  intro p hp
  rw [directGraph,direct_value A χ hK f p.1 p.2 (ne_of_lt (Finset.mem_filter.mp hp).2)]

/-- Exact graph-sum semantics of the charged evaluator, for any real edge weights. -/
theorem evaluate_eq_graph_sum {K : ℕ} (A : Finset (Option V)) (hA : none ∈ A)
    (χ : Outside A → Fin K) (hK : 0 < K) (f : Finset (Option V) → ℝ) :
    SKChargedExecution.evaluate (endpointCharge A) (branch A) Subtype.val χ f =
    (∑ Γ ∈ (Finset.univ : Finset (Finset (Finset (Option V)))).filter
      (SKColorfulGraphSum.GraphCondition A),
      value charge id A (branch A) (totalColor A χ hK) f Γ).coeff := by
  rw [SKChargedExecution.evaluate_eq_polynomial,
    SKChargedPrimitiveAssembly.primitives_eq_catalog A hA χ hK f,
    SKChargedGraphSum.primitive_exponential charge A χ hK f,
    direct_product A χ hK f,
    ← Finset.prod_union (SKColorfulGraphSum.catalog_direct_disjoint A χ)]
  change (∏ E ∈ SKColorfulGraphSum.fullCatalog A χ,
    (1 + value charge id A (branch A) (totalColor A χ hK) f E)).coeff = _
  rw [SKChargedGraphSum.product_eq_graph_sum charge A χ hK f]

end Manuscript.SKChargedEvaluatorCorrect
