import Manuscript.SKChargedGraphProduct
import SpinGlass.SKColorfulGraphSum

/-! The canonical optional block product with original-edge charging. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKChargedGraphSum
open SpinGlass SKRing SKActualEvaluator SKCatalogSelection SKDirectCatalog
open SKChargedMonomial SKChargedGraphProduct
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- The actual simple outside-degree-two graph sum, with an arbitrary declared
edge charge. This reuses the proved unique canonical block partition. -/
theorem product_eq_graph_sum (charge : Finset V → Bool) {L : ℕ}
    (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L) (f : Finset V → ℝ) :
    (∏ K ∈ SKColorfulGraphSum.fullCatalog A χ,
      (1 + value charge id A (branch A) (totalColor A χ hL) f K)) =
      ∑ Γ ∈ (Finset.univ : Finset (Finset (Finset V))).filter
        (SKColorfulGraphSum.GraphCondition A),
        value charge id A (branch A) (totalColor A χ hL) f Γ := by
  rw [optional_product_eq_graph_sum charge id A (branch A) (totalColor A χ hL) f
    (SKColorfulGraphSum.fullCatalog A χ)
    (fun K hK => ((SKColorfulGraphSum.fullCatalog_iff A χ hL K).mp hK).1.nonempty)
    (fun K hK => ((SKColorfulGraphSum.fullCatalog_iff A χ hL K).mp hK).1.connected)]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hc : Colorful id A (totalColor A χ hL) Γ
  · have he := SKColorfulGraphSum.builtFrom_iff_of_colorful A χ hL Γ hc
    change BuiltFrom id A (SKColorfulGraphSum.fullCatalog A χ) Γ ↔
      SKColorfulGraphSum.GraphCondition A Γ at he
    rw [he]
  · have hz : value charge id A (branch A) (totalColor A χ hL) f Γ = 0 := by simp [value,hc]
    simp only [hz,ite_self]

/-- Primitive colors make each optional primitive factor square-zero, so the
finite exponential is exactly the product, including ghost-edge weights. -/
theorem primitive_exponential (charge : Finset V → Bool) {L : ℕ}
    (A : Finset V) (χ : Outside A → Fin L) (hL : 0 < L) (f : Finset V → ℝ) :
    IsNilpotent.exp
      (∑ K ∈ catalog A χ, value charge id A (branch A) (totalColor A χ hL) f K) =
    ∏ K ∈ catalog A χ, (1 + value charge id A (branch A) (totalColor A χ hL) f K) := by
  exact SKPrimitiveExpansion.exp_sum_sq_zero (catalog A χ)
    (fun K => value charge id A (branch A) (totalColor A χ hL) f K)
    (fun K hK => value_vanishesBelow charge id A (branch A) (totalColor A χ hL) f K
      (SKCatalogMembership.catalog_properties A χ hK).outside_nonempty)
    (fun K hK => value_sq_zero charge id A (branch A) (totalColor A χ hL) f K
      (SKCatalogMembership.catalog_properties A χ hK).outside_nonempty)

end Manuscript.SKChargedGraphSum
