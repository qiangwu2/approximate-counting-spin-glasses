import SpinGlass.SKCatalogMembership
import Manuscript.SKBranchReindex

noncomputable section
namespace Manuscript.SKPathSymmetry
open SpinGlass SKTraversal SKCatalogMembership
open scoped BigOperators

theorem pathClosure {V W C : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] [DecidableEq C] (outside : W → V) (hinj : Function.Injective outside)
    (χ : W → C) (S : Finset C) (f : Finset V → ℝ) {a c : V}
    (hac : a≠c) (ha : a∉Set.range outside) (hc : c∉Set.range outside) :
    SKPrimitiveTables.pathClosure χ (fun i => f {a,outside i})
      (fun i j => f {outside i,outside j}) (fun j => f {outside j,c}) S=
    SKPrimitiveTables.pathClosure χ (fun i => f {c,outside i})
      (fun i j => f {outside i,outside j}) (fun j => f {outside j,a}) S := by
  rw [pathClosure_eq_graph_sum outside hinj χ S f hac ha hc,
    pathClosure_eq_graph_sum outside hinj χ S f hac.symm hc ha]
  have heq : (liftedChains outside χ S).image (betweenEdges a c)=
      (liftedChains outside χ S).image (betweenEdges c a) := by
    ext Γ
    constructor
    · rintro h
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨l.reverse,
        liftedChains_closed outside hinj χ S l hl l.reverse (List.reverse_perm l),
        betweenEdges_reverse_swap a c l⟩
    · rintro h
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨l.reverse,
        liftedChains_closed outside hinj χ S l hl l.reverse (List.reverse_perm l),
        betweenEdges_reverse_swap c a l⟩
  rw [heq]

theorem pathCoefficient {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {b K : ℕ} (branch : Fin b → V) (outside : W → V)
    (hb : Function.Injective branch) (ho : Function.Injective outside)
    (hsep : ∀ a, branch a∉Set.range outside) (χ : W → Fin K)
    (f : Finset V → ℝ) (a c : Fin b) (hac : a≠c) (S : Finset (Fin K)) :
    SKFastEvaluator.pathCoefficient branch outside χ f a c S=
      SKFastEvaluator.pathCoefficient branch outside χ f c a S := by
  rw [SKFastEvaluator.pathCoefficient_eq,SKFastEvaluator.pathCoefficient_eq]
  exact pathClosure outside ho χ S f (fun h => hac (hb h)) (hsep a) (hsep c)

theorem pathDegrees {b : ℕ} (a c : Fin b) :
    SKFastEvaluator.pathDegrees a c=SKFastEvaluator.pathDegrees c a := by
  funext i
  simp only [SKFastEvaluator.pathDegrees,Nat.add_comm]

end Manuscript.SKPathSymmetry
