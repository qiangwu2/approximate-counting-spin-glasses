import Manuscript.SKPathSymmetry
import Manuscript.SKPairReindex

noncomputable section
namespace Manuscript.SKPrimitiveReindex
open SpinGlass SKBranchReindex SKChargedExecution
open SKFastEvaluator (pairWeight pathDegrees insertMonomial pathCoefficient returnCoefficient cycleCoefficient)
open scoped BigOperators
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def betweenTerm {b K : ℕ} (q : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ) (a c : Fin b) : SKRing.Element b K :=
  ∑ S : Finset (Fin K), if 1≤S.card then
    insertMonomial (S.card-1+q a+q c) S (pathDegrees a c)
      (pathCoefficient branch outside χ f a c S) else 0

theorem betweenTerm_symm {b K : ℕ} (q : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (hb : Function.Injective branch) (ho : Function.Injective outside)
    (hsep : ∀ a, branch a∉Set.range outside) (χ : W → Fin K)
    (f : Finset V → ℝ) (a c : Fin b) (hac : a≠c) :
    betweenTerm q branch outside χ f a c=betweenTerm q branch outside χ f c a := by
  apply Finset.sum_congr rfl
  intro S hS
  rw [SKPathSymmetry.pathCoefficient branch outside hb ho hsep χ f a c hac S,
    SKPathSymmetry.pathDegrees a c,Nat.add_right_comm (S.card-1) (q a) (q c)]

theorem betweenTerm_map {b c K : ℕ} (e : Fin b ≃ Fin c) (q : Fin c → ℕ)
    (branch : Fin c → V) (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (a d : Fin b) :
    ringEquiv e (betweenTerm q branch outside χ f (e a) (e d))=
      betweenTerm (q ∘ e) (branch ∘ e) outside χ f a d := by
  simp only [betweenTerm,map_sum,apply_ite,map_zero,insertMonomial_map,pathDegrees_map]
  rfl

theorem primitives_map {b c K : ℕ} (e : Fin b ≃ Fin c) (q : Fin c → ℕ)
    (branch : Fin c → V) (outside : W → V)
    (hb : Function.Injective branch) (ho : Function.Injective outside)
    (hsep : ∀ a, branch a∉Set.range outside) (χ : W → Fin K) (f : Finset V → ℝ) :
    ringEquiv e (primitives q branch outside χ f)=
      primitives (q ∘ e) (branch ∘ e) outside χ f := by
  unfold primitives
  rw [map_add,map_add]
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · simp only [map_sum,apply_ite,map_zero,insertMonomial_map]
      rfl
    · change ringEquiv e (∑ a : Fin c, ∑ d : Fin c,
        if a<d then betweenTerm q branch outside χ f a d else 0)=
        ∑ a : Fin b, ∑ d : Fin b,
        if a<d then betweenTerm (q ∘ e) (branch ∘ e) outside χ f a d else 0
      have hs := SKPairReindex.sum_reindex e (betweenTerm q branch outside χ f)
        (betweenTerm_symm q branch outside hb ho hsep χ f)
      rw [← hs]
      simp only [map_sum,apply_ite,map_zero,betweenTerm_map]
  · rw [map_sum]
    symm
    apply Fintype.sum_equiv e
    intro a
    simp only [map_sum,apply_ite,map_zero,insertMonomial_map,pathDegrees_map]
    rfl

theorem direct_symm {b K : ℕ} (q : Fin b → ℕ) (branch : Fin b → V)
    (f : Finset V → ℝ) (a c : Fin b) :
    direct (L:=K) q branch f a c=direct q branch f c a := by
  simp only [direct,or_comm,SKPathSymmetry.pathDegrees a c,pairWeight,Finset.pair_comm]

theorem direct_map {b c K : ℕ} (e : Fin b ≃ Fin c) (q : Fin c → ℕ)
    (branch : Fin c → V) (f : Finset V → ℝ) (a d : Fin b) :
    ringEquiv (K:=K) e (direct q branch f (e a) (e d))=
      direct (q ∘ e) (branch ∘ e) f a d := by
  simp only [direct,insertMonomial_map,pathDegrees_map]
  rfl

theorem directProduct_map {b c K : ℕ} (e : Fin b ≃ Fin c) (q : Fin c → ℕ)
    (branch : Fin c → V) (f : Finset V → ℝ) :
    ringEquiv (K:=K) e (∏ p ∈ directPairs c, (1+direct q branch f p.1 p.2))=
      ∏ p ∈ directPairs b, (1+direct (q ∘ e) (branch ∘ e) f p.1 p.2) := by
  have hs := SKPairReindex.prod_reindex e (fun a d => 1+direct (L:=K) q branch f a d)
    (fun a d _ => congrArg (1+·) (direct_symm q branch f a d))
  rw [← hs]
  simp only [map_prod,map_add,map_one,direct_map]

theorem evaluate_map {b c K : ℕ} (e : Fin b ≃ Fin c) (q : Fin c → ℕ)
    (branch : Fin c → V) (outside : W → V)
    (hb : Function.Injective branch) (ho : Function.Injective outside)
    (hsep : ∀ a, branch a∉Set.range outside) (χ : W → Fin K) (f : Finset V → ℝ) :
    pull e (evaluate q branch outside χ f)=
      evaluate (q ∘ e) (branch ∘ e) outside χ f := by
  rw [evaluate_eq_polynomial,evaluate_eq_polynomial]
  rw [← ringEquiv_coeff e]
  rw [map_mul,directProduct_map]
  have hn : IsNilpotent (primitives q branch outside χ f) :=
    ⟨K+1,SKRing.color_ideal_pow_zero _ (primitives_vanishesBelow q branch outside χ f)⟩
  rw [hn.map_exp (ringEquiv e),primitives_map e q branch outside hb ho hsep χ f]

end Manuscript.SKPrimitiveReindex
