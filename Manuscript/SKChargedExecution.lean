import SpinGlass.SKFastEvaluator
import Manuscript.SKChargedMonomial

/-! The colorful dynamic-programming evaluator with zero-charge ghost edges.
The algebra capacity can be 2L while only coefficients of charged degree≤L
are selected. Every primitive reads the saved colorful path table. -/
noncomputable section
namespace Manuscript.SKChargedExecution
open SpinGlass
open scoped BigOperators
open SKRing
open SKFastEvaluator (pairWeight pathDegrees insertMonomial pathCoefficient
  returnCoefficient cycleCoefficient insertMonomial_vanishesBelow vanishesBelow_add)
variable {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

/-- The primitive polynomial in equation (46), constructed from the actual recurrence outputs. -/
def primitives {b L : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) : Element b L :=
  (∑ S : Finset (Fin L), if 3 ≤ S.card then
    insertMonomial S.card S (fun _ => 0) (cycleCoefficient outside χ f S) else 0) +
  (∑ a : Fin b, ∑ c : Fin b, if a < c then
    ∑ S : Finset (Fin L), if 1 ≤ S.card then
      insertMonomial (S.card - 1 + endpointCharge a + endpointCharge c) S (pathDegrees a c)
        (pathCoefficient branch outside χ f a c S) else 0 else 0) +
  (∑ a : Fin b, ∑ S : Finset (Fin L), if 2 ≤ S.card then
    insertMonomial (S.card - 1 + endpointCharge a + endpointCharge a) S (pathDegrees a a)
      (returnCoefficient branch outside χ f a S) else 0)

/-- The direct edge factor includes no outside color. -/
def direct {b L : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ) (a c : Fin b) : Element b L :=
  insertMonomial (if endpointCharge a = 0 ∨ endpointCharge c = 0 then 0 else 1) ∅ (pathDegrees a c) (pairWeight f (branch a) (branch c))

/-- Each unordered branch pair is scheduled once, by the order of its labels. -/
def directPairs (b : ℕ) : Finset (Fin b × Fin b) := Finset.univ.filter (fun p => p.1 < p.2)

/-- Point-update charged coefficient evaluator before extraction. -/
def evaluate {b L : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) : SKCoefficient.Coefficients b L :=
  SKDenseExecution.evaluator (primitives endpointCharge branch outside χ f).coeff
    ((directPairs b).toList.map (fun p => (direct (L := L) endpointCharge branch f p.1 p.2).coeff))

/-- The actual recurrence-built primitive polynomial is nilpotent for every signed input. -/
theorem primitives_vanishesBelow {b L : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) :
    SKCoefficient.VanishesBelow 1 (primitives endpointCharge branch outside χ f).coeff := by
  unfold primitives
  apply vanishesBelow_add
  · apply vanishesBelow_add
    · apply SKPrimitiveExpansion.sum_vanishesBelow
      intro S hS
      split
      · apply insertMonomial_vanishesBelow
        exact Finset.card_pos.mp (by omega)
      · intro z hz; rfl
    · apply SKPrimitiveExpansion.sum_vanishesBelow
      intro a ha
      apply SKPrimitiveExpansion.sum_vanishesBelow
      intro c hc
      split
      · apply SKPrimitiveExpansion.sum_vanishesBelow
        intro S hS
        split
        · apply insertMonomial_vanishesBelow
          exact Finset.card_pos.mp (by omega)
        · intro z hz; rfl
      · intro z hz; rfl
  · apply SKPrimitiveExpansion.sum_vanishesBelow
    intro a ha
    apply SKPrimitiveExpansion.sum_vanishesBelow
    intro S hS
    split
    · apply insertMonomial_vanishesBelow
      exact Finset.card_pos.mp (by omega)
    · intro z hz; rfl

/-- The scheduled implementation computes exactly the assembled polynomial in equation (49) for its computed primitives. -/
theorem evaluate_eq_polynomial {b L : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin L) (f : Finset V → ℝ) :
    evaluate endpointCharge branch outside χ f =
      (IsNilpotent.exp (primitives endpointCharge branch outside χ f) *
        ∏ p ∈ directPairs b, (1 + direct (L := L) endpointCharge branch f p.1 p.2)).coeff := by
  rw [evaluate, SKDenseExecution.evaluator_correct, SKExponential.algebraEvaluator,
    SKExponential.directLoop_correct,
    SKPrimitiveExpansion.loop_eq_exp _ (primitives_vanishesBelow endpointCharge branch outside χ f)]
  have hd := SKPrimitiveExpansion.directProduct_eq
    ((directPairs b).toList.map (fun p => direct (L := L) endpointCharge branch f p.1 p.2))
  simp only [List.map_map, Function.comp_def, Finset.prod_map_toList] at hd
  rw [hd, coeff_mul]


/-- Sum exactly the requested charged edge degrees, outside sizes and accepted
distinguished-vertex states. -/
def byOutsideSize {b K : ℕ} (endpointCharge : Fin b → ℕ)
    (branch : Fin b → V) (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (L m : ℕ) (accepted : Finset (Fin b → CappedDegree)) : ℝ :=
  ∑ k : Fin (K+1), ∑ S : Finset (Fin K), ∑ d ∈ accepted,
    if k.val ≤ L ∧ S.card = m then
      evaluate endpointCharge branch outside χ f (SKChargedMonomial.target k S d) else 0

end Manuscript.SKChargedExecution
