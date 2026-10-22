import Manuscript.SKPrimitiveReindex
import Manuscript.SKOutsideReindex
import Manuscript.SKChargedTrialExecution
import Manuscript.SKExtractionCell

noncomputable section
namespace Manuscript.SKTrialReindex
open SpinGlass SKBranchReindex SKChargedExecution
open SpinGlass.ArithmeticEvaluation
open scoped BigOperators

theorem accepted_map {b c : ℕ} (e : Fin b ≃ Fin c) (g : Fin b) (d : Fin c → CappedDegree) :
    d ∘ e ∈ SKExtractionCell.accepted g ↔ d∈SKExtractionCell.accepted (e g) := by
  simp only [SKExtractionCell.accepted,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h i
    obtain ⟨j,rfl⟩ := e.surjective i
    simpa only [e.injective.eq_iff,Function.comp_apply] using h j
  · intro h i
    simpa only [e.injective.eq_iff,Function.comp_apply] using h (e i)

theorem extract_map {b c K : ℕ} (e : Fin b ≃ Fin c) (g : Fin b)
    (f : SKCoefficient.Coefficients c K) (L : ℕ) :
    (SKChargedExtractionExecution.extract (pull e f) L (SKExtractionCell.accepted g)).value=
      (SKChargedExtractionExecution.extract f L (SKExtractionCell.accepted (e g))).value := by
  simp only [SKChargedExtractionExecution.extract,sumFinset_value,apply_ite,
    mul,literal,SKChargedExtractionExecution.colorReciprocal_value]
  symm
  apply Fintype.sum_equiv (coordinate e)
  intro x
  simp only [pull,Equiv.symm_apply_apply]
  change (if x.1.val≤L ∧ x.2.2∈SKExtractionCell.accepted (e g) then
    (ColoringProbability.probability K x.2.1.card)⁻¹*f x else 0)=
    (if x.1.val≤L ∧ x.2.2 ∘ e∈SKExtractionCell.accepted g then
    (ColoringProbability.probability K x.2.1.card)⁻¹*f x else 0)
  simp only [accepted_map]

theorem trial_eq_extract {V W : Type*} [Fintype W] [DecidableEq V] [DecidableEq W]
    {b K : ℕ} (q : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin K) (f : Finset V → ℝ) (L : ℕ)
    (accepted : Finset (Fin b → CappedDegree)) :
    (SKChargedTrialExecution.trial q branch outside χ f L accepted).value=
      (SKChargedExtractionExecution.extract (evaluate q branch outside χ f) L accepted).value := by
  simp only [SKChargedTrialExecution.trial,SKChargedPrimitiveExecution.primitives_value,
    SKChargedAlgebraExecution.evaluator_value,evaluate,SKChargedTrialExecution.directList,
    SKDenseExecution.evaluator_correct]

theorem trial_branch {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {b c K : ℕ}
    (e : Fin b ≃ Fin c) (g : Fin b) (q : Fin c → ℕ) (branch : Fin c → V)
    (outside : W → V) (hb : Function.Injective branch) (ho : Function.Injective outside)
    (hsep : ∀ a, branch a∉Set.range outside) (χ : W → Fin K) (f : Finset V → ℝ) (L : ℕ) :
    (SKChargedTrialExecution.trial (q ∘ e) (branch ∘ e) outside χ f L
      (SKExtractionCell.accepted g)).value=
    (SKChargedTrialExecution.trial q branch outside χ f L
      (SKExtractionCell.accepted (e g))).value := by
  rw [trial_eq_extract,trial_eq_extract,
    ← SKPrimitiveReindex.evaluate_map e q branch outside hb ho hsep χ f]
  exact extract_map e g _ L

theorem trial_outside {V W U : Type*} [Fintype W] [Fintype U]
    [DecidableEq V] [DecidableEq W] [DecidableEq U] {b K : ℕ}
    (e : U ≃ W) (q : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin K) (f : Finset V → ℝ) (L : ℕ)
    (accepted : Finset (Fin b → CappedDegree)) :
    (SKChargedTrialExecution.trial q branch (outside ∘ e) (χ ∘ e) f L accepted).value=
      (SKChargedTrialExecution.trial q branch outside χ f L accepted).value := by
  rw [trial_eq_extract,trial_eq_extract,SKOutsideReindex.evaluate]

end Manuscript.SKTrialReindex
