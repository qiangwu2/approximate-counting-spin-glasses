import Manuscript.SKChargedExecution

noncomputable section
namespace Manuscript.SKOutsideReindex
open SpinGlass
open scoped BigOperators

theorem table {W U C : Type*} [Fintype W] [Fintype U]
    [DecidableEq W] [DecidableEq U] [DecidableEq C]
    (e : U ≃ W) (χ : W → C) (start : W → ℝ) (w : W → W → ℝ)
    (n : ℕ) (S : Finset C) (j : U) :
    ColorPath.table (χ ∘ e) (start ∘ e) (fun i j => w (e i) (e j)) n S j=
      ColorPath.table χ start w n S (e j) := by
  induction n generalizing S j with
  | zero => rfl
  | succ n ih =>
    simp only [ColorPath.table,Function.comp_apply]
    split_ifs
    · rfl
    · apply Fintype.sum_equiv e
      intro i
      rw [ih]
    · rfl

theorem pathTable {W U C : Type*} [Fintype W] [Fintype U]
    [DecidableEq W] [DecidableEq U] [DecidableEq C]
    (e : U ≃ W) (χ : W → C) (start : W → ℝ) (w : W → W → ℝ)
    (S : Finset C) (j : U) :
    ColorPath.pathTable (χ ∘ e) (start ∘ e) (fun i j => w (e i) (e j)) S j=
      ColorPath.pathTable χ start w S (e j) := table e χ start w _ _ _

theorem closure {W U C : Type*} [Fintype W] [Fintype U]
    [DecidableEq W] [DecidableEq U] [DecidableEq C]
    (e : U ≃ W) (χ : W → C) (start : W → ℝ) (w : W → W → ℝ)
    (finish : W → ℝ) (S : Finset C) :
    SKPrimitiveTables.pathClosure (χ ∘ e) (start ∘ e)
      (fun i j => w (e i) (e j)) (finish ∘ e) S=
      SKPrimitiveTables.pathClosure χ start w finish S := by
  unfold SKPrimitiveTables.pathClosure
  apply Fintype.sum_equiv e
  intro j
  rw [pathTable]
  rfl

theorem pathCoefficient {V W U : Type*} [Fintype W] [Fintype U]
    [DecidableEq V] [DecidableEq W] [DecidableEq U] {b K : ℕ}
    (e : U ≃ W) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin K) (f : Finset V → ℝ) (a c : Fin b) (S : Finset (Fin K)) :
    SKFastEvaluator.pathCoefficient branch (outside ∘ e) (χ ∘ e) f a c S=
      SKFastEvaluator.pathCoefficient branch outside χ f a c S := by
  rw [SKFastEvaluator.pathCoefficient_eq,SKFastEvaluator.pathCoefficient_eq]
  exact closure e χ (fun i => SKFastEvaluator.pairWeight f (branch a) (outside i))
    (fun i j => SKFastEvaluator.pairWeight f (outside i) (outside j))
    (fun j => SKFastEvaluator.pairWeight f (outside j) (branch c)) S

theorem returnCoefficient {V W U : Type*} [Fintype W] [Fintype U]
    [DecidableEq V] [DecidableEq W] [DecidableEq U] {b K : ℕ}
    (e : U ≃ W) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin K) (f : Finset V → ℝ) (a : Fin b) (S : Finset (Fin K)) :
    SKFastEvaluator.returnCoefficient branch (outside ∘ e) (χ ∘ e) f a S=
      SKFastEvaluator.returnCoefficient branch outside χ f a S := by
  simp only [SKFastEvaluator.returnCoefficient,pathCoefficient]

theorem cycleCoefficient {V W U : Type*} [Fintype W] [Fintype U]
    [DecidableEq V] [DecidableEq W] [DecidableEq U] {K : ℕ}
    (e : U ≃ W) (outside : W → V) (χ : W → Fin K)
    (f : Finset V → ℝ) (S : Finset (Fin K)) :
    SKFastEvaluator.cycleCoefficient (outside ∘ e) (χ ∘ e) f S=
      SKFastEvaluator.cycleCoefficient outside χ f S := by
  rw [SKFastEvaluator.cycleCoefficient_eq,SKFastEvaluator.cycleCoefficient_eq]
  unfold SKPrimitiveTables.outsideClosure
  split_ifs
  · congr 1
    apply Fintype.sum_equiv e
    intro r
    apply Fintype.sum_equiv e
    intro j
    unfold ColorCycleChain.rootTable
    have hstart : ColorCycleChain.rootStart r=ColorCycleChain.rootStart (e r) ∘ e := by
      funext i
      simp [ColorCycleChain.rootStart,e.injective.eq_iff]
    rw [hstart]
    exact congrArg (fun x => x*SKFastEvaluator.pairWeight f (outside (e j)) (outside (e r)))
      (pathTable e χ (ColorCycleChain.rootStart (e r))
        (fun i j => SKFastEvaluator.pairWeight f (outside i) (outside j)) S j)
  · rfl

theorem primitives {V W U : Type*} [Fintype W] [Fintype U]
    [DecidableEq V] [DecidableEq W] [DecidableEq U] {b K : ℕ}
    (e : U ≃ W) (q : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin K) (f : Finset V → ℝ) :
    SKChargedExecution.primitives q branch (outside ∘ e) (χ ∘ e) f=
      SKChargedExecution.primitives q branch outside χ f := by
  simp only [SKChargedExecution.primitives,pathCoefficient,returnCoefficient,cycleCoefficient]

theorem evaluate {V W U : Type*} [Fintype W] [Fintype U]
    [DecidableEq V] [DecidableEq W] [DecidableEq U] {b K : ℕ}
    (e : U ≃ W) (q : Fin b → ℕ) (branch : Fin b → V) (outside : W → V)
    (χ : W → Fin K) (f : Finset V → ℝ) :
    SKChargedExecution.evaluate q branch (outside ∘ e) (χ ∘ e) f=
      SKChargedExecution.evaluate q branch outside χ f := by
  simp only [SKChargedExecution.evaluate,primitives]

end Manuscript.SKOutsideReindex
