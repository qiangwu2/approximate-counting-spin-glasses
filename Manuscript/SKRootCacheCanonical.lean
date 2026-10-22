import Manuscript.SKRootCacheInitialization
import SpinGlass.SKCountedExecutionCache

noncomputable section
namespace Manuscript.SKRootCache
open RestrictedMachine SKMemoUpdate

def rootNumber {N B : ℕ} : Fin B ⊕ Fin N → ℕ
  | .inl a => a.val
  | .inr r => B+r.val

theorem start_root {V : Type*} [DecidableEq V] {N B : ℕ}
    (branch : Fin B→V) (outside : Fin N→V) (f : Finset V→ℝ)
    (root : Fin B⊕Fin N) :
    start (fun a j => SpinGlass.SKFastEvaluator.pairWeight f (branch a) (outside j))
      (rootNumber root)=SpinGlass.SKCountedExecution.rootStart branch outside f root := by
  funext j
  cases root with
  | inl a => simp [rootNumber,start,a.isLt,SpinGlass.SKCountedExecution.rootStart]
  | inr r =>
    simp [rootNumber,start,show ¬B+r.val<B by omega,SpinGlass.SKCountedExecution.rootStart,
      SpinGlass.ColorCycleChain.rootStart,Fin.ext_iff]

theorem invariant_canonical {V : Type*} [DecidableEq V] (d : Layout)
    (branch : Fin d.B→V) (outside : Fin d.N→V) (f : Finset V→ℝ)
    (χ : Fin d.N→Fin d.K) (t : State)
    (hi : Invariant d χ
      (fun i j => SpinGlass.SKFastEvaluator.pairWeight f (outside i) (outside j))
      (fun a j => SpinGlass.SKFastEvaluator.pairWeight f (branch a) (outside j))
      (d.B+d.N) t) (root : Fin d.B⊕Fin d.N) (S : Finset (Fin d.K)) (j : Fin d.N) :
    t.realMem (rowAddress d.N (d.cache+rootNumber root*d.T) S j.val)=
      (SpinGlass.SKCountedExecution.rootCache branch outside χ f).value root S j := by
  have hr : rootNumber root<d.B+d.N := by
    cases root with
    | inl a => simp only [rootNumber]; have := a.isLt; omega
    | inr r => simp only [rootNumber]; have := r.isLt; omega
  rw [hi.computed _ hr,start_root,SpinGlass.SKCountedExecution.rootCache_value]
  have hm := SpinGlass.ColorMemoExecution.memo_correct χ
    (SpinGlass.SKCountedExecution.rootStart branch outside f root)
    (fun i j => SpinGlass.SKFastEvaluator.pairWeight f (outside i) (outside j)) S j
  simpa only [Fintype.card_fin] using hm.symm

end Manuscript.SKRootCache
