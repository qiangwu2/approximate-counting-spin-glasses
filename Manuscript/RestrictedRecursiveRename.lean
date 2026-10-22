import Manuscript.RestrictedRecursiveMachine

noncomputable section
namespace Manuscript.RestrictedRecursiveMachine
open RestrictedMachine

/-- Change finite procedure addresses in syntax only. No machine computation
is replaced, and the source body is not evaluated during renaming. -/
def Program.rename {q r : ℕ} (f : Fin q→Fin r) : Program q→Program r
  | .base p => .base p
  | .seq p s => .seq (p.rename f) (s.rename f)
  | .branch flag p s => .branch flag (p.rename f) (s.rename f)
  | .repeat bound p => .repeat bound (p.rename f)
  | .call id => .call (f id)

def Procedure.rename {q r : ℕ} (f : Fin q→Fin r) (p : Procedure q) : Procedure r :=
  ⟨p.body.rename f,p.saveReal,p.saveNat⟩

@[simp] theorem restore_rename {q r : ℕ} (f : Fin q→Fin r) (p : Procedure q) (s t : State) :
    restore (p.rename f) s t=restore p s t := rfl
@[simp] theorem callCost_rename {q r : ℕ} (f : Fin q→Fin r) (p : Procedure q) :
    callCost (p.rename f)=callCost p := rfl

/-- Transport an execution into a larger fixed procedure table. The premise
is equality of finite syntax and save lists, not an assumed output behavior. -/
theorem Exec.rename {q r : ℕ} {table : Fin q→Procedure q}
    {params : Parameters} {input : Inputs} {prog : Program q} {s t : State} {c : ℕ}
    (h : Exec table params input prog s c t) (f : Fin q→Fin r)
    (target : Fin r→Procedure r)
    (ht : ∀ id, target (f id)=(table id).rename f) :
    Exec target params input (prog.rename f) s c t := by
  induction h using Exec.rec
      (motive_2 := fun body n s c t _ => Repeats target params input (body.rename f) n s c t) with
  | base run => exact Exec.base run
  | seq first second ih₁ ih₂ => exact Exec.seq ih₁ ih₂
  | branchZero zero chosen ih => exact Exec.branchZero zero ih
  | branchNonzero nonzero chosen ih => exact Exec.branchNonzero nonzero ih
  | «repeat» iterations ih => exact Exec.repeat ih
  | call id bodyRun ih =>
    have heq : (target (f id)).body=(table id).body.rename f := congrArg Procedure.body (ht id)
    rw [←heq] at ih
    simpa only [Program.rename,ht,restore_rename,callCost_rename] using Exec.call (f id) ih
  | zero body s => exact Repeats.zero (body.rename f) s
  | succ first rest ih₁ ih₂ => exact Repeats.succ ih₁ ih₂

end Manuscript.RestrictedRecursiveMachine
