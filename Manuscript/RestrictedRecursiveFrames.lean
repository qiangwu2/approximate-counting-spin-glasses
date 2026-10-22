import Manuscript.RestrictedRecursiveMachine
import Manuscript.RestrictedFrames

noncomputable section
namespace Manuscript.RestrictedRecursiveMachine
open RestrictedMachine

def Program.All {q : ℕ} (P : Instruction → Prop) : Program q → Prop
  | .base p => p.All P
  | .seq p r | .branch _ p r => p.All P ∧ r.All P
  | .repeat _ p => p.All P
  | .call _ => True

theorem Exec.observation_eq {q : ℕ} {α : Type*} (observe : State → α)
    {table : Fin q → Procedure q} {p : Parameters} {i : Inputs}
    {prog : Program q} {s t : State} {c : ℕ}
    (h : Exec table p i prog s c t)
    (safe : prog.All (fun op => ∀ u, observe (step p i op u)=observe u))
    (safeTable : ∀ id, (table id).body.All (fun op => ∀ u, observe (step p i op u)=observe u))
    (restoreSafe : ∀ id original final, observe final=observe original →
      observe (restore (table id) original final)=observe original) : observe t=observe s := by
  induction h using Exec.rec
      (motive_2 := fun body _ s _ t _ =>
        body.All (fun op => ∀ u, observe (step p i op u)=observe u) → observe t=observe s) with
  | base run => exact run.observation_eq observe safe
  | seq first second ih₁ ih₂ => exact (ih₂ safe.2).trans (ih₁ safe.1)
  | branchZero zero chosen ih => exact ih safe.2
  | branchNonzero nonzero chosen ih => exact ih safe.1
  | «repeat» iterations ih => exact ih safe
  | call id run ih => exact restoreSafe id _ _ (ih (safeTable id))
  | zero => rfl
  | succ first rest ih₁ ih₂ => exact (ih₂ (by assumption)).trans (ih₁ (by assumption))

theorem Program.All.mono {q : ℕ} {P Q : Instruction → Prop} {p : Program q}
    (h : p.All P) (imp : ∀ op, P op → Q op) : p.All Q := by
  induction p with
  | base p => exact RestrictedMachine.Program.All.mono h imp
  | seq p q hp hq | branch flag p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | «repeat» bound p hp => exact hp h
  | call => trivial

theorem Exec.realReg_frame {q : ℕ} {table : Fin q → Procedure q}
    {p : Parameters} {i : Inputs} {prog : Program q} {s t : State} {c r : ℕ}
    (h : Exec table p i prog s c t)
    (safe : prog.All (fun op => op.realDestination≠some r))
    (safeTable : ∀ id, (table id).body.All (fun op => op.realDestination≠some r)) :
    t.realReg r=s.realReg r := by
  apply h.observation_eq (fun u => u.realReg r)
    (safe.mono fun op ho u => step_realReg_frame p i op u r ho)
    (fun id => (safeTable id).mono fun op ho u => step_realReg_frame p i op u r ho)
  intro id original final heq
  simp [heq]

theorem Exec.natReg_frame {q : ℕ} {table : Fin q → Procedure q}
    {p : Parameters} {i : Inputs} {prog : Program q} {s t : State} {c r : ℕ}
    (h : Exec table p i prog s c t)
    (safe : prog.All (fun op => op.natDestination≠some r))
    (safeTable : ∀ id, (table id).body.All (fun op => op.natDestination≠some r)) :
    t.natReg r=s.natReg r := by
  apply h.observation_eq (fun u => u.natReg r)
    (safe.mono fun op ho u => step_natReg_frame p i op u r ho)
    (fun id => (safeTable id).mono fun op ho u => step_natReg_frame p i op u r ho)
  intro id original final heq
  simp [heq]

theorem Exec.realMem_frame {q : ℕ} {table : Fin q → Procedure q}
    {p : Parameters} {i : Inputs} {prog : Program q} {s t : State} {c : ℕ}
    (h : Exec table p i prog s c t)
    (safe : prog.All (fun op => op.writesRealMemory=false))
    (safeTable : ∀ id, (table id).body.All (fun op => op.writesRealMemory=false)) :
    t.realMem=s.realMem := by
  apply h.observation_eq State.realMem
    (safe.mono fun op ho u => step_realMem_frame p i op u ho)
    (fun id => (safeTable id).mono fun op ho u => step_realMem_frame p i op u ho)
  intro id original final heq
  simpa using heq

end Manuscript.RestrictedRecursiveMachine
