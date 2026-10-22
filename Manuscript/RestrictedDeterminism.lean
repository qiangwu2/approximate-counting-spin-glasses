import Manuscript.RestrictedRecursiveMachine

noncomputable section
namespace Manuscript.RestrictedMachine

/-- Fixed raw input and program determine both the result and its charged
trace length. Execution theorems cannot select a cheaper alternative run. -/
theorem Exec.deterministic {params : Parameters} {input : Inputs} {p : Program}
    {s t : State} {c : ℕ} (h : Exec params input p s c t) :
    ∀ {d u},Exec params input p s d u → c=d ∧ t=u := by
  induction h using Exec.rec
      (motive_2:=fun body n s c t _=>∀{d u},Repeats params input body n s d u → c=d ∧ t=u) with
  | skip s => intro d u h;cases h;exact ⟨rfl,rfl⟩
  | atom i s => intro d u h;cases h;exact ⟨rfl,rfl⟩
  | seq h1 h2 ih1 ih2 =>
    intro d u h
    cases h with
    | seq h1' h2' =>
      obtain ⟨rfl,rfl⟩:=ih1 h1'
      obtain ⟨rfl,rfl⟩:=ih2 h2'
      exact ⟨rfl,rfl⟩
  | branchZero hz h ih =>
    intro d u h'
    cases h' with
    | branchZero _ h' => obtain ⟨rfl,rfl⟩:=ih h';exact ⟨rfl,rfl⟩
    | branchNonzero hn _ => exact False.elim (hn hz)
  | branchNonzero hn h ih =>
    intro d u h'
    cases h' with
    | branchZero hz _ => exact False.elim (hn hz)
    | branchNonzero _ h' => obtain ⟨rfl,rfl⟩:=ih h';exact ⟨rfl,rfl⟩
  | «repeat» h ih =>
    intro d u h'
    cases h' with
    | «repeat» h' => obtain ⟨rfl,rfl⟩:=ih h';exact ⟨rfl,rfl⟩
  | whileZero s hz =>
    intro d u h'
    cases h' with
    | whileZero _ _ => exact ⟨rfl,rfl⟩
    | whileNonzero hn _ _ => exact False.elim (hn hz)
  | whileNonzero hn h1 h2 ih1 ih2 =>
    intro d u h'
    cases h' with
    | whileZero _ hz => exact False.elim (hn hz)
    | whileNonzero _ h1' h2' =>
      obtain ⟨rfl,rfl⟩:=ih1 h1'
      obtain ⟨rfl,rfl⟩:=ih2 h2'
      exact ⟨rfl,rfl⟩
  | zero body s => rename_i d u h;cases h;exact ⟨rfl,rfl⟩
  | succ h1 h2 ih1 ih2 =>
    rename_i d u h
    cases h with
    | succ h1' h2' =>
      obtain ⟨rfl,rfl⟩:=ih1 h1'
      obtain ⟨rfl,rfl⟩:=ih2 h2'
      exact ⟨rfl,rfl⟩

end Manuscript.RestrictedMachine

namespace Manuscript.RestrictedRecursiveMachine
open RestrictedMachine

theorem Exec.deterministic {q : ℕ} {table : Fin q→Procedure q}
    {params : Parameters} {input : Inputs} {p : Program q}
    {s t : State} {c : ℕ} (h : Exec table params input p s c t) :
    ∀ {d u},Exec table params input p s d u → c=d ∧ t=u := by
  induction h using Exec.rec
      (motive_2:=fun body n s c t _=>∀{d u},Repeats table params input body n s d u → c=d ∧ t=u) with
  | base h =>
    intro d u h'
    cases h' with
    | base h' => exact h.deterministic h'
  | seq h1 h2 ih1 ih2 =>
    intro d u h
    cases h with
    | seq h1' h2' =>
      obtain ⟨rfl,rfl⟩:=ih1 h1'
      obtain ⟨rfl,rfl⟩:=ih2 h2'
      exact ⟨rfl,rfl⟩
  | branchZero hz h ih =>
    intro d u h'
    cases h' with
    | branchZero _ h' => obtain ⟨rfl,rfl⟩:=ih h';exact ⟨rfl,rfl⟩
    | branchNonzero hn _ => exact False.elim (hn hz)
  | branchNonzero hn h ih =>
    intro d u h'
    cases h' with
    | branchZero hz _ => exact False.elim (hn hz)
    | branchNonzero _ h' => obtain ⟨rfl,rfl⟩:=ih h';exact ⟨rfl,rfl⟩
  | «repeat» h ih =>
    intro d u h'
    cases h' with
    | «repeat» h' => obtain ⟨rfl,rfl⟩:=ih h';exact ⟨rfl,rfl⟩
  | call id h ih =>
    intro d u h'
    cases h' with
    | call _ h' => obtain ⟨rfl,rfl⟩:=ih h';exact ⟨rfl,rfl⟩
  | zero body s => rename_i d u h;cases h;exact ⟨rfl,rfl⟩
  | succ h1 h2 ih1 ih2 =>
    rename_i d u h
    cases h with
    | succ h1' h2' =>
      obtain ⟨rfl,rfl⟩:=ih1 h1'
      obtain ⟨rfl,rfl⟩:=ih2 h2'
      exact ⟨rfl,rfl⟩

end Manuscript.RestrictedRecursiveMachine
