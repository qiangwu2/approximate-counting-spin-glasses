import Manuscript.RestrictedMachine

/-! A finite-procedure extension of the restricted exact-real RAM.
A procedure table is fixed independently of raw input. Calls save only the
listed registers; arguments, results, and persistent data remain in the same
registers and RAM arrays as the base machine. Every saved register is charged
for its read/push and pop/write. There is no function-value instruction,
semantic callback, cost annotation, or data-dependent procedure definition. -/
noncomputable section
namespace Manuscript.RestrictedRecursiveMachine
open RestrictedMachine

inductive Program (q : ℕ) where
  | base (program : RestrictedMachine.Program)
  | seq (first second : Program q)
  | branch (flag : ℕ) (yes no : Program q)
  | repeat (boundRegister : ℕ) (body : Program q)
  | call (procedure : Fin q)

structure Procedure (q : ℕ) where
  body : Program q
  saveReal : List ℕ
  saveNat : List ℕ

def restoreReal (original : State) : List ℕ → State → State
  | [], final => final
  | r::rs, final => restoreReal original rs (writeRealReg final r (original.realReg r))

def restoreNat (original : State) : List ℕ → State → State
  | [], final => final
  | r::rs, final => restoreNat original rs (writeNatReg final r (original.natReg r))

def restore {q : ℕ} (procedure : Procedure q) (original final : State) : State :=
  restoreNat original procedure.saveNat (restoreReal original procedure.saveReal final)

@[simp] theorem restoreReal_realReg (original final : State) (rs : List ℕ) (r : ℕ) :
    (restoreReal original rs final).realReg r =
      if r ∈ rs then original.realReg r else final.realReg r := by
  induction rs generalizing final with
  | nil => simp [restoreReal]
  | cons a rs ih =>
      simp only [restoreReal, ih, List.mem_cons, writeRealReg_realReg]
      by_cases hr : r = a <;> by_cases hm : r ∈ rs <;> simp [hr,hm]

@[simp] theorem restoreReal_natReg (original final : State) (rs : List ℕ) :
    (restoreReal original rs final).natReg = final.natReg := by
  induction rs generalizing final with
  | nil => rfl
  | cons a rs ih => simp [restoreReal, ih]

@[simp] theorem restoreReal_realMem (original final : State) (rs : List ℕ) :
    (restoreReal original rs final).realMem = final.realMem := by
  induction rs generalizing final with
  | nil => rfl
  | cons a rs ih => simp [restoreReal, ih]

@[simp] theorem restoreReal_natMem (original final : State) (rs : List ℕ) :
    (restoreReal original rs final).natMem = final.natMem := by
  induction rs generalizing final with
  | nil => rfl
  | cons a rs ih => simp [restoreReal, ih]

@[simp] theorem restoreNat_natReg (original final : State) (rs : List ℕ) (r : ℕ) :
    (restoreNat original rs final).natReg r =
      if r ∈ rs then original.natReg r else final.natReg r := by
  induction rs generalizing final with
  | nil => simp [restoreNat]
  | cons a rs ih =>
      simp only [restoreNat, ih, List.mem_cons, writeNatReg_natReg]
      by_cases hr : r = a <;> by_cases hm : r ∈ rs <;> simp [hr,hm]

@[simp] theorem restoreNat_realReg (original final : State) (rs : List ℕ) :
    (restoreNat original rs final).realReg = final.realReg := by
  induction rs generalizing final with
  | nil => rfl
  | cons a rs ih => simp [restoreNat, ih]

@[simp] theorem restoreNat_realMem (original final : State) (rs : List ℕ) :
    (restoreNat original rs final).realMem = final.realMem := by
  induction rs generalizing final with
  | nil => rfl
  | cons a rs ih => simp [restoreNat, ih]

@[simp] theorem restoreNat_natMem (original final : State) (rs : List ℕ) :
    (restoreNat original rs final).natMem = final.natMem := by
  induction rs generalizing final with
  | nil => rfl
  | cons a rs ih => simp [restoreNat, ih]

@[simp] theorem restore_realReg {q : ℕ} (p : Procedure q) (s t : State) (r : ℕ) :
    (restore p s t).realReg r = if r ∈ p.saveReal then s.realReg r else t.realReg r := by
  simp [restore]
@[simp] theorem restore_natReg {q : ℕ} (p : Procedure q) (s t : State) (r : ℕ) :
    (restore p s t).natReg r = if r ∈ p.saveNat then s.natReg r else t.natReg r := by
  simp [restore]
@[simp] theorem restore_realMem {q : ℕ} (p : Procedure q) (s t : State) :
    (restore p s t).realMem = t.realMem := by simp [restore]
@[simp] theorem restore_natMem {q : ℕ} (p : Procedure q) (s t : State) :
    (restore p s t).natMem = t.natMem := by simp [restore]

/-- Save and restore cost four for each listed register; return-address
push/pop and call/return dispatch cost five. -/
def callCost {q : ℕ} (p : Procedure q) : ℕ :=
  4*(p.saveReal.length+p.saveNat.length)+5

mutual
  inductive Exec {q : ℕ} (table : Fin q → Procedure q) (params : Parameters) (input : Inputs) :
      Program q → State → ℕ → State → Prop where
    | base {p : RestrictedMachine.Program} {s t : State} {c : ℕ}
        (run : RestrictedMachine.Exec params input p s c t) :
        Exec table params input (.base p) s c t
    | seq {p q : Program _} {s m t : State} {c d : ℕ}
        (first : Exec table params input p s c m) (second : Exec table params input q m d t) :
        Exec table params input (.seq p q) s (c+d) t
    | branchZero {flag : ℕ} {yes no : Program _} {s t : State} {c : ℕ}
        (zero : s.natReg flag = 0) (chosen : Exec table params input no s c t) :
        Exec table params input (.branch flag yes no) s (c+3) t
    | branchNonzero {flag : ℕ} {yes no : Program _} {s t : State} {c : ℕ}
        (nonzero : s.natReg flag ≠ 0) (chosen : Exec table params input yes s c t) :
        Exec table params input (.branch flag yes no) s (c+3) t
    | repeat {bound : ℕ} {body : Program _} {s t : State} {c : ℕ}
        (iterations : Repeats table params input body (s.natReg bound) s c t) :
        Exec table params input (.repeat bound body) s (c+2) t
    | call (id : Fin _) {s m : State} {c : ℕ}
        (bodyRun : Exec table params input (table id).body s c m) :
        Exec table params input (.call id) s (c+callCost (table id)) (restore (table id) s m)
  inductive Repeats {q : ℕ} (table : Fin q → Procedure q) (params : Parameters) (input : Inputs) :
      Program q → ℕ → State → ℕ → State → Prop where
    | zero (body : Program q) (s : State) : Repeats table params input body 0 s 3 s
    | succ {body : Program q} {n : ℕ} {s m t : State} {c d : ℕ}
        (bodyRun : Exec table params input body s c m) (rest : Repeats table params input body n m d t) :
        Repeats table params input body (n+1) s (c+d+5) t
end

end Manuscript.RestrictedRecursiveMachine
