import Manuscript.RestrictedMachine

noncomputable section
namespace Manuscript.RestrictedMachine

def Instruction.realDestination : Instruction → Option ℕ
  | .rconst d _ | .rcopy d _ | .radd d _ _ | .rmul d _ _ | .rdiv d _ _
  | .rexp d _ | .rlog d _ | .rtanh d _ | .natToReal d _ | .readParam d _
  | .readRealInput d _ | .loadReal d _ => some d
  | _ => none
def Instruction.natDestination : Instruction → Option ℕ
  | .nconst d _ | .ncopy d _ | .rle d _ _ | .nadd d _ _ | .nsub d _ _
  | .nmul d _ _ | .ndiv d _ _ | .nmod d _ _ | .nle d _ _ | .neq d _ _
  | .readNatInput d _ | .loadNat d _ => some d
  | _ => none
def Instruction.writesRealMemory : Instruction → Bool
  | .storeReal .. => true
  | _ => false
def Instruction.writesNatMemory : Instruction → Bool
  | .storeNat .. => true
  | _ => false

/-- A syntactic condition checked on every primitive, including both branches
and the bodies of unbounded loops. -/
def Program.All (P : Instruction → Prop) : Program → Prop
  | .skip => True
  | .atom i => P i
  | .seq p q | .branch _ p q => p.All P ∧ q.All P
  | .repeat _ p | .while _ p => p.All P

theorem Exec.observation_eq {α : Type*} (observe : State → α)
    {p : Parameters} {i : Inputs} {prog : Program} {s t : State} {c : ℕ}
    (h : Exec p i prog s c t)
    (safe : prog.All (fun op => ∀ u, observe (step p i op u) = observe u)) :
    observe t = observe s := by
  induction h using Exec.rec
      (motive_2 := fun body _ s _ t _ =>
        body.All (fun op => ∀ u, observe (step p i op u) = observe u) → observe t = observe s) with
  | skip => rfl
  | atom op s => exact safe s
  | seq first second ih₁ ih₂ => exact (ih₂ safe.2).trans (ih₁ safe.1)
  | branchZero zero chosen ih => exact ih safe.2
  | branchNonzero nonzero chosen ih => exact ih safe.1
  | «repeat» iterations ih => exact ih safe
  | whileZero => rfl
  | whileNonzero nonzero body rest ih₁ ih₂ => exact (ih₂ safe).trans (ih₁ safe)
  | zero => rfl
  | succ first rest ih₁ ih₂ => exact (ih₂ (by assumption)).trans (ih₁ (by assumption))

theorem Program.All.mono {P Q : Instruction → Prop} {p : Program}
    (h : p.All P) (imp : ∀ op, P op → Q op) : p.All Q := by
  induction p with
  | skip => trivial
  | atom op => exact imp op h
  | seq p q hp hq | branch flag p q hp hq => exact ⟨hp h.1, hq h.2⟩
  | «repeat» bound p hp | «while» flag p hp => exact hp h

theorem step_realReg_frame (p : Parameters) (i : Inputs) (op : Instruction) (s : State) (r : ℕ)
    (h : op.realDestination ≠ some r) : (step p i op s).realReg r = s.realReg r := by
  cases op <;> simp_all [Instruction.realDestination, step, writeRealMem, writeNatMem, eq_comm]
theorem step_natReg_frame (p : Parameters) (i : Inputs) (op : Instruction) (s : State) (r : ℕ)
    (h : op.natDestination ≠ some r) : (step p i op s).natReg r = s.natReg r := by
  cases op <;> simp_all [Instruction.natDestination, step, writeRealMem, writeNatMem, eq_comm]
theorem step_realMem_frame (p : Parameters) (i : Inputs) (op : Instruction) (s : State)
    (h : op.writesRealMemory = false) : (step p i op s).realMem = s.realMem := by
  cases op <;> simp_all [Instruction.writesRealMemory, step, writeNatMem]
theorem step_natMem_frame (p : Parameters) (i : Inputs) (op : Instruction) (s : State)
    (h : op.writesNatMemory = false) : (step p i op s).natMem = s.natMem := by
  cases op <;> simp_all [Instruction.writesNatMemory, step, writeRealMem]

theorem Exec.realReg_frame {p : Parameters} {i : Inputs} {prog : Program} {s t : State} {c r : ℕ}
    (h : Exec p i prog s c t) (safe : prog.All (fun op => op.realDestination ≠ some r)) :
    t.realReg r = s.realReg r :=
  h.observation_eq (fun u => u.realReg r) (safe.mono fun op ho u => step_realReg_frame p i op u r ho)
theorem Exec.natReg_frame {p : Parameters} {i : Inputs} {prog : Program} {s t : State} {c r : ℕ}
    (h : Exec p i prog s c t) (safe : prog.All (fun op => op.natDestination ≠ some r)) :
    t.natReg r = s.natReg r :=
  h.observation_eq (fun u => u.natReg r) (safe.mono fun op ho u => step_natReg_frame p i op u r ho)
theorem Exec.realMem_frame {p : Parameters} {i : Inputs} {prog : Program} {s t : State} {c : ℕ}
    (h : Exec p i prog s c t) (safe : prog.All (fun op => op.writesRealMemory = false)) :
    t.realMem = s.realMem :=
  h.observation_eq State.realMem (safe.mono fun op ho u => step_realMem_frame p i op u ho)
theorem Exec.natMem_frame {p : Parameters} {i : Inputs} {prog : Program} {s t : State} {c : ℕ}
    (h : Exec p i prog s c t) (safe : prog.All (fun op => op.writesNatMemory = false)) :
    t.natMem = s.natMem :=
  h.observation_eq State.natMem (safe.mono fun op ho u => step_natMem_frame p i op u ho)

end Manuscript.RestrictedMachine
