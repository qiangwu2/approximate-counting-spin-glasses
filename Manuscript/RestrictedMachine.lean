import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Restricted exact-real RAM execution

Programs contain no arbitrary real-valued operation, real literal, or cost
annotation. Real constants are integers encoded in syntax or designated fixed
model parameters. Input arrays are read-only. Arrays in State are constant-time
addressed RAM stores: this specifies the mathematical machine, not Lean's VM.
Every operand read, arithmetic operation and destination write is charged.
Structured control has fixed, explicit dispatch/counter costs. A top-level
realization must fix Parameters and Program before quantifying over raw Inputs;
stage programs may receive previously constructed State and compose using seq.
-/
noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedMachine

abbrev Parameters := ℕ → ℝ
structure Inputs where
  real : ℕ → ℝ
  nat : ℕ → ℕ

structure State where
  realReg : ℕ → ℝ
  natReg : ℕ → ℕ
  realMem : ℕ → ℝ
  natMem : ℕ → ℕ

def initial : State := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
def writeRealReg (s : State) (d : ℕ) (v : ℝ) : State :=
  { s with realReg := Function.update s.realReg d v }
def writeNatReg (s : State) (d v : ℕ) : State :=
  { s with natReg := Function.update s.natReg d v }
def writeRealMem (s : State) (d : ℕ) (v : ℝ) : State :=
  { s with realMem := Function.update s.realMem d v }
def writeNatMem (s : State) (d v : ℕ) : State :=
  { s with natMem := Function.update s.natMem d v }

@[simp] theorem writeRealReg_realReg (s : State) (d : ℕ) (v : ℝ) (r : ℕ) :
    (writeRealReg s d v).realReg r = if r=d then v else s.realReg r := by
  simp [writeRealReg, Function.update_apply, eq_comm]
@[simp] theorem writeRealReg_natReg (s : State) (d : ℕ) (v : ℝ) :
    (writeRealReg s d v).natReg = s.natReg := rfl
@[simp] theorem writeRealReg_realMem (s : State) (d : ℕ) (v : ℝ) :
    (writeRealReg s d v).realMem = s.realMem := rfl
@[simp] theorem writeRealReg_natMem (s : State) (d : ℕ) (v : ℝ) :
    (writeRealReg s d v).natMem = s.natMem := rfl
@[simp] theorem writeNatReg_realReg (s : State) (d v : ℕ) :
    (writeNatReg s d v).realReg = s.realReg := rfl
@[simp] theorem writeNatReg_natReg (s : State) (d v r : ℕ) :
    (writeNatReg s d v).natReg r = if r=d then v else s.natReg r := by
  simp [writeNatReg, Function.update_apply, eq_comm]
@[simp] theorem writeNatReg_realMem (s : State) (d v : ℕ) :
    (writeNatReg s d v).realMem = s.realMem := rfl
@[simp] theorem writeNatReg_natMem (s : State) (d v : ℕ) :
    (writeNatReg s d v).natMem = s.natMem := rfl

inductive Instruction where
  | rconst (destination : ℕ) (value : ℤ)
  | nconst (destination value : ℕ)
  | rcopy (destination source : ℕ)
  | ncopy (destination source : ℕ)
  | radd (destination left right : ℕ)
  | rmul (destination left right : ℕ)
  | rdiv (destination left right : ℕ)
  | rexp (destination source : ℕ)
  | rlog (destination source : ℕ)
  | rtanh (destination source : ℕ)
  | rle (destination left right : ℕ)
  | nadd (destination left right : ℕ)
  | nsub (destination left right : ℕ)
  | nmul (destination left right : ℕ)
  | ndiv (destination left right : ℕ)
  | nmod (destination left right : ℕ)
  | nle (destination left right : ℕ)
  | neq (destination left right : ℕ)
  | natToReal (destination source : ℕ)
  | readParam (destination addressRegister : ℕ)
  | readRealInput (destination addressRegister : ℕ)
  | readNatInput (destination addressRegister : ℕ)
  | loadReal (destination addressRegister : ℕ)
  | loadNat (destination addressRegister : ℕ)
  | storeReal (addressRegister source : ℕ)
  | storeNat (addressRegister source : ℕ)

def step (params : Parameters) (input : Inputs) (instruction : Instruction) (s : State) : State :=
  match instruction with
  | .rconst d z => writeRealReg s d z
  | .nconst d n => writeNatReg s d n
  | .rcopy d x => writeRealReg s d (s.realReg x)
  | .ncopy d x => writeNatReg s d (s.natReg x)
  | .radd d x y => writeRealReg s d (s.realReg x + s.realReg y)
  | .rmul d x y => writeRealReg s d (s.realReg x * s.realReg y)
  | .rdiv d x y => writeRealReg s d (s.realReg x / s.realReg y)
  | .rexp d x => writeRealReg s d (Real.exp (s.realReg x))
  | .rlog d x => writeRealReg s d (Real.log (s.realReg x))
  | .rtanh d x => writeRealReg s d (Real.tanh (s.realReg x))
  | .rle d x y => writeNatReg s d (if s.realReg x ≤ s.realReg y then 1 else 0)
  | .nadd d x y => writeNatReg s d (s.natReg x + s.natReg y)
  | .nsub d x y => writeNatReg s d (s.natReg x - s.natReg y)
  | .nmul d x y => writeNatReg s d (s.natReg x * s.natReg y)
  | .ndiv d x y => writeNatReg s d (s.natReg x / s.natReg y)
  | .nmod d x y => writeNatReg s d (s.natReg x % s.natReg y)
  | .nle d x y => writeNatReg s d (if s.natReg x ≤ s.natReg y then 1 else 0)
  | .neq d x y => writeNatReg s d (if s.natReg x = s.natReg y then 1 else 0)
  | .natToReal d x => writeRealReg s d (s.natReg x)
  | .readParam d a => writeRealReg s d (params (s.natReg a))
  | .readRealInput d a => writeRealReg s d (input.real (s.natReg a))
  | .readNatInput d a => writeNatReg s d (input.nat (s.natReg a))
  | .loadReal d a => writeRealReg s d (s.realMem (s.natReg a))
  | .loadNat d a => writeNatReg s d (s.natMem (s.natReg a))
  | .storeReal a x => writeRealMem s (s.natReg a) (s.realReg x)
  | .storeNat a x => writeNatMem s (s.natReg a) (s.natReg x)

/-- Copies read and write; binary instructions read twice, compute, write;
unary/cast instructions read, compute, write. Addressed reads/writes include
the address-register read and the actual memory access. Constants write once. -/
def instrCost : Instruction → ℕ
  | .rconst .. | .nconst .. => 1
  | .rcopy .. | .ncopy .. => 2
  | .radd .. | .rmul .. | .rdiv .. | .rle ..
  | .nadd .. | .nsub .. | .nmul .. | .ndiv .. | .nmod .. | .nle .. | .neq .. => 4
  | _ => 3

inductive Program where
  | skip
  | atom (instruction : Instruction)
  | seq (first second : Program)
  | branch (flag : ℕ) (yes no : Program)
  | repeat (boundRegister : ℕ) (body : Program)
  | while (flag : ℕ) (body : Program)

mutual
  /-- A derivation follows only the displayed primitive semantics. There is
  no evaluation oracle, external cost field, or arbitrary-result constructor. -/
  inductive Exec (params : Parameters) (input : Inputs) :
      Program → State → ℕ → State → Prop where
    | skip (s : State) : Exec params input .skip s 0 s
    | atom (instruction : Instruction) (s : State) :
        Exec params input (.atom instruction) s (instrCost instruction) (step params input instruction s)
    | seq {p q : Program} {s m t : State} {c d : ℕ}
        (first : Exec params input p s c m) (second : Exec params input q m d t) :
        Exec params input (.seq p q) s (c+d) t
    | branchZero {flag : ℕ} {yes no : Program} {s t : State} {c : ℕ}
        (zero : s.natReg flag = 0) (chosen : Exec params input no s c t) :
        Exec params input (.branch flag yes no) s (c+3) t
    | branchNonzero {flag : ℕ} {yes no : Program} {s t : State} {c : ℕ}
        (nonzero : s.natReg flag ≠ 0) (chosen : Exec params input yes s c t) :
        Exec params input (.branch flag yes no) s (c+3) t
    | repeat {bound : ℕ} {body : Program} {s t : State} {c : ℕ}
        (iterations : Repeats params input body (s.natReg bound) s c t) :
        Exec params input (.repeat bound body) s (c+2) t
    | whileZero {flag : ℕ} {body : Program} (s : State) (zero : s.natReg flag = 0) :
        Exec params input (.while flag body) s 3 s
    | whileNonzero {flag : ℕ} {body : Program} {s m t : State} {c d : ℕ}
        (nonzero : s.natReg flag ≠ 0) (bodyRun : Exec params input body s c m)
        (rest : Exec params input (.while flag body) m d t) :
        Exec params input (.while flag body) s (c+d+3) t
  /-- Repeat snapshots a bound in an internal control counter. Its initial
  copy costs two; each positive iteration costs five control operations
  (read/test/branch/decrement/write), and the final read/test/exit costs three.
  The body cannot read or replace this interpreter-owned counter. -/
  inductive Repeats (params : Parameters) (input : Inputs) :
      Program → ℕ → State → ℕ → State → Prop where
    | zero (body : Program) (s : State) : Repeats params input body 0 s 3 s
    | succ {body : Program} {n : ℕ} {s m t : State} {c d : ℕ}
        (bodyRun : Exec params input body s c m) (rest : Repeats params input body n m d t) :
        Repeats params input body (n+1) s (c+d+5) t
end

def code : List Instruction → Program
  | [] => .skip
  | i :: is => .seq (.atom i) (code is)
def runCode (params : Parameters) (input : Inputs) : List Instruction → State → State
  | [], s => s
  | i :: is, s => runCode params input is (step params input i s)
def codeCost : List Instruction → ℕ
  | [] => 0
  | i :: is => instrCost i + codeCost is

theorem exec_code (params : Parameters) (input : Inputs) (is : List Instruction) (s : State) :
    Exec params input (code is) s (codeCost is) (runCode params input is s) := by
  induction is generalizing s with
  | nil => exact Exec.skip s
  | cons i is ih => exact Exec.seq (Exec.atom i s) (ih _)

@[simp] theorem runCode_append (params : Parameters) (input : Inputs)
    (xs ys : List Instruction) (s : State) :
    runCode params input (xs++ys) s = runCode params input ys (runCode params input xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

@[simp] theorem codeCost_append (xs ys : List Instruction) :
    codeCost (xs++ys) = codeCost xs + codeCost ys := by
  induction xs with
  | nil => simp [codeCost]
  | cons x xs ih => simp [codeCost, ih, Nat.add_assoc]

theorem instrCost_pos (i : Instruction) : 0 < instrCost i := by cases i <;> simp [instrCost]

/-- A reusable bounded-loop rule. F is only a proof invariant describing
successive machine states; it is not a callable operation in Program. -/
theorem repeats_of_steps (params : Parameters) (input : Inputs) (body : Program)
    (F : ℕ → State) (cost : ℕ → ℕ) (n : ℕ)
    (steps : ∀ i < n, Exec params input body (F i) (cost i) (F (i+1))) :
    Repeats params input body n (F 0) ((∑ i ∈ Finset.range n, cost i)+5*n+3) (F n) := by
  induction n generalizing F cost with
  | zero => simpa using Repeats.zero (params := params) (input := input) body (F 0)
  | succ n ih =>
    have first := steps 0 (by omega)
    have rest := ih (fun i => F (i+1)) (fun i => cost (i+1)) (fun i hi => steps (i+1) (by omega))
    have h := Repeats.succ first rest
    have hs : (∑ i ∈ Finset.range (n+1), cost i) = cost 0 + ∑ i ∈ Finset.range n, cost (i+1) := by
      rw [Finset.sum_range_succ']
      omega
    have hc : (∑ i ∈ Finset.range (n+1), cost i)+5*(n+1)+3 =
        cost 0 + ((∑ i ∈ Finset.range n, cost (i+1))+5*n+3)+5 := by rw [hs]; omega
    rw [hc]
    exact h

/-- Uniform correctness explicitly fixes the machine program before raw input.
This specification contains no existential oracle for an input-dependent
program, result, initial cache, or counter. -/
def Realizes (params : Parameters) (program : Program) (outputRegister : ℕ)
    (target : Inputs → ℝ) (bound : Inputs → ℕ) : Prop :=
  ∀ input, ∃ count final,
    Exec params input program initial count final ∧
    final.realReg outputRegister = target input ∧ count ≤ bound input

end Manuscript.RestrictedMachine
