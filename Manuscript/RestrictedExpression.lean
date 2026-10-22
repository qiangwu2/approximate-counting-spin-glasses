import Manuscript.RestrictedMachine

/-!
Arithmetic expressions compile to the restricted RAM. Every leaf is an
integer, a fixed model parameter, a raw input read, or an addressed cache
read. There is no arbitrary real literal or pure-function constructor.
This is an arithmetic-stage compiler: generation of an input-dependent
expression or cache must separately be executed by a uniform machine.
-/
noncomputable section
namespace Manuscript.RestrictedMachine
namespace RealExpression

inductive Binary where | add | mul | div
inductive Unary where | exp | log | tanh
inductive Expr where
  | integer (z : ℤ)
  | parameter (address : ℕ)
  | input (address : ℕ)
  | memory (address : ℕ)
  | naturalInput (address : ℕ)
  | binary (op : Binary) (left right : Expr)
  | unary (op : Unary) (arg : Expr)

def Binary.eval : Binary → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .mul => (· * ·)
  | .div => (· / ·)
def Unary.eval : Unary → ℝ → ℝ
  | .exp => Real.exp
  | .log => Real.log
  | .tanh => Real.tanh
def Binary.instruction : Binary → ℕ → ℕ → ℕ → Instruction
  | .add => Instruction.radd
  | .mul => Instruction.rmul
  | .div => Instruction.rdiv
def Unary.instruction : Unary → ℕ → ℕ → Instruction
  | .exp => Instruction.rexp
  | .log => Instruction.rlog
  | .tanh => Instruction.rtanh

def eval (params : Parameters) (raw : Inputs) (memory : ℕ → ℝ) : Expr → ℝ
  | .integer z => z
  | .parameter a => params a
  | .input a => raw.real a
  | .memory a => memory a
  | .naturalInput a => raw.nat a
  | .binary op x y => op.eval (eval params raw memory x) (eval params raw memory y)
  | .unary op x => op.eval (eval params raw memory x)

/-- `base` is the first available real register; `address` is one natural
scratch register. The compiler never writes either memory array. -/
def compile : Expr → ℕ → ℕ → List Instruction
  | .integer z, b, _ => [.rconst b z]
  | .parameter a, b, t => [.nconst t a, .readParam b t]
  | .input a, b, t => [.nconst t a, .readRealInput b t]
  | .memory a, b, t => [.nconst t a, .loadReal b t]
  | .naturalInput a, b, t => [.nconst t a, .readNatInput t t, .natToReal b t]
  | .binary op x y, b, t => compile x b t ++ compile y (b+1) t ++ [op.instruction b b (b+1)]
  | .unary op x, b, t => compile x b t ++ [op.instruction b b]

def cost : Expr → ℕ
  | .integer _ => 1
  | .parameter _ | .input _ | .memory _ => 4
  | .naturalInput _ => 7
  | .binary _ x y => cost x + cost y + 4
  | .unary _ x => cost x + 3
def size : Expr → ℕ
  | .integer _ | .parameter _ | .input _ | .memory _ | .naturalInput _ => 1
  | .binary _ x y => size x + size y + 1
  | .unary _ x => size x + 1

@[simp] theorem binary_cost (op : Binary) (d x y : ℕ) : instrCost (op.instruction d x y) = 4 := by
  cases op <;> rfl
@[simp] theorem unary_cost (op : Unary) (d x : ℕ) : instrCost (op.instruction d x) = 3 := by
  cases op <;> rfl
@[simp] theorem binary_step (op : Binary) (p : Parameters) (i : Inputs) (d x y : ℕ) (s : State) :
    step p i (op.instruction d x y) s = writeRealReg s d (op.eval (s.realReg x) (s.realReg y)) := by
  cases op <;> rfl
@[simp] theorem unary_step (op : Unary) (p : Parameters) (i : Inputs) (d x : ℕ) (s : State) :
    step p i (op.instruction d x) s = writeRealReg s d (op.eval (s.realReg x)) := by
  cases op <;> rfl

theorem compile_cost (e : Expr) (b t : ℕ) : codeCost (compile e b t) = cost e := by
  induction e generalizing b with
  | binary op x y hx hy => simp [compile, cost, hx, hy, codeCost, Nat.add_assoc]
  | unary op x hx => simp [compile, cost, hx, codeCost]
  | _ => rfl

theorem cost_le (e : Expr) : cost e ≤ 7 * size e := by
  induction e <;> simp_all [cost, size] <;> omega

/-- Value and complete frame guarantee for an arbitrary starting state.
In particular this theorem does not assume the value it is proving. -/
theorem compile_spec (e : Expr) (p : Parameters) (i : Inputs) (b t : ℕ) (s : State) :
    let out := runCode p i (compile e b t) s
    out.realReg b = eval p i s.realMem e ∧
    (∀ r < b, out.realReg r = s.realReg r) ∧
    out.realMem = s.realMem ∧ out.natMem = s.natMem ∧
    (∀ r, r ≠ t → out.natReg r = s.natReg r) := by
  induction e generalizing b s with
  | integer z =>
    simp [compile, runCode, step, eval]
    intro r hr heq
    omega
  | parameter a =>
    simp [compile, runCode, step, eval]
    constructor
    · intro r hr heq; omega
    · intro r hr heq; exact False.elim (hr heq)
  | input a =>
    simp [compile, runCode, step, eval]
    constructor
    · intro r hr heq; omega
    · intro r hr heq; exact False.elim (hr heq)
  | memory a =>
    simp [compile, runCode, step, eval]
    constructor
    · intro r hr heq; omega
    · intro r hr heq; exact False.elim (hr heq)
  | naturalInput a =>
    simp [compile, runCode, step, eval]
    constructor
    · intro r hr heq; omega
    · intro r hr; simp [hr]
  | binary op x y hx hy =>
    dsimp only at hx hy ⊢
    let m := runCode p i (compile x b t) s
    let n := runCode p i (compile y (b+1) t) m
    have h₁ := hx b s
    have h₂ := hy (b+1) m
    change m.realReg b = _ ∧ _ at h₁
    change n.realReg (b+1) = _ ∧ _ at h₂
    simp only [compile, runCode_append, runCode, binary_step]
    change (writeRealReg n b (op.eval (n.realReg b) (n.realReg (b+1)))).realReg b = _ ∧ _
    simp only [writeRealReg_realReg, if_pos, writeRealReg_realMem, writeRealReg_natMem,
      writeRealReg_natReg, eval]
    refine ⟨?_, ?_, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1, ?_⟩
    · rw [h₂.2.1 b (by omega), h₁.1, h₂.1, h₁.2.2.1]
    · intro r hr
      rw [if_neg (by omega), h₂.2.1 r (by omega), h₁.2.1 r hr]
    · intro r hr
      exact (h₂.2.2.2.2 r hr).trans (h₁.2.2.2.2 r hr)
  | unary op x hx =>
    dsimp only at hx ⊢
    let m := runCode p i (compile x b t) s
    have h := hx b s
    change m.realReg b = _ ∧ _ at h
    simp only [compile, runCode_append, runCode, unary_step]
    change (writeRealReg m b (op.eval (m.realReg b))).realReg b = _ ∧ _
    simp only [writeRealReg_realReg, if_pos, writeRealReg_realMem, writeRealReg_natMem,
      writeRealReg_natReg, eval]
    refine ⟨?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
    · rw [h.1]
    · intro r hr
      rw [if_neg (by omega), h.2.1 r hr]

theorem compile_exec (e : Expr) (p : Parameters) (i : Inputs) (b t : ℕ) (s : State) :
    Exec p i (code (compile e b t)) s (cost e) (runCode p i (compile e b t) s) := by
  simpa only [compile_cost] using exec_code p i (compile e b t) s

end RealExpression
end Manuscript.RestrictedMachine
