import Manuscript.InputPreparation

/-!
# Concrete instruction realization of `InputPreparation.prepareEdge`

This is a narrow execution refinement, not a refinement of all SupportSum.
The program's only real inputs are N, p, a, beta, and J, in a read-only
environment. Program constants are a fixed finite alphabet. Every program
step is one addition, multiplication, division, exponential, logarithm, or
hyperbolic tangent; it cannot embed an arbitrary computed real as a literal.

The operational relation counts actual executed instructions. The concrete
15-step program is proved to return the two fields of `prepareEdge` from
any initial register state, with exactly the existing primitive budget.
-/

noncomputable section

namespace Manuscript.EdgePreparationInstructions

inductive Input where
  | size | order | coefficient | inverseTemperature | coupling
  deriving DecidableEq

inductive Constant where
  | negativeOne | two

abbrev Environment := Input → ℝ
abbrev Registers := Fin 15 → ℝ

inductive Operand where
  | input : Input → Operand
  | constant : Constant → Operand
  | register : Fin 15 → Operand

inductive Unary where
  | exponential | logarithm | hyperbolicTangent

inductive Binary where
  | add | multiply | divide

inductive Instruction where
  | unary : Fin 15 → Unary → Operand → Instruction
  | binary : Fin 15 → Binary → Operand → Operand → Instruction

def constantValue : Constant → ℝ
  | .negativeOne => -1
  | .two => 2

def readOperand (input : Environment) (registers : Registers) : Operand → ℝ
  | .input i => input i
  | .constant c => constantValue c
  | .register r => registers r

def unaryValue : Unary → ℝ → ℝ
  | .exponential => Real.exp
  | .logarithm => Real.log
  | .hyperbolicTangent => Real.tanh

def binaryValue : Binary → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .multiply => (· * ·)
  | .divide => (· / ·)

def step (input : Environment) (registers : Registers) : Instruction → Registers
  | .unary destination operation source =>
    Function.update registers destination
      (unaryValue operation (readOperand input registers source))
  | .binary destination operation left right =>
    Function.update registers destination
      (binaryValue operation (readOperand input registers left)
        (readOperand input registers right))

def run (input : Environment) : List Instruction → Registers → Registers
  | [], registers => registers
  | instruction :: rest, registers => run input rest (step input registers instruction)

/-- Each rule executes one of the six permitted real instructions. No rule
accepts an arbitrary output value or a user-supplied operation counter. -/
inductive Executes (input : Environment) :
    List Instruction → Registers → ℕ → Registers → Prop where
  | nil (registers : Registers) : Executes input [] registers 0 registers
  | cons (instruction : Instruction) (rest : List Instruction)
      (registers : Registers) {count : ℕ} {final : Registers}
      (tail : Executes input rest (step input registers instruction) count final) :
      Executes input (instruction :: rest) registers (count + 1) final

theorem run_executes (input : Environment) (program : List Instruction)
    (registers : Registers) :
    Executes input program registers program.length (run input program registers) := by
  induction program generalizing registers with
  | nil => exact Executes.nil registers
  | cons instruction rest ih =>
    exact Executes.cons instruction rest registers (ih (step input registers instruction))

/-- The five supplied scalars are read-only; they are never a writable register. -/
def edgeInputs (N p : ℕ) (a beta J : ℝ) : Environment
  | .size => N
  | .order => p
  | .coefficient => a
  | .inverseTemperature => beta
  | .coupling => J

/-- Registers 0--4 form the denominator; 5--7 form the physical coupling;
8 is its tanh; 9--14 form its log-cosh with the shared coupling in register 7. -/
def edgeProgram : List Instruction :=
  [ .unary 0 .logarithm (.input .size),
    .binary 1 .add (.input .order) (.constant .negativeOne),
    .binary 2 .divide (.register 1) (.constant .two),
    .binary 3 .multiply (.register 0) (.register 2),
    .unary 4 .exponential (.register 3),
    .binary 5 .multiply (.input .inverseTemperature) (.input .coefficient),
    .binary 6 .multiply (.register 5) (.input .coupling),
    .binary 7 .divide (.register 6) (.register 4),
    .unary 8 .hyperbolicTangent (.register 7),
    .unary 9 .exponential (.register 7),
    .binary 10 .multiply (.constant .negativeOne) (.register 7),
    .unary 11 .exponential (.register 10),
    .binary 12 .add (.register 9) (.register 11),
    .binary 13 .divide (.register 12) (.constant .two),
    .unary 14 .logarithm (.register 13) ]

theorem edgeProgram_length : edgeProgram.length = 15 := rfl

theorem edgeProgram_weight (N p : ℕ) (a beta J : ℝ) (initial : Registers) :
    run (edgeInputs N p a beta J) edgeProgram initial 8 =
      (InputPreparation.prepareEdge N p a beta J).weight := by
  rfl

theorem edgeProgram_logCosh (N p : ℕ) (a beta J : ℝ) (initial : Registers) :
    run (edgeInputs N p a beta J) edgeProgram initial 14 =
      (InputPreparation.prepareEdge N p a beta J).logCosh := by
  rfl

/-- A concrete execution with exactly fifteen arithmetic/elementary-function
instructions realizes both actual preprocessing outputs. Operand selection,
register assignment, and the surrounding input-array traversal are not
separately counted here; their refinement remains a separate obligation. -/
theorem prepareEdge_realized (N p : ℕ) (a beta J : ℝ) (initial : Registers) :
    ∃ final : Registers,
      Executes (edgeInputs N p a beta J) edgeProgram initial 15 final ∧
      final 8 = (InputPreparation.prepareEdge N p a beta J).weight ∧
      final 14 = (InputPreparation.prepareEdge N p a beta J).logCosh ∧
      15 = (InputPreparation.prepareEdge N p a beta J).operations := by
  refine ⟨run (edgeInputs N p a beta J) edgeProgram initial,
    run_executes _ _ _, edgeProgram_weight _ _ _ _ _ _,
    edgeProgram_logCosh _ _ _ _ _ _, ?_⟩
  exact (InputPreparation.prepareEdge_operations N p a beta J).symm

/-- On physical inputs the instruction outputs are the exact two target
functions of the normalized coupling, not merely matching abstract counters. -/
theorem prepareEdge_physical (N p : ℕ) (hN : 0 < N)
    (a beta J : ℝ) (initial : Registers) :
    ∃ final : Registers,
      Executes (edgeInputs N p a beta J) edgeProgram initial 15 final ∧
      final 8 = Real.tanh (beta * a * J / Model.scaleDenominator N p) ∧
      final 14 = Real.log (Real.cosh (beta * a * J / Model.scaleDenominator N p)) := by
  obtain ⟨final, hexecute, hweight, hlog, _⟩ := prepareEdge_realized N p a beta J initial
  exact ⟨final, hexecute,
    hweight.trans (InputPreparation.prepareEdge_weight hN p a beta J),
    hlog.trans (InputPreparation.prepareEdge_logCosh hN p a beta J)⟩

end Manuscript.EdgePreparationInstructions
