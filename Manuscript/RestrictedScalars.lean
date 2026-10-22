import Manuscript.RestrictedMachine
import Manuscript.LogApprox

/-! Fixed register programs for the scalar stages of Algorithm 1.
All values are produced by instructions from existing registers and integer
constants. Registers holding model constants are supplied by the enclosing
program's parameter reads. -/

noncomputable section
namespace Manuscript.RestrictedScalars
open RestrictedMachine

/-- Inputs C, delta, epsilon, s occupy real registers 0,1,2,3.
Outputs z,u occupy 14,19. Only real registers 10--21 are modified. -/
def budgetCode : List Instruction :=
  [ .rconst 20 2,
    .rmul 10 20 0,
    .rdiv 11 1 10,
    .rlog 12 11,
    .rdiv 13 12 3,
    .rexp 14 13,
    .rmul 15 2 2,
    .rmul 16 1 15,
    .rmul 17 14 14,
    .rmul 18 16 17,
    .rconst 21 8,
    .rdiv 19 18 21 ]

/-- Inputs N,h occupy real registers 0,1. Outputs are the mean in 16,
the positive and negative spin weights in 18,23, and log base in 25. -/
def fieldCode : List Instruction :=
  [ .rconst 20 2, .rconst 21 (-1),
    .rexp 10 1,
    .rmul 11 21 1,
    .rexp 12 11,
    .radd 13 10 12,
    .rdiv 14 13 20,
    .rmul 15 20 14,
    .rtanh 16 1,
    .rexp 17 1,
    .rdiv 18 17 15,
    .rmul 19 21 1,
    .rexp 22 19,
    .rdiv 23 22 15,
    .rlog 24 15,
    .rmul 25 0 24 ]

/-- Inputs log-prefactor and graph approximation occupy real registers 0,1.
Output is real register 3. The comparison flag is natural register 0. -/
def finish : Program :=
  .seq (code [.rconst 2 0, .rle 0 1 2])
    (.branch 0
      (.atom (.rcopy 3 0))
      (code [.rlog 2 1, .radd 3 0 2]))

theorem budget_cost : codeCost budgetCode = 40 := rfl

theorem budget_values (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input budgetCode s).realReg 14 =
      (InputPreparation.prepareBudget (s.realReg 0) (s.realReg 1)
        (s.realReg 2) (s.realReg 3)).z ∧
    (runCode params input budgetCode s).realReg 19 =
      (InputPreparation.prepareBudget (s.realReg 0) (s.realReg 1)
        (s.realReg 2) (s.realReg 3)).u := by
  constructor <;> rfl

theorem budget_frame (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input budgetCode s).natReg = s.natReg ∧
    (runCode params input budgetCode s).realMem = s.realMem ∧
    (runCode params input budgetCode s).natMem = s.natMem := by
  exact ⟨rfl, rfl, rfl⟩

theorem budget_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ final : State, Exec params input (code budgetCode) s 40 final ∧
      final.realReg 14 =
        (InputPreparation.prepareBudget (s.realReg 0) (s.realReg 1)
          (s.realReg 2) (s.realReg 3)).z ∧
      final.realReg 19 =
        (InputPreparation.prepareBudget (s.realReg 0) (s.realReg 1)
          (s.realReg 2) (s.realReg 3)).u :=
  ⟨runCode params input budgetCode s, exec_code _ _ _ _, budget_values _ _ _⟩

theorem field_cost : codeCost fieldCode = 52 := rfl

theorem field_values (params : Parameters) (input : Inputs) (s : State)
    (N : ℕ) (hN : s.realReg 0 = N) :
    (runCode params input fieldCode s).realReg 16 =
      (InputPreparation.prepareField N (s.realReg 1)).mean ∧
    (runCode params input fieldCode s).realReg 18 =
      (InputPreparation.prepareField N (s.realReg 1)).plusWeight ∧
    (runCode params input fieldCode s).realReg 23 =
      (InputPreparation.prepareField N (s.realReg 1)).minusWeight ∧
    (runCode params input fieldCode s).realReg 25 =
      (InputPreparation.prepareField N (s.realReg 1)).logBase := by
  simp [fieldCode, runCode, step, InputPreparation.prepareField,
    InputPreparation.hyperbolicCosine, InputPreparation.hyperbolicTangent,
    InputPreparation.divide, InputPreparation.exponential, InputPreparation.logarithm,
    SpinGlass.ArithmeticEvaluation.mul, SpinGlass.ArithmeticEvaluation.add,
    SpinGlass.ArithmeticEvaluation.literal, hN]

theorem field_frame (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input fieldCode s).natReg = s.natReg ∧
    (runCode params input fieldCode s).realMem = s.realMem ∧
    (runCode params input fieldCode s).natMem = s.natMem :=
  ⟨rfl, rfl, rfl⟩

theorem finish_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ cost final, Exec params input finish s cost final ∧ cost ≤ 15 ∧
      final.realReg 3 = SpinGlass.logOutput (s.realReg 0) (s.realReg 1) ∧
      final.realMem = s.realMem ∧ final.natMem = s.natMem := by
  let test := runCode params input [.rconst 2 0, .rle 0 1 2] s
  have ht := exec_code params input [.rconst 2 0, .rle 0 1 2] s
  by_cases h : s.realReg 1 ≤ 0
  · have hf : test.natReg 0 ≠ 0 := by simp [test, runCode, step, h]
    have hc := Exec.seq ht (Exec.branchNonzero
      (no := code [.rlog 2 1, .radd 3 0 2]) hf (Exec.atom (.rcopy 3 0) test))
    refine ⟨10, _, hc, by omega, ?_, rfl, rfl⟩
    simp [step, test, runCode, SpinGlass.logOutput, not_lt.mpr h]
  · have hf : test.natReg 0 = 0 := by simp [test, runCode, step, h]
    have hc := Exec.seq ht
      (Exec.branchZero (yes := .atom (.rcopy 3 0)) hf
        (exec_code params input [.rlog 2 1, .radd 3 0 2] test))
    refine ⟨15, _, hc, by omega, ?_, rfl, rfl⟩
    simp [test, runCode, step, SpinGlass.logOutput, lt_of_not_ge h]

end Manuscript.RestrictedScalars
