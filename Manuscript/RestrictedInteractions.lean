import Manuscript.RestrictedMachine
import Manuscript.InputPreparation

/-! Actual primitive instructions for preparing a physical interaction.
The source registers are inputs to the macro, not an arbitrary real literal
instruction.  The read-composed macro obtains all five from read-only inputs.
-/
noncomputable section
namespace Manuscript.RestrictedInteractions
open RestrictedMachine

/-- Source registers 40--44 contain N,p,a_p,beta,J_e.  Destination 55 is
`tanh(beta*a_p*J_e/N^((p-1)/2))`; destination 60 is its log-cosh.
Every intermediate arithmetic operation is a restricted-machine instruction. -/
def edgeCode : List Instruction :=
  [.rconst 45 (-1), .rconst 46 2,
   .rlog 47 40,
   .radd 48 41 45,
   .rdiv 48 48 46,
   .rmul 49 47 48,
   .rexp 49 49,
   .rmul 50 43 42,
   .rmul 51 50 44,
   .rdiv 52 51 49,
   .rtanh 55 52,
   .rexp 56 52,
   .rmul 57 45 52,
   .rexp 57 57,
   .radd 58 56 57,
   .rdiv 59 58 46,
   .rlog 60 59]

/-- Natural registers 40--44 specify the addresses of the five source inputs.
N and p are read from the natural input array and converted to reals;
a_p is a model parameter, and beta,J_e are physical real inputs. -/
def readEdgeCode : List Instruction :=
  [.readNatInput 45 40, .natToReal 40 45,
   .readNatInput 45 41, .natToReal 41 45,
   .readParam 42 42, .readRealInput 43 43, .readRealInput 44 44] ++ edgeCode

def normalizedArgument (s : State) : ℝ :=
  s.realReg 43 * s.realReg 42 * s.realReg 44 /
    Real.exp (Real.log (s.realReg 40) * ((s.realReg 41 + (-1)) / 2))

@[simp] theorem edgeCode_cost : codeCost edgeCode = 56 := by
  norm_num [edgeCode, codeCost, instrCost]

theorem edgeCode_weight (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input edgeCode s).realReg 55 = Real.tanh (normalizedArgument s) := by
  simp [edgeCode, runCode, step, normalizedArgument]

theorem edgeCode_logCosh (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input edgeCode s).realReg 60 = Real.log (Real.cosh (normalizedArgument s)) := by
  simp [edgeCode, runCode, step, normalizedArgument, Real.cosh_eq]

theorem edgeCode_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input (code edgeCode) s 56 final ∧
      final.realReg 55 = Real.tanh (normalizedArgument s) ∧
      final.realReg 60 = Real.log (Real.cosh (normalizedArgument s)) := by
  refine ⟨runCode params input edgeCode s, ?_, edgeCode_weight _ _ _, edgeCode_logCosh _ _ _⟩
  simpa using exec_code params input edgeCode s

theorem edgeCode_memory (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input edgeCode s).natReg = s.natReg ∧
    (runCode params input edgeCode s).realMem = s.realMem ∧
    (runCode params input edgeCode s).natMem = s.natMem := by
  simp [edgeCode, runCode, step]

theorem edgeCode_frame (params : Parameters) (input : Inputs) (s : State) (r : ℕ)
    (hr : r < 45 ∨ 60 < r) :
    (runCode params input edgeCode s).realReg r = s.realReg r := by
  have h45 : r ≠ 45 := by omega
  have h46 : r ≠ 46 := by omega
  have h47 : r ≠ 47 := by omega
  have h48 : r ≠ 48 := by omega
  have h49 : r ≠ 49 := by omega
  have h50 : r ≠ 50 := by omega
  have h51 : r ≠ 51 := by omega
  have h52 : r ≠ 52 := by omega
  have h55 : r ≠ 55 := by omega
  have h56 : r ≠ 56 := by omega
  have h57 : r ≠ 57 := by omega
  have h58 : r ≠ 58 := by omega
  have h59 : r ≠ 59 := by omega
  have h60 : r ≠ 60 := by omega
  simp [edgeCode, runCode, step, h45,h46,h47,h48,h49,h50,h51,h52,h55,h56,h57,h58,h59,h60]

@[simp] theorem readEdgeCode_cost : codeCost readEdgeCode = 77 := by
  norm_num [readEdgeCode, codeCost, instrCost, edgeCode_cost]

def rawEdge (params : Parameters) (input : Inputs) (s : State) : InputPreparation.EdgeData :=
  InputPreparation.prepareEdge (input.nat (s.natReg 40)) (input.nat (s.natReg 41))
    (params (s.natReg 42)) (input.real (s.natReg 43)) (input.real (s.natReg 44))

theorem readEdgeCode_weight (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input readEdgeCode s).realReg 55 = (rawEdge params input s).weight := by
  rw [readEdgeCode, runCode_append, edgeCode_weight]
  simp [rawEdge, normalizedArgument, runCode, step, InputPreparation.prepareEdge,
    InputPreparation.denominator, InputPreparation.divide, InputPreparation.exponential,
    InputPreparation.logarithm, InputPreparation.hyperbolicTangent,
    SpinGlass.ArithmeticEvaluation.add, SpinGlass.ArithmeticEvaluation.mul,
    SpinGlass.ArithmeticEvaluation.literal]

theorem readEdgeCode_logCosh (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input readEdgeCode s).realReg 60 = (rawEdge params input s).logCosh := by
  rw [readEdgeCode, runCode_append, edgeCode_logCosh]
  simp [rawEdge, normalizedArgument, runCode, step, InputPreparation.prepareEdge,
    InputPreparation.denominator, InputPreparation.divide, InputPreparation.exponential,
    InputPreparation.logarithm, InputPreparation.hyperbolicCosine, Real.cosh_eq,
    SpinGlass.ArithmeticEvaluation.add, SpinGlass.ArithmeticEvaluation.mul,
    SpinGlass.ArithmeticEvaluation.literal]

theorem readEdgeCode_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input (code readEdgeCode) s 77 final ∧
      final.realReg 55 = (rawEdge params input s).weight ∧
      final.realReg 60 = (rawEdge params input s).logCosh := by
  refine ⟨runCode params input readEdgeCode s, ?_, readEdgeCode_weight _ _ _, readEdgeCode_logCosh _ _ _⟩
  simpa using exec_code params input readEdgeCode s

theorem readEdgeCode_physical (params : Parameters) (input : Inputs) (s : State)
    (hN : 0 < input.nat (s.natReg 40)) :
    ∃ final, Exec params input (code readEdgeCode) s 77 final ∧
      final.realReg 55 = Real.tanh
        (input.real (s.natReg 43) * params (s.natReg 42) * input.real (s.natReg 44) /
          Model.scaleDenominator (input.nat (s.natReg 40)) (input.nat (s.natReg 41))) ∧
      final.realReg 60 = Real.log (Real.cosh
        (input.real (s.natReg 43) * params (s.natReg 42) * input.real (s.natReg 44) /
          Model.scaleDenominator (input.nat (s.natReg 40)) (input.nat (s.natReg 41)))) := by
  obtain ⟨final, he, hw, hl⟩ := readEdgeCode_realized params input s
  refine ⟨final, he, ?_, ?_⟩
  · simpa [rawEdge, InputPreparation.prepareEdge_weight hN] using hw
  · simpa [rawEdge, InputPreparation.prepareEdge_logCosh hN] using hl

@[simp] theorem readEdgeCode_natReg (params : Parameters) (input : Inputs) (s : State) (r : ℕ)
    (hr : r ≠ 45) :
    (runCode params input readEdgeCode s).natReg r = s.natReg r := by
  simp [readEdgeCode, edgeCode, runCode, step, hr]

@[simp] theorem readEdgeCode_realMem (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input readEdgeCode s).realMem = s.realMem := by
  simp [readEdgeCode, edgeCode, runCode, step]

@[simp] theorem readEdgeCode_natMem (params : Parameters) (input : Inputs) (s : State) :
    (runCode params input readEdgeCode s).natMem = s.natMem := by
  simp [readEdgeCode, edgeCode, runCode, step]

/-- Input layout: nat[0]=N, nat[1]=M, nat[i+2]=order of interaction i;
real[0]=beta, real[i+1]=J_i, Parameters[p]=a_p. This is a raw input layout,
not a supplied weight/log-cosh table. -/
def tableEdge (params : Parameters) (input : Inputs) (i : ℕ) : InputPreparation.EdgeData :=
  InputPreparation.prepareEdge (input.nat 0) (input.nat (i+2))
    (params (input.nat (i+2))) (input.real 0) (input.real (i+1))

def tableInit : List Instruction :=
  [.nconst 40 0, .nconst 43 0, .nconst 62 0, .nconst 63 1,
   .nconst 65 2, .nconst 66 1, .readNatInput 61 66, .nconst 64 0]

def tablePrefix : List Instruction :=
  [.nadd 41 62 65, .readNatInput 42 41, .nadd 44 62 63]

def tableSuffix : List Instruction :=
  [.storeReal 64 55, .nadd 64 64 63, .storeReal 64 60,
   .nadd 64 64 63, .nadd 62 62 63]

def tableBody : List Instruction := tablePrefix ++ readEdgeCode ++ tableSuffix

def tableProgram : Program := .seq (code tableInit) (.repeat 61 (code tableBody))

def TableInvariant (params : Parameters) (input : Inputs) (i : ℕ) (s : State) : Prop :=
  s.natReg 40 = 0 ∧ s.natReg 43 = 0 ∧ s.natReg 62 = i ∧ s.natReg 63 = 1 ∧
  s.natReg 65 = 2 ∧ s.natReg 64 = 2*i ∧
  (∀ j < i, s.realMem (2*j) = (tableEdge params input j).weight ∧
    s.realMem (2*j+1) = (tableEdge params input j).logCosh)

@[simp] theorem tableInit_cost : codeCost tableInit = 10 := by
  norm_num [tableInit, codeCost, instrCost]

@[simp] theorem tableBody_cost : codeCost tableBody = 106 := by
  norm_num [tableBody, tablePrefix, tableSuffix, codeCost, instrCost, readEdgeCode_cost]

theorem table_body_invariant (params : Parameters) (input : Inputs) {i : ℕ} {s : State}
    (hs : TableInvariant params input i s) :
    TableInvariant params input (i+1) (runCode params input tableBody s) := by
  rcases hs with ⟨h40,h43,h62,h63,h65,h64,htable⟩
  let pre := runCode params input tablePrefix s
  let mid := runCode params input readEdgeCode pre
  have hpre : rawEdge params input pre = tableEdge params input i := by
    simp [pre, rawEdge, tableEdge, tablePrefix, runCode, step, h40,h43,h62,h63,h65]
  have hw : mid.realReg 55 = (tableEdge params input i).weight := by
    change (runCode params input readEdgeCode pre).realReg 55 = _
    rw [readEdgeCode_weight, hpre]
  have hl : mid.realReg 60 = (tableEdge params input i).logCosh := by
    change (runCode params input readEdgeCode pre).realReg 60 = _
    rw [readEdgeCode_logCosh, hpre]
  have hm : mid.realMem = s.realMem := by
    simp [mid, pre, tablePrefix, runCode, step]
  have hnr (r : ℕ) (hr : r ≠ 45) : mid.natReg r = pre.natReg r :=
    readEdgeCode_natReg params input pre r hr
  have hstep : runCode params input tableBody s = runCode params input tableSuffix mid := by
    simp [tableBody, mid, pre]
  rw [hstep]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try { simp [tableSuffix, runCode, step, writeRealMem, hnr, pre, tablePrefix, h40,h43,h62,h63,h65,h64] <;> omega }
  intro j hj
  have hji : j ≤ i := by omega
  by_cases he : j = i
  · subst j
    simp [tableSuffix, runCode, step, writeRealMem, hw, hl, hnr, pre, tablePrefix,
      h40,h43,h62,h63,h65,h64, Function.update_apply]
  · have hjlt : j < i := by omega
    obtain ⟨hjw,hjl⟩ := htable j hjlt
    have hne1 : 2*j ≠ 2*i := by omega
    have hne2 : 2*j ≠ 2*i+1 := by omega
    have hne3 : 2*j+1 ≠ 2*i := by omega
    have hne4 : 2*j+1 ≠ 2*i+1 := by omega
    simp [tableSuffix, runCode, step, writeRealMem, hm, hw, hl, hnr, pre, tablePrefix,
      h40,h43,h62,h63,h65,h64, Function.update_apply, hne1,hne2,hne3,hne4, hjw,hjl]

theorem table_body_repeats (params : Parameters) (input : Inputs) (m : ℕ) :
    ∀ i s, TableInvariant params input i s →
      ∃ final, Repeats params input (code tableBody) m s (111*m+3) final ∧
        TableInvariant params input (i+m) final := by
  induction m with
  | zero =>
      intro i s hs
      exact ⟨s, by simpa using Repeats.zero (params := params) (input := input) (code tableBody) s,
        by simpa using hs⟩
  | succ m ih =>
      intro i s hs
      let middle := runCode params input tableBody s
      have hm : TableInvariant params input (i+1) middle := table_body_invariant params input hs
      obtain ⟨final, he, hf⟩ := ih (i+1) middle hm
      refine ⟨final, ?_, ?_⟩
      · have hb : Exec params input (code tableBody) s 106 middle := by
          simpa [middle] using exec_code params input tableBody s
        convert Repeats.succ hb he using 1 <;> omega
      · convert hf using 1 <;> omega

/-- A single fixed program prepares every interaction from the read-only raw
arrays. Neither the program nor its cost depends on the coupling values. -/
theorem table_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input tableProgram s (111*input.nat 1+15) final ∧
      ∀ j < input.nat 1,
        final.realMem (2*j) = (tableEdge params input j).weight ∧
        final.realMem (2*j+1) = (tableEdge params input j).logCosh := by
  let start := runCode params input tableInit s
  have hi : TableInvariant params input 0 start := by
    simp [TableInvariant, start, tableInit, runCode, step]
  have hb : start.natReg 61 = input.nat 1 := by
    simp [start, tableInit, runCode, step]
  obtain ⟨final, he, hf⟩ := table_body_repeats params input (input.nat 1) 0 start hi
  have he' : Repeats params input (code tableBody) (start.natReg 61) start
      (111*input.nat 1+3) final := by simpa [hb] using he
  have hloop := Exec.repeat he'
  refine ⟨final, ?_, ?_⟩
  · have hinit : Exec params input (code tableInit) s 10 start := by
      simpa [start] using exec_code params input tableInit s
    change Exec params input (.seq (code tableInit) (.repeat 61 (code tableBody))) s _ final
    convert Exec.seq hinit hloop using 1 <;> omega
  · exact (by simpa only [Nat.zero_add] using hf.2.2.2.2.2.2)

end Manuscript.RestrictedInteractions
