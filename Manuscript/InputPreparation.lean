import Manuscript.Model
import Manuscript.OriginalLawLowerTail
import Manuscript.InputIndices
import SpinGlass.ArithmeticEvaluation
import SpinGlass.AccuracyBudget

/-! Counted mixed-model input preparation and the exact budgets in Algorithm 1.
Elementary real operations have the manuscript's unit cost. Finite input-array
traversals use recursive lists, including index/read/write overhead. -/

noncomputable section
open scoped BigOperators
namespace Manuscript.InputPreparation
open SpinGlass.ArithmeticEvaluation

def divide (x y : Computation) : Computation :=
  ⟨x.value / y.value, x.operations + y.operations + 1⟩
def exponential (x : Computation) : Computation := ⟨Real.exp x.value, x.operations + 1⟩
def logarithm (x : Computation) : Computation := ⟨Real.log x.value, x.operations + 1⟩
def hyperbolicTangent (x : Computation) : Computation := ⟨Real.tanh x.value, x.operations + 1⟩

def hyperbolicCosine (x : ℝ) : Computation :=
  divide (add (exponential (literal x))
    (exponential (mul (literal (-1)) (literal x)))) (literal 2)

@[simp] theorem hyperbolicCosine_value (x : ℝ) :
    (hyperbolicCosine x).value = Real.cosh x := by
  simp [hyperbolicCosine, divide, add, exponential, mul, literal, Real.cosh_eq]

@[simp] theorem hyperbolicCosine_operations (x : ℝ) :
    (hyperbolicCosine x).operations = 5 := rfl

/-- The physical half-integer denominator computed with logarithm and exponential. -/
def denominator (N p : ℕ) : Computation :=
  exponential (mul (logarithm (literal N))
    (divide (add (literal p) (literal (-1))) (literal 2)))

@[simp] theorem denominator_value {N : ℕ} (hN : 0 < N) (p : ℕ) :
    (denominator N p).value = Model.scaleDenominator N p := by
  simp only [denominator, exponential, mul, logarithm, literal, divide, add,
    Model.scaleDenominator, Real.rpow_def_of_pos (Nat.cast_pos.mpr hN)]
  congr 1

@[simp] theorem denominator_operations (N p : ℕ) : (denominator N p).operations = 5 := rfl

structure EdgeData where
  weight : ℝ
  logCosh : ℝ
  operations : ℕ

/-- The coefficient is computed once, then shared by tanh and log-cosh. -/
def prepareEdge (N p : ℕ) (a beta J : ℝ) : EdgeData :=
  let x := divide (mul (mul (literal beta) (literal a)) (literal J)) (denominator N p)
  let w := hyperbolicTangent (literal x.value)
  let l := logarithm (hyperbolicCosine x.value)
  ⟨w.value, l.value, x.operations + w.operations + l.operations⟩

@[simp] theorem prepareEdge_operations (N p : ℕ) (a beta J : ℝ) :
    (prepareEdge N p a beta J).operations = 15 := rfl

@[simp] theorem prepareEdge_weight {N : ℕ} (hN : 0 < N) (p : ℕ) (a beta J : ℝ) :
    (prepareEdge N p a beta J).weight = Real.tanh (beta * a * J / Model.scaleDenominator N p) := by
  simp [prepareEdge, hyperbolicTangent, divide, mul, literal, denominator_value hN]

@[simp] theorem prepareEdge_logCosh {N : ℕ} (hN : 0 < N) (p : ℕ) (a beta J : ℝ) :
    (prepareEdge N p a beta J).logCosh =
      Real.log (Real.cosh (beta * a * J / Model.scaleDenominator N p)) := by
  simp [prepareEdge, logarithm, divide, mul, literal, denominator_value hN]

structure EdgeArray (E : Type*) where
  entries : List (E × EdgeData)
  cache : E → EdgeData
  operations : ℕ

/-- Five index/control/read/write operations are charged per input-array entry. -/
def prepareEdges (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (J : Model.Edge N P → ℝ) : List (Model.Edge N P) → EdgeArray (Model.Edge N P)
  | [] => ⟨[], fun _ => ⟨0, 0, 0⟩, 0⟩
  | e :: es =>
    let d := prepareEdge N e.val.card (a e.val.card) beta (J e)
    let tail := prepareEdges N P a beta J es
    ⟨(e, d) :: tail.entries, Function.update tail.cache e d, d.operations + tail.operations + 5⟩

@[simp] theorem prepareEdges_entries (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta : ℝ) (J : Model.Edge N P → ℝ) (es : List (Model.Edge N P)) :
    (prepareEdges N P a beta J es).entries =
      es.map (fun e => (e, prepareEdge N e.val.card (a e.val.card) beta (J e))) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [prepareEdges, ih]

@[simp] theorem prepareEdges_operations (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta : ℝ) (J : Model.Edge N P → ℝ) (es : List (Model.Edge N P)) :
    (prepareEdges N P a beta J es).operations = 20 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [prepareEdges, ih]; omega

/-- The finite indexed cache is filled by the same traversal. Array update and
read are the finite-index primitives in the manuscript's operation model. -/
theorem prepareEdges_cache (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta : ℝ) (J : Model.Edge N P → ℝ) (es : List (Model.Edge N P))
    (e : Model.Edge N P) (he : e ∈ es) :
    (prepareEdges N P a beta J es).cache e = prepareEdge N e.val.card (a e.val.card) beta (J e) := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    by_cases hef : e = f
    · subst f
      simp [prepareEdges]
    · simp only [prepareEdges, Function.update_of_ne hef]
      exact ih ((List.mem_cons.mp he).resolve_left hef)

structure FieldData where
  mean : ℝ
  plusWeight : ℝ
  minusWeight : ℝ
  logBase : ℝ
  operations : ℕ

/-- Shared field quantities are evaluated once for every local-cube computation. -/
def prepareField (N : ℕ) (h : ℝ) : FieldData :=
  let c := hyperbolicCosine h
  let d := mul (literal 2) (literal c.value)
  let m := hyperbolicTangent (literal h)
  let plus := divide (exponential (literal h)) (literal d.value)
  let minus := divide (exponential (mul (literal (-1)) (literal h))) (literal d.value)
  let base := mul (literal N) (logarithm (literal d.value))
  ⟨m.value, plus.value, minus.value, base.value,
    c.operations + d.operations + m.operations + plus.operations + minus.operations + base.operations⟩

@[simp] theorem prepareField_operations (N : ℕ) (h : ℝ) :
    (prepareField N h).operations = 14 := rfl

@[simp] theorem prepareField_mean (N : ℕ) (h : ℝ) : (prepareField N h).mean = Real.tanh h := rfl

@[simp] theorem prepareField_weight (N : ℕ) (h : ℝ) (b : Bool) :
    (if b then (prepareField N h).minusWeight else (prepareField N h).plusWeight) =
      FieldExpansion.spinWeight h b := by
  cases b <;> simp [prepareField, divide, exponential, mul, literal,
    FieldExpansion.spinWeight, SpinGlass.Expansion.spinSign]

@[simp] theorem prepareField_logBase (N : ℕ) (h : ℝ) :
    (prepareField N h).logBase = N * Real.log (2 * Real.cosh h) := by
  simp [prepareField, mul, literal, logarithm]

def logBase (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (J : Model.Edge N P → ℝ) : ℝ :=
  N * Real.log (2 * Real.cosh h) + ∑ e, Real.log (Real.cosh (Model.coefficient N P a beta J e))

theorem logBase_eq_log_prefactor (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Model.Edge N P → ℝ) :
    logBase N P a beta h J = Real.log (Model.prefactor N P a beta h J) := by
  rw [Model.prefactor, Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_prod (fun e _ => (Real.cosh_pos _).ne')]
  rfl

theorem targetLog_decomposition (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Model.Edge N P → ℝ) :
    Real.log (Model.partition N P a beta h J) =
      logBase N P a beta h J + Real.log (Model.normalizedPartition N P a beta h J) := by
  rw [logBase_eq_log_prefactor, Model.partition_eq_fieldPartition,
    Model.prefactor_eq_fieldPrefactor, Model.normalizedPartition_eq_fieldNormalized]
  exact FieldExpansion.log_partition_decomposition _ _ _ _

structure PreparedInput (N : ℕ) (P : Finset ℕ) where
  entries : List (Model.Edge N P × EdgeData)
  cache : Model.Edge N P → EdgeData
  field : FieldData
  logPrefactor : ℝ
  operations : ℕ

def prepareInput (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (J : Model.Edge N P → ℝ) : PreparedInput N P :=
  let es := prepareEdges N P a beta J (InputIndices.edges N P)
  let f := prepareField N h
  let l := add (literal f.logBase) (sumList (es.entries.map (fun e => literal e.2.logCosh)))
  ⟨es.entries, es.cache, f, l.value, InputIndices.generationWork N P +
    es.operations + f.operations + l.operations + 2 * es.entries.length⟩

@[simp] theorem prepareInput_logPrefactor {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Model.Edge N P → ℝ) :
    (prepareInput N P a beta h J).logPrefactor = logBase N P a beta h J := by
  simp only [prepareInput, add, literal, sumList_value, prepareField_logBase,
    prepareEdges_entries, List.map_map, Function.comp_def, prepareEdge_logCosh hN,
    InputIndices.edges_sum, logBase, Model.coefficient]

@[simp] theorem prepareInput_operations (N : ℕ) (P : Finset ℕ)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Model.Edge N P → ℝ) :
    (prepareInput N P a beta h J).operations = InputIndices.generationWork N P +
      23 * Fintype.card (Model.Edge N P) + 15 := by
  simp only [prepareInput, add, literal, prepareEdges_operations,
    prepareField_operations, sumList_operations, prepareEdges_entries,
    List.map_map, Function.comp_def, List.length_map, InputIndices.edges_length,
    List.map_const', List.sum_replicate, smul_zero, add_zero, zero_add]
  omega

def cachedWeight {N : ℕ} {P : Finset ℕ} (input : PreparedInput N P) (e : Model.Edge N P) : ℝ :=
  (input.cache e).weight

def cachedFieldWeight {N : ℕ} {P : Finset ℕ} (input : PreparedInput N P) (b : Bool) : ℝ :=
  if b then input.field.minusWeight else input.field.plusWeight

@[simp] theorem cachedWeight_value {N : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Model.Edge N P → ℝ) (e : Model.Edge N P) :
    cachedWeight (prepareInput N P a beta h J) e = Real.tanh (Model.coefficient N P a beta J e) := by
  change ((prepareEdges N P a beta J (InputIndices.edges N P)).cache e).weight = _
  rw [prepareEdges_cache _ _ _ _ _ _ _ (InputIndices.edges_mem N P e)]
  exact prepareEdge_weight hN _ _ _ _

@[simp] theorem cachedFieldWeight_value (N : ℕ) (P : Finset ℕ)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Model.Edge N P → ℝ) (b : Bool) :
    cachedFieldWeight (prepareInput N P a beta h J) b = FieldExpansion.spinWeight h b :=
  prepareField_weight N h b

/-- Input preparation, including physical index generation, is polynomial in N
for the fixed finite active-order set. -/
theorem prepareInput_polynomial {N Pmax : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p ≤ Pmax) (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Model.Edge N P → ℝ) :
    (prepareInput N P a beta h J).operations ≤
      48 * (P.card + 1) * (N + 1) ^ (Pmax + 2) := by
  have hg := InputIndices.generationWork_le P hPN
  rw [← InputIndices.card_edges_eq_sum_choose] at hg
  have hc := InputIndices.card_edges_le hN P hP
  have hc' : Fintype.card (Model.Edge N P) ≤ P.card * (N + 1) ^ Pmax :=
    hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hm : 1 ≤ (N + 1) ^ 2 := by nlinarith
  have hx : 1 ≤ (N + 1) ^ Pmax := Nat.one_le_pow _ _ (by omega)
  have hn : N + 15 ≤ 16 * (N + 1) ^ 2 := by nlinarith
  rw [prepareInput_operations, pow_add]
  calc
    _ ≤ N + 9 * (N + 1) ^ 2 * Fintype.card (Model.Edge N P) +
        23 * Fintype.card (Model.Edge N P) + 15 := by omega
    _ ≤ 32 * (N + 1) ^ 2 * Fintype.card (Model.Edge N P) + 16 * (N + 1) ^ 2 := by
      have hh := Nat.mul_le_mul_right (23 * Fintype.card (Model.Edge N P)) hm
      nlinarith
    _ ≤ 32 * (N + 1) ^ 2 * (P.card * (N + 1) ^ Pmax) +
        16 * (N + 1) ^ 2 * (N + 1) ^ Pmax :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hc')
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (16 * (N + 1) ^ 2) hx)
    _ ≤ _ := by nlinarith

structure Budget where
  z : ℝ
  u : ℝ
  operations : ℕ

/-- Literal real-operation evaluation of the two budgets in Algorithm 1. -/
def prepareBudget (C delta epsilon s : ℝ) : Budget :=
  let z := exponential (divide (logarithm (divide (literal delta)
    (mul (literal 2) (literal C)))) (literal s))
  let u := divide (mul (mul (literal delta) (mul (literal epsilon) (literal epsilon)))
    (mul (literal z.value) (literal z.value))) (literal 8)
  ⟨z.value, u.value, z.operations + u.operations⟩

@[simp] theorem prepareBudget_z {C delta epsilon s : ℝ} (hC : 0 < C) (hd : 0 < delta) :
    (prepareBudget C delta epsilon s).z = SpinGlass.accuracyThreshold C delta s := by
  rw [SpinGlass.accuracyThreshold, Real.rpow_def_of_pos
    (show 0 < delta / (2 * C) from div_pos hd (by positivity))]
  simp only [prepareBudget, exponential, divide, logarithm, literal, mul]
  congr 1
  ring

@[simp] theorem prepareBudget_u {C delta epsilon s : ℝ} (hC : 0 < C) (hd : 0 < delta) :
    (prepareBudget C delta epsilon s).u = SpinGlass.accuracyMSEBudget C delta epsilon s := by
  change delta * (epsilon * epsilon) *
    ((prepareBudget C delta epsilon s).z * (prepareBudget C delta epsilon s).z) / 8 = _
  rw [prepareBudget_z hC hd]
  simp only [SpinGlass.accuracyMSEBudget, pow_two]

@[simp] theorem prepareBudget_operations (C delta epsilon s : ℝ) :
    (prepareBudget C delta epsilon s).operations = 10 := rfl

end Manuscript.InputPreparation
