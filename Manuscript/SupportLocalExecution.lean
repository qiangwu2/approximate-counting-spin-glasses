import Manuscript.SupportIndices
import SpinGlass.ArithmeticEvaluation

/-! A counted, biased local-spin evaluator with a concrete cube generator. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SupportLocalExecution
open SpinGlass.ArithmeticEvaluation Manuscript.SupportEvaluation
open Manuscript.FieldExpansion Manuscript.SupportIndices
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The spin-coordinate order is fixed once for a local support. -/
def localAssignments (U : Finset V) : List (U → Bool) :=
  (cubeAssignments U.card).map (fun σ v => σ ((U.equivFin) v))

theorem localAssignments_sum {R : Type*} [AddCommMonoid R]
    (U : Finset V) (f : (U → Bool) → R) :
    ((localAssignments U).map f).sum = ∑ σ, f σ := by
  rw [localAssignments,List.map_map,cubeAssignments_sum]
  exact Fintype.sum_equiv (Equiv.arrowCongr (U.equivFin).symm (Equiv.refl Bool))
    _ _ (fun σ => rfl)

@[simp] theorem localAssignments_length (U : Finset V) :
    (localAssignments U).length = 2^U.card := by
  simp [localAssignments,cubeAssignments]

/-- An actual short-circuit subset test selects the induced edges once. -/
def selectEdges (incidence : E → Finset V) (U : Finset V) : List E → Generated E
  | [] => ⟨[],0⟩
  | e::es =>
    let test := finsetSubset (incidence e) U
    let tail := selectEdges incidence U es
    ⟨if test.value then e::tail.values else tail.values,
      test.comparisons+tail.work+1⟩

@[simp] theorem selectEdges_values (incidence : E → Finset V) (U : Finset V)
    (es : List E) :
    (selectEdges incidence U es).values = es.filter (fun e => decide (incidence e ⊆ U)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [selectEdges,List.filter_cons]
    by_cases he : incidence e ⊆ U
    · have ht := (finsetSubset_value _ _).mpr he
      simp [ht,he,ih]
    · have ht : (finsetSubset (incidence e) U).value = false := by
        cases hh : (finsetSubset (incidence e) U).value
        · rfl
        · exact False.elim (he ((finsetSubset_value _ _).mp hh))
      simp [ht,he,ih]

theorem selectEdges_work (incidence : E → Finset V) (U : Finset V) (es : List E) :
    (selectEdges incidence U es).work ≤
      es.length * (Fintype.card V * U.card+1) := by
  induction es with
  | nil => simp [selectEdges]
  | cons e es ih =>
    have ht := finsetSubset_comparisons (incidence e) U
    have hc := Finset.card_le_univ (incidence e)
    have hm := Nat.mul_le_mul_right U.card hc
    simp only [selectEdges,List.length_cons]
    nlinarith

/-- The local edge character multiplies its selected spin coordinates. -/
def character (incidence : E → Finset V) (U : Finset V) (σ : U → Bool) (e : E) : Computation :=
  productFinset (localIncidence incidence U e)
    (fun v => literal (SpinGlass.Expansion.spinSign (σ v)))

@[simp] theorem character_value (incidence : E → Finset V) (U : Finset V)
    (σ : U → Bool) (e : E) :
    (character incidence U σ e).value =
      SpinGlass.Expansion.edgeCharacter (localIncidence incidence U) σ e := by
  simp [character,literal,SpinGlass.Expansion.edgeCharacter]

@[simp] theorem character_operations (incidence : E → Finset V) (U : Finset V)
    (σ : U → Bool) (e : E) :
    (character incidence U σ e).operations = (localIncidence incidence U e).card := by
  simp [character,literal]

def edgeFactor (incidence : E → Finset V) (w : E → ℝ)
    (U : Finset V) (σ : U → Bool) (e : E) : Computation :=
  add (literal 1) (mul (literal (w e)) (character incidence U σ e))

/-- The two normalized single-spin weights are cached inputs. -/
def spinTerm (incidence : E → Finset V) (es : List E) (b : Bool → ℝ) (w : E → ℝ)
    (U : Finset V) (σ : U → Bool) : Computation :=
  mul (productFinset Finset.univ (fun v : U => literal (b (σ v))))
    (productList (es.map (edgeFactor incidence w U σ)))

/-- Per assignment, write the local spins to the ambient array, read each
spin and its cached field weight, and read each interaction weight and spin.
The counts follow the same finite list loops as the arithmetic evaluator. -/
def indexedSpinTerm (incidence : E → Finset V) (es : List E) (b : Bool → ℝ) (w : E → ℝ)
    (U : Finset V) (σ : U → Bool) : Computation :=
  let term := spinTerm incidence es b w U σ
  ⟨term.value,term.operations+3*U.card+
    (es.map (fun e => (localIncidence incidence U e).card)).sum+es.length⟩

/-- Each local assignment is generated and evaluated exactly once. Selection
of induced edges is saved and reused by all assignments. -/
def localEvaluator (incidence : E → Finset V) (edges : Finset E)
    (b : Bool → ℝ) (w : E → ℝ) (U : Finset V) : Computation :=
  let es := selectEdges incidence U edges.toList
  let result := sumList ((localAssignments U).map (indexedSpinTerm incidence es.values b w U))
  ⟨result.value, result.operations + es.work + (cubeExecution U.card).work + Fintype.card V⟩

@[simp] theorem localEvaluator_value (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (U : Finset V) :
    (localEvaluator incidence edges (spinWeight h) w U).value = localG incidence edges h w U := by
  simp only [localEvaluator,sumList_value,List.map_map,Function.comp_def]
  rw [localAssignments_sum]
  unfold localG fieldMean
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [indexedSpinTerm,spinTerm,mul,productFinset_value,literal,productList_value,
    List.map_map,Function.comp_def,edgeFactor,add,character_value,selectEdges_values]
  congr 1
  rw [← List.prod_toFinset _ (edges.nodup_toList.filter _)]
  simp

/-- Exact arithmetic count before the already charged index generators. -/
theorem spinTerm_operations (incidence : E → Finset V) (es : List E)
    (b : Bool → ℝ) (w : E → ℝ) (U : Finset V) (σ : U → Bool) :
    (spinTerm incidence es b w U σ).operations =
      U.card + (es.map (fun e => (localIncidence incidence U e).card+2)).sum + es.length+1 := by
  simp [spinTerm,mul,literal,edgeFactor,add,List.map_map,Function.comp_def]
  ring

theorem spinTerm_operations_le (incidence : E → Finset V) (es : List E)
    (b : Bool → ℝ) (w : E → ℝ) (U : Finset V) (σ : U → Bool) :
    (spinTerm incidence es b w U σ).operations ≤
      U.card + es.length*(U.card+3)+1 := by
  rw [spinTerm_operations]
  have hs : (es.map (fun e => (localIncidence incidence U e).card+2)).sum ≤
      es.length*(U.card+2) := by
    induction es with
    | nil => simp
    | cons e es ih =>
      have hc : (localIncidence incidence U e).card ≤ U.card := by
        simpa only [Fintype.card_coe] using Finset.card_le_univ (localIncidence incidence U e)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  nlinarith

theorem indexedSpinTerm_operations_le (incidence : E → Finset V) (es : List E)
    (b : Bool → ℝ) (w : E → ℝ) (U : Finset V) (σ : U → Bool) :
    (indexedSpinTerm incidence es b w U σ).operations ≤
      4*U.card + es.length*(2*U.card+4)+1 := by
  have hs : (es.map (fun e => (localIncidence incidence U e).card)).sum ≤ es.length*U.card := by
    induction es with
    | nil => simp
    | cons e es ih =>
      have hc : (localIncidence incidence U e).card ≤ U.card := by
        simpa only [Fintype.card_coe] using Finset.card_le_univ (localIncidence incidence U e)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hh := spinTerm_operations_le incidence es b w U σ
  dsimp only [indexedSpinTerm]
  nlinarith

/-- A uniform bound includes the induced-edge scan and concrete local cube
construction in addition to arithmetic. -/
theorem localEvaluator_operations_le (incidence : E → Finset V) (edges : Finset E)
    (b : Bool → ℝ) (w : E → ℝ) (U : Finset V) :
    (localEvaluator incidence edges b w U).operations ≤
      2^U.card * (4*U.card + edges.card*(2*U.card+4)+2) +
        edges.card*(Fintype.card V*U.card+1)+4*(U.card+1)*2^U.card+Fintype.card V := by
  have hc := cubeExecution_work U.card
  have he := selectEdges_work incidence U edges.toList
  have hel : (selectEdges incidence U edges.toList).values.length ≤ edges.card := by
    rw [selectEdges_values]
    simpa only [Finset.length_toList] using List.length_filter_le (fun e => decide (incidence e ⊆ U)) edges.toList
  have hs : (((localAssignments U).map (indexedSpinTerm incidence
      (selectEdges incidence U edges.toList).values b w U)).map Computation.operations).sum ≤
      (localAssignments U).length*(4*U.card+edges.card*(2*U.card+4)+1) := by
    rw [List.map_map]
    have hh := List.sum_le_card_nsmul ((localAssignments U).map
      (Computation.operations ∘ indexedSpinTerm incidence (selectEdges incidence U edges.toList).values b w U))
      (4*U.card+edges.card*(2*U.card+4)+1) (by
        intro x hx
        obtain ⟨σ,hσ,rfl⟩ := List.mem_map.mp hx
        have ht := indexedSpinTerm_operations_le incidence (selectEdges incidence U edges.toList).values b w U σ
        exact ht.trans (by nlinarith))
    simpa only [List.length_map, nsmul_eq_mul, Nat.cast_id] using hh
  simp only [Finset.length_toList] at he
  simp only [localAssignments_length] at hs
  simp only [localEvaluator,sumList_operations,List.length_map,localAssignments_length]
  nlinarith

end Manuscript.SupportLocalExecution
