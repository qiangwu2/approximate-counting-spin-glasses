import Manuscript.SKChargedControlExecution

/-! One fully counted colorful trial: cached primitives, charged dense algebra,
and extracted accepted states with computed color corrections. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKChargedTrialExecution
open SpinGlass SpinGlass.ArithmeticEvaluation SpinGlass.SKCountedExecution
open Manuscript.SKChargedExtractionExecution
variable {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]

def directList {b K : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (f : Finset V → ℝ) : List (SKCoefficient.Coefficients b K) :=
  (SKChargedExecution.directPairs b).toList.map
    (fun p => (SKChargedExecution.direct endpointCharge branch f p.1 p.2).coeff)

theorem directList_length_le {b K : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (f : Finset V → ℝ) : (directList (K := K) endpointCharge branch f).length ≤ b^2 := by
  simpa only [directList, List.length_map, Finset.length_toList, SKChargedExecution.directPairs, SKFastEvaluator.directPairs] using
    SKOperationCount.directPairs_card_le b

def trial {b K : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (L : ℕ) (accepted : Finset (Fin b → CappedDegree)) : Computation :=
  let prim := SKChargedPrimitiveExecution.primitives endpointCharge branch outside χ f
  let alg := SKChargedAlgebraExecution.evaluator prim.value (directList endpointCharge branch f)
  let out := extract alg.value L accepted
  ⟨out.value, prim.operations + alg.operations + out.operations⟩

@[simp] theorem trial_value {b K : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (L : ℕ) (accepted : Finset (Fin b → CappedDegree)) :
    (trial endpointCharge branch outside χ f L accepted).value =
      ∑ m ∈ Finset.range (K+1), (ColoringProbability.probability K m)⁻¹ *
        SKChargedExecution.byOutsideSize endpointCharge branch outside χ f L m accepted := by
  simp only [trial, extract_value, SKChargedAlgebraExecution.evaluator_value,
    SKChargedPrimitiveExecution.primitives_value, SKChargedExecution.byOutsideSize,
    SKChargedExecution.evaluate, directList, SKDenseExecution.evaluator_correct]

/-- Actual arithmetic, without a primitive-cost or multiplication-cost premise. -/
theorem trial_operations_le {b K N : ℕ} (hb : b ≤ N) (hw : Fintype.card W ≤ N)
    (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (L : ℕ) (accepted : Finset (Fin b → CappedDegree)) :
    (trial endpointCharge branch outside χ f L accepted).operations ≤
      64 * (N+K+1)^4 * 4^K * 36^b := by
  let prim := SKChargedPrimitiveExecution.primitives endpointCharge branch outside χ f
  let es := directList (K := K) endpointCharge branch f
  have hp := SKChargedPrimitiveExecution.primitives_operations_le endpointCharge branch outside χ f
  have ha := SKChargedAlgebraExecution.evaluator_operations_le prim.value es
  have he := extract_operations_le (SKChargedAlgebraExecution.evaluator prim.value es).value L accepted
  have hd : es.length ≤ b^2 := directList_length_le endpointCharge branch f
  have hprofile : (trial endpointCharge branch outside χ f L accepted).operations ≤
      SKOperationCount.trialWork N b K + (4*K+1)*SKOperationCount.registers b K := by
    have hp' : prim.operations ≤ SKOperationCount.tableWork N b K +
        SKOperationCount.closureWork N b K := by
      apply hp.trans
      unfold SKOperationCount.tableWork SKOperationCount.closureWork
      gcongr
    have ha' := ha.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_left hd K))
    change prim.operations + (SKChargedAlgebraExecution.evaluator prim.value es).operations +
      (extract (SKChargedAlgebraExecution.evaluator prim.value es).value L accepted).operations ≤ _
    unfold SKOperationCount.trialWork SKOperationCount.algebraWork
      SKChargedAlgebraExecution.iterationWork at *
    nlinarith
  let M := N+K+1
  let T := 4^K*36^b
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hK : K ≤ M := by dsimp [M]; omega
  have hK1 : K+1 ≤ M := by dsimp [M]; omega
  have hreg2 : SKOperationCount.registers b K ^ 2 ≤ M^2*T := by
    rw [SKOperationCount.registers_sq]
    dsimp [T]
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (36^b) (Nat.mul_le_mul_right (4^K) (Nat.pow_le_pow_left hK1 2))
  have hregpos : 1 ≤ SKOperationCount.registers b K :=
    Nat.succ_le_of_lt (by unfold SKOperationCount.registers; positivity)
  have hreg : SKOperationCount.registers b K ≤ M^2*T :=
    (by nlinarith : SKOperationCount.registers b K ≤ SKOperationCount.registers b K ^ 2).trans hreg2
  have hextra : (4*K+1)*SKOperationCount.registers b K ≤ 5*M^4*T := by
    calc
      _ ≤ (5*M)*(M^2*T) := by gcongr; omega
      _ = 5*M^3*T := by ring
      _ ≤ _ := by gcongr <;> norm_num
  have hmain := SKOperationCount.trialWork_bound N b K hb
  change _ ≤ 64*M^4*4^K*36^b
  have hgoal : 64*M^4*4^K*36^b = 64*M^4*T := by dsimp [T]; ring
  rw [hgoal]
  have hmain' : SKOperationCount.trialWork N b K ≤ 32*M^4*T := by
    simpa only [M, T, Nat.mul_assoc] using hmain
  nlinarith

/-- Structural schedules include all color-bit scans, table indices, direct
factors, accepted-state tests, and one draw per outside vertex. -/
def totalTrial {b K : ℕ} (N : ℕ) (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (L : ℕ) (accepted : Finset (Fin b → CappedDegree)) : Computation :=
  let result := trial endpointCharge branch outside χ f L accepted
  ⟨result.value, result.operations + SKChargedControlExecution.outerTrialControl (W := W) N b K +
    SKChargedAlgebraExecution.expControl b K K +
    SKChargedAlgebraExecution.directControl (directList (K := K) endpointCharge branch f) +
    SKChargedControlExecution.acceptanceControl b K accepted⟩

@[simp] theorem totalTrial_value {b K : ℕ} (N : ℕ) (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (L : ℕ) (accepted : Finset (Fin b → CappedDegree)) :
    (totalTrial N endpointCharge branch outside χ f L accepted).value =
      (trial endpointCharge branch outside χ f L accepted).value := rfl

theorem totalTrial_operations_le {b K N : ℕ} (hb : b ≤ N) (hw : Fintype.card W ≤ N)
    (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (L : ℕ) (accepted : Finset (Fin b → CappedDegree)) :
    (totalTrial N endpointCharge branch outside χ f L accepted).operations ≤
      512 * (N+K+1)^6 * 4^K * 36^b := by
  let prim := SKChargedPrimitiveExecution.primitives endpointCharge branch outside χ f
  let es := directList (K := K) endpointCharge branch f
  have hac := SKChargedControlExecution.acceptanceControl_bound (K := K) hb accepted
  have ho := SKChargedControlExecution.outerTrialControl_bound (W := W) hb hw (L := K)
  have ha := SKChargedAlgebraExecution.totalEvaluatorWork_bound hb prim.value es
    (directList_length_le endpointCharge branch f)
  have ht := trial_operations_le hb hw endpointCharge branch outside χ f L accepted
  have hpow : (N+K+1)^4 ≤ (N+K+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have ht' : (trial endpointCharge branch outside χ f L accepted).operations ≤
      64*(N+K+1)^6*4^K*36^b := by apply ht.trans; gcongr
  change (trial endpointCharge branch outside χ f L accepted).operations + _ + _ +
    SKChargedAlgebraExecution.directControl es + SKChargedControlExecution.acceptanceControl b K accepted ≤ _
  unfold SKChargedAlgebraExecution.totalEvaluatorWork at ha
  nlinarith

end Manuscript.SKChargedTrialExecution
