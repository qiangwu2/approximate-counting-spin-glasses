import Manuscript.SKChargedTrialExecution
import Manuscript.SKCandidateExecution
import Manuscript.SKGhostAggregation

/-! Counted ghost evaluator, repeated averaging, and output-sensitive candidate
schedule for Algorithm 3. The field mean and original edge weights are inputs
already saved in the prepared array. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKGeneratedExecution
open SpinGlass SpinGlass.ArithmeticEvaluation
open SKActualEvaluator SKGhostAdmissible SKChargedPrimitiveCounts SKCandidateExecution
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Prepared edge-array access; the ghost entry is the cached field mean. -/
def augmentedWeight (mean : ℝ) (w : Finset V → ℝ) (e : Finset (Option V)) : ℝ :=
  if none ∈ e then mean else w (SKAugmentFinset.lowerEdge e)

def trial (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (mean : ℝ) (w : Finset V → ℝ) : Computation :=
  SKChargedTrialExecution.totalTrial (Fintype.card V+1)
    (endpointCharge (distinguished A)) (branch (distinguished A)) Subtype.val
    (outsideColor A χ) (augmentedWeight mean w) L (accepted A)

@[simp] theorem trial_value (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (h : ℝ) (w : Finset V → ℝ) :
    (trial L A χ (Real.tanh h) w).value =
      ∑ m ∈ Finset.range (2*L+1), (ColoringProbability.probability (2*L) m)⁻¹ *
        SKGhostCoefficient.byOutsideSize A χ L m h w := by
  simp only [trial,SKChargedTrialExecution.totalTrial_value,SKChargedTrialExecution.trial_value]
  rfl

theorem trial_operations (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (mean : ℝ) (w : Finset V → ℝ) :
    (trial L A χ mean w).operations ≤
      512*(Fintype.card V+2*L+2)^6*4^(2*L)*36^(A.card+1) := by
  have hb : (distinguished A).card ≤ Fintype.card V+1 := by
    rw [distinguished_card]
    exact Nat.add_le_add_right (Finset.card_le_univ A) 1
  have hw : Fintype.card (Outside (distinguished A)) ≤ Fintype.card V+1 := by
    simpa only [Fintype.card_option] using Fintype.card_subtype_le (fun v => v ∉ distinguished A)
  have ht := SKChargedTrialExecution.totalTrial_operations_le hb hw
    (endpointCharge (distinguished A)) (branch (distinguished A)) Subtype.val
    (outsideColor A χ) (augmentedWeight mean w) L (accepted A)
  simpa only [trial,distinguished_card,show Fintype.card V+1+2*L+1=Fintype.card V+2*L+2 by omega] using ht

/-- The trial outputs are saved and averaged once. -/
def average (L R : ℕ) (A : Finset V) (χ : Fin R → V → Fin (2*L))
    (mean : ℝ) (w : Finset V → ℝ) : Computation :=
  let result := InputPreparation.divide
    (sumFinset Finset.univ (fun r => trial L A (χ r) mean w)) (literal R)
  ⟨result.value,result.operations+4*R+1⟩

@[simp] theorem average_value (L R : ℕ) (A : Finset V) (χ : Fin R → V → Fin (2*L))
    (h : ℝ) (w : Finset V → ℝ) :
    (average L R A χ (Real.tanh h) w).value = (R : ℝ)⁻¹ *
      ∑ r : Fin R, ∑ m ∈ Finset.range (2*L+1), (ColoringProbability.probability (2*L) m)⁻¹ *
        SKGhostCoefficient.byOutsideSize A (χ r) L m h w := by
  simp [average,InputPreparation.divide,literal,div_eq_mul_inv,mul_comm]

def estimator (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (mean : ℝ) (w : Finset V → ℝ) : Computation :=
  let result := sumList ((candidateList V D).map (fun A => average L R A (χ A) mean w))
  ⟨result.value,result.operations+candidateGenerationWork (Fintype.card V) D+
    SKChargedControlExecution.visitControl (20*(Fintype.card V+2*L+2)^2) (candidateList V D)⟩

@[simp] theorem estimator_value (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (h : ℝ) (w : Finset V → ℝ) :
    (estimator D L R χ (Real.tanh h) w).value = SKGhostCoefficient.algorithm D L R χ h w := by
  simp only [estimator,sumList_value,List.map_map,Function.comp_def,average_value,
    candidateList_sum,sum_candidates,SKGhostCoefficient.algorithm]

/-- All arithmetic, finite index/control comparisons and random draws in the
actual generated schedule have a fixed polynomial exponent. -/
theorem estimator_operations (D L R : ℕ) (hR : 0 < R)
    (χ : SKColorEstimator.Colors V L R) (mean : ℝ) (w : Finset V → ℝ) :
    (estimator D L R χ mean w).operations ≤
      4096*R*(Fintype.card V+2*L+2)^6*16^L*
        (∑ b ∈ Finset.range (D+1), (Fintype.card V).choose b*36^(b+1)) := by
  let M := Fintype.card V+2*L+2
  let P := M^6*4^(2*L)
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hP : 1 ≤ P := Nat.succ_le_of_lt (by dsimp [P]; positivity)
  have hM2 : M^2 ≤ P := by
    exact (Nat.pow_le_pow_right hM (by omega : 2≤6)).trans
      (Nat.le_mul_of_pos_right _ (by positivity))
  have hlocal (A : Finset V) : (average L R A (χ A) mean w).operations+1+40*M^2+2 ≤
      4096*R*P*36^(A.card+1) := by
    have ht : (∑ r : Fin R, (trial L A (χ A r) mean w).operations) ≤
        R*(512*P*36^(A.card+1)) := by
      calc
        _ ≤ ∑ _r : Fin R,512*P*36^(A.card+1) :=
          Finset.sum_le_sum (fun r _ => by simpa only [P,M,Nat.mul_assoc] using trial_operations L A (χ A r) mean w)
        _ = _ := by simp
    have hp : 1≤36^(A.card+1) := Nat.succ_le_of_lt (by positivity)
    have hr : R ≤ R*P*36^(A.card+1) :=
      (Nat.le_mul_of_pos_right _ (by positivity : 0<P)).trans (Nat.le_mul_of_pos_right _ (by positivity))
    have hm : M^2 ≤ R*P*36^(A.card+1) :=
      (hM2.trans (Nat.le_mul_of_pos_left _ hR)).trans (Nat.le_mul_of_pos_right _ (by positivity))
    simp only [average,InputPreparation.divide,literal,sumFinset_operations,Finset.card_univ,Fintype.card_fin]
    nlinarith
  have hc : 1 ≤ (candidates V D).card := Finset.card_pos.mpr ⟨∅,by simp⟩
  have hg := candidateGenerationWork_le (V := V) D (2*L+1)
  have hsum := Finset.sum_le_sum (s := candidates V D) (fun A _ => hlocal A)
  have hs : (∑ A ∈ candidates V D,4096*R*P*36^(A.card+1)) =
      4096*R*P*∑ b∈Finset.range (D+1),(Fintype.card V).choose b*36^(b+1) := by
    rw [← Finset.mul_sum]
    congr 1
    exact sum_candidates_card D (fun b => 36^(b+1))
  rw [hs] at hsum
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at hsum
  have hlist : (candidateList V D).length = (candidates V D).card := by
    simpa using candidateList_sum (V := V) D (fun _ => (1 : ℕ))
  simp only [SKChargedControlExecution.visitControl_eq,Finset.length_toList] at hg
  change candidateGenerationWork (Fintype.card V) D ≤ 1+(candidates V D).card*(20*M^2) at hg
  simp only [estimator,sumList_operations,List.map_map,Function.comp_def,List.length_map,
    candidateList_sum,SKChargedControlExecution.visitControl_eq,hlist]
  have h4 : (4 : ℕ)^(2*L)=16^L := by rw [pow_mul]; norm_num
  change _ ≤ 4096*R*M^6*16^L*_
  have he : 4096*R*P = 4096*R*M^6*16^L := by dsimp [P]; rw [h4]; ring
  rw [he] at hsum
  dsimp [M] at *
  nlinarith

end Manuscript.SKGeneratedExecution
