import Manuscript.SKExecutionLowerBound
import Manuscript.SKFinal

noncomputable section
open scoped BigOperators
namespace Manuscript.SKGlobalLowerBound
open SpinGlass SpinGlass.ArithmeticEvaluation SKCandidateExecution
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem average_lower (L R : ℕ) (A : Finset V) (χ : Fin R→V→Fin (2*L))
    (mean : ℝ) (w : Finset V→ℝ) :
    R≤(SKGeneratedExecution.average L R A χ mean w).operations ∧
    (∑ r : Fin R,(SKGeneratedExecution.trial L A (χ r) mean w).operations)≤
      (SKGeneratedExecution.average L R A χ mean w).operations := by
  simp only [SKGeneratedExecution.average,InputPreparation.divide,literal,
    sumFinset_operations,Finset.card_univ,Fintype.card_fin]
  omega

theorem estimator_lower (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (mean : ℝ) (w : Finset V→ℝ) :
    (∑ A∈candidates V D,(SKGeneratedExecution.average L R A (χ A) mean w).operations)≤
      (SKGeneratedExecution.estimator D L R χ mean w).operations := by
  simp only [SKGeneratedExecution.estimator,sumList_operations,List.map_map,
    Function.comp_def,candidateList_sum]
  omega

theorem trials_candidates (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (mean : ℝ) (w : Finset V→ℝ) :
    R*(candidates V D).card≤(SKGeneratedExecution.estimator D L R χ mean w).operations := by
  calc
    _ = ∑ _A∈candidates V D,R := by simp [Nat.mul_comm]
    _ ≤ ∑ A∈candidates V D,(SKGeneratedExecution.average L R A (χ A) mean w).operations :=
      Finset.sum_le_sum (fun A _ => (average_lower L R A (χ A) mean w).1)
    _ ≤ _ := estimator_lower D L R χ mean w

theorem trial_le_estimator (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (mean : ℝ) (w : Finset V→ℝ) (A : Finset V) (hA : A.card≤D) (r : Fin R) :
    (SKGeneratedExecution.trial L A (χ A r) mean w).operations≤
      (SKGeneratedExecution.estimator D L R χ mean w).operations := by
  calc
    _ ≤ ∑ r : Fin R,(SKGeneratedExecution.trial L A (χ A r) mean w).operations :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    _ ≤ (SKGeneratedExecution.average L R A (χ A) mean w).operations :=
      (average_lower L R A (χ A) mean w).2
    _ ≤ ∑ A∈candidates V D,(SKGeneratedExecution.average L R A (χ A) mean w).operations :=
      Finset.single_le_sum (f:=fun A : Finset V =>
        (SKGeneratedExecution.average L R A (χ A) mean w).operations)
        (fun _ _ => Nat.zero_le _) ((mem_candidates D A).2 hA)
    _ ≤ _ := estimator_lower D L R χ mean w

theorem registers (D L R : ℕ) (hR : 0<R) (χ : SKColorEstimator.Colors V L R)
    (mean : ℝ) (w : Finset V→ℝ) (A : Finset V) (hA : A.card≤D) :
    SKOperationCount.registers (A.card+1) (2*L)≤
      (SKGeneratedExecution.estimator D L R χ mean w).operations :=
  (SKExecutionLowerBound.generated_registers L A (χ A ⟨0,hR⟩) mean w).trans
    (trial_le_estimator D L R χ mean w A hA ⟨0,hR⟩)

theorem dimensions (D L R : ℕ) (hR : 0<R) (χ : SKColorEstimator.Colors V L R)
    (mean : ℝ) (w : Finset V→ℝ) :
    2*L+1≤(SKGeneratedExecution.estimator D L R χ mean w).operations ∧
    R≤(SKGeneratedExecution.estimator D L R χ mean w).operations := by
  have hr := registers D L R hR χ mean w ∅ (by simp)
  have hd := SKExecutionLowerBound.size_le_registers (0+1) (2*L)
  have hc : 1≤(candidates V D).card := Finset.card_pos.mpr ⟨∅,by simp⟩
  refine ⟨?_,?_⟩
  · simpa using hd.1.trans hr
  · exact (Nat.le_mul_of_pos_right R (by omega)).trans (trials_candidates D L R χ mean w)

theorem candidates_card (D : ℕ) :
    (candidates V D).card=∑ j∈Finset.range (D+1),(Fintype.card V).choose j := by
  simpa using sum_candidates_card (V:=V) D (fun _ => 1)

end Manuscript.SKGlobalLowerBound
