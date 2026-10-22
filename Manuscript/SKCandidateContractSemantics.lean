import Manuscript.SKCandidateContract

noncomputable section
open scoped BigOperators
namespace Manuscript.SKCandidateContract
open SpinGlass RestrictedMachine

@[simp] theorem value_encoded {N L R : ℕ} (χ : SKColorEstimator.Colors (Fin N) L R)
    (mean : ℝ) (w : Finset (Fin N)→ℝ) (A : Finset (Fin N)) (r : Fin R) :
    value χ mean w (RestrictedMaskBridge.encode A) r.val=
      (SKGeneratedExecution.trial L A (χ A r) mean w).value := by
  simp [value,decodeMask_encode,r.isLt]

@[simp] theorem bound_encoded {N L R : ℕ} (χ : SKColorEstimator.Colors (Fin N) L R)
    (mean : ℝ) (w : Finset (Fin N)→ℝ) (A : Finset (Fin N)) :
    bound χ mean w (RestrictedMaskBridge.encode A)=
      7000*(N+(SKGeneratedExecution.average L R A (χ A) mean w).operations+1)^5 := by
  simp [bound,decodeMask_encode]

theorem sum_eq_range (f : ℕ→ℕ→ℝ) (mask n j : ℕ) :
    RestrictedSKTrials.sum f mask n j=∑k∈Finset.range n,f mask (j+k) := by
  induction n generalizing j with
  | zero => simp [RestrictedSKTrials.sum]
  | succ n ih =>
    rw [RestrictedSKTrials.sum,ih,Finset.sum_range_succ']
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_comm]

theorem average_encoded {N L R : ℕ} (χ : SKColorEstimator.Colors (Fin N) L R)
    (mean : ℝ) (w : Finset (Fin N)→ℝ) (A : Finset (Fin N)) :
    RestrictedSKTrials.sum (value χ mean w) (RestrictedMaskBridge.encode A) R 0/(R:ℝ)=
      (SKGeneratedExecution.average L R A (χ A) mean w).value := by
  rw [sum_eq_range]
  simp only [Nat.zero_add,←Fin.sum_univ_eq_sum_range,value_encoded]
  simp [SKGeneratedExecution.average,InputPreparation.divide,ArithmeticEvaluation.literal]
end Manuscript.SKCandidateContract
