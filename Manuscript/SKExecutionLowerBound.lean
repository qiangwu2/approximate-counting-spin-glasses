import Manuscript.SKChargedTrialExecution
import Manuscript.SKGeneratedExecution

noncomputable section
namespace Manuscript.SKExecutionLowerBound
open SpinGlass

theorem self_le_power (n : ℕ) : n+1≤2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ];omega

theorem size_le_registers (b K : ℕ) :
    K+1≤SKOperationCount.registers b K ∧
    b+1≤SKOperationCount.registers b K ∧
    2^K≤SKOperationCount.registers b K ∧ 6^b≤SKOperationCount.registers b K := by
  have hpow : 2^b≤6^b := Nat.pow_le_pow_left (by decide) b
  have hb := (self_le_power b).trans hpow
  have hk : K+1≤(K+1)*2^K := Nat.le_mul_of_pos_right _ (by positivity)
  have hk' : (K+1)*2^K≤(K+1)*2^K*6^b := Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : 2^K≤(K+1)*2^K := Nat.le_mul_of_pos_left _ (by omega)
  have h6 : 6^b≤(K+1)*2^K*6^b := Nat.le_mul_of_pos_left _ (by positivity)
  unfold SKOperationCount.registers
  exact ⟨hk.trans hk',hb.trans h6,h2.trans hk',h6⟩

theorem registers_le_trial {V W : Type*} [Fintype W] [DecidableEq V] [DecidableEq W]
    {b K : ℕ} (N : ℕ) (q : Fin b→ℕ) (branch : Fin b→V) (outside : W→V)
    (χ : W→Fin K) (f : Finset V→ℝ) (L : ℕ)
    (accepted : Finset (Fin b→CappedDegree)) :
    SKOperationCount.registers b K≤
      (SKChargedTrialExecution.totalTrial N q branch outside χ f L accepted).operations := by
  simp only [SKChargedTrialExecution.totalTrial,SKChargedAlgebraExecution.expControl_eq]
  omega

theorem one_le_trial {V W : Type*} [Fintype W] [DecidableEq V] [DecidableEq W]
    {b K : ℕ} (N : ℕ) (q : Fin b→ℕ) (branch : Fin b→V) (outside : W→V)
    (χ : W→Fin K) (f : Finset V→ℝ) (L : ℕ)
    (accepted : Finset (Fin b→CappedDegree)) :
    1≤(SKChargedTrialExecution.totalTrial N q branch outside χ f L accepted).operations :=
  (Nat.succ_le_of_lt (by unfold SKOperationCount.registers;positivity) :
    1≤SKOperationCount.registers b K).trans
    (registers_le_trial N q branch outside χ f L accepted)

theorem generated_registers {V : Type*} [Fintype V] [DecidableEq V]
    (L : ℕ) (A : Finset V) (χ : V→Fin (2*L)) (mean : ℝ) (w : Finset V→ℝ) :
    SKOperationCount.registers (A.card+1) (2*L)≤
      (SKGeneratedExecution.trial L A χ mean w).operations := by
  simpa only [SKGeneratedExecution.trial,SKGhostAdmissible.distinguished_card] using
    registers_le_trial (Fintype.card V+1)
      (SKChargedPrimitiveCounts.endpointCharge (SKGhostAdmissible.distinguished A))
      (SKActualEvaluator.branch (SKGhostAdmissible.distinguished A)) Subtype.val
      (SKGhostAdmissible.outsideColor A χ) (SKGeneratedExecution.augmentedWeight mean w)
      L (SKGhostAdmissible.accepted A)

end Manuscript.SKExecutionLowerBound
