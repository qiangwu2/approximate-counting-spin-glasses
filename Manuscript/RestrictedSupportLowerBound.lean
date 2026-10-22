import Manuscript.SupportExecution

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSupportLowerBound
open SpinGlass.ArithmeticEvaluation SupportLocalExecution
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

theorem local_cube (incidence : E→Finset V) (edges : Finset E) (b : Bool→ℝ)
    (w : E→ℝ) (U : Finset V) :
    2^U.card≤(localEvaluator incidence edges b w U).operations := by
  simp only [SupportLocalExecution.localEvaluator,sumList_operations,List.length_map,localAssignments_length]
  omega

theorem layer_cube (incidence : E→Finset V) (edges : Finset E) (b : Bool→ℝ)
    (w : E→ℝ) (k l : ℕ) :
    (Fintype.card V).choose l*2^l≤(SupportExecution.layer incidence edges b w k l).operations := by
  have hs : (Fintype.card V).choose l*2^l≤
      ∑U∈(Finset.univ : Finset V).powersetCard l,((localEvaluator incidence edges b w U).operations+1) := by
    calc
      _ = ∑U∈(Finset.univ : Finset V).powersetCard l,2^l := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro U hU
        have hh := local_cube incidence edges b w U
        rw [(Finset.mem_powersetCard.mp hU).2] at hh
        omega
  rw [SupportExecution.layer_operations]
  omega

theorem weighted_full (N : ℕ) : (∑l∈Finset.range (N+1),N.choose l*2^l)=3^N := by
  have hh := add_pow (2 : ℕ) 1 N
  simpa [Nat.mul_comm] using hh.symm

theorem weighted_le_operations_square (incidence : E→Finset V) (edges : Finset E)
    (b : Bool→ℝ) (w : E→ℝ) {k : ℕ} (hk : k≤Fintype.card V) :
    (∑l∈Finset.range (k+1),(Fintype.card V).choose l*2^l)≤
      ((SupportExecution.supportSum incidence edges b w k).operations+1)^2 := by
  unfold SupportExecution.supportSum
  split_ifs with hlt
  · have hh : (∑l∈Finset.range (k+1),(Fintype.card V).choose l*2^l)≤
        (SupportExecution.truncated incidence edges b w k).operations := by
      unfold SupportExecution.truncated
      rw [sumFinset_operations]
      have hs := Finset.sum_le_sum (s:=Finset.range (k+1))
        (fun l _ => layer_cube incidence edges b w k l)
      omega
    nlinarith
  · have heq : k=Fintype.card V := by omega
    rw [heq,weighted_full]
    have hh := local_cube incidence edges b w (Finset.univ : Finset V)
    simp only [Finset.card_univ] at hh
    have hp : (3 : ℕ)^Fintype.card V≤4^Fintype.card V := Nat.pow_le_pow_left (by omega) _
    have hp2 : (4 : ℕ)^Fintype.card V=(2^Fintype.card V)^2 := by
      rw [show (4 : ℕ)=2^2 by norm_num,←pow_mul,←pow_mul,Nat.mul_comm]
    rw [hp2] at hp
    exact hp.trans (Nat.pow_le_pow_left (by omega) 2)

end Manuscript.RestrictedSupportLowerBound
