import Manuscript.RestrictedSupportProgram

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSupportCost
open RestrictedLocalSum RestrictedHigherLayer RestrictedLayerSemantics RestrictedMaskBridge

def factor (d : Data) : ℕ := termCost d+300*(d.N+1)+400

theorem local_cost_bound (d : Data) (U : Finset (Fin d.N)) :
    localCost d (encode U)+24≤(termCost d+67*(2*d.N+1)+67)*2^U.card := by
  have hh := RestrictedLocalEvaluation.cost_bound (withSupport d (encode U))
  change localCost d (encode U)≤
    (termCost d+67*(2*d.N+1)+20)*2^RestrictedCubes.supportSize d.N (encode U)+23 at hh
  rw [supportSize_card] at hh
  have ht : 1≤2^U.card := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem layer_bound (d : Data) {k l : ℕ} (hl : l≤k) (hk : k≤d.N) :
    cost d k l+13≤factor d*(d.N.choose l*2^l) := by
  have hln : l≤d.N := hl.trans hk
  have hc : 1≤d.N.choose l := Nat.choose_pos hln
  have ht : 1≤2^l := Nat.one_le_pow _ _ (by omega)
  have hg := RestrictedSubsets.work_bound hln
  have hs : ((RestrictedSubsets.masks d.N l 0 1).map (fun u => localCost d u+24)).sum≤
      d.N.choose l*((termCost d+67*(2*d.N+1)+67)*2^l) := by
    rw [support_masks_sum]
    calc
      _ ≤ ∑U∈(Finset.univ : Finset (Fin d.N)).powersetCard l,
          (termCost d+67*(2*d.N+1)+67)*2^l := by
        apply Finset.sum_le_sum
        intro U hU
        have hu := (Finset.mem_powersetCard.mp hU).2
        simpa [hu] using local_cost_bound d U
      _ = _ := by simp
  have hct : 1≤d.N.choose l*2^l := Nat.mul_le_mul hc ht
  have hcg := Nat.mul_le_mul_left (63*(2*d.N+1)) (Nat.mul_le_mul_left (d.N.choose l) ht)
  have hbase := Nat.mul_le_mul_left (31*(d.N+1)+77) hct
  unfold cost factor
  nlinarith [Nat.sub_le k l]

theorem totalCost_range (d : Data) (k i m : ℕ) :
    RestrictedSupportProgram.totalCost d k i m=
      ∑j∈Finset.range m,(cost d k (i+j)+13) := by
  induction m generalizing i with
  | zero => simp [RestrictedSupportProgram.totalCost]
  | succ m ih =>
      rw [RestrictedSupportProgram.totalCost,Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [ih,add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Actual instruction count is a fixed polynomial prefactor times the
retained binomial/cube enumeration, including generated list construction. -/
theorem total_bound (d : Data) {k : ℕ} (hk : k≤d.N) :
    RestrictedSupportProgram.totalCost d k 0 (k+1)+12≤
      factor d*(∑l∈Finset.range (k+1),d.N.choose l*2^l)+12 := by
  rw [totalCost_range]
  simp only [Nat.zero_add]
  apply Nat.add_le_add_right
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  apply layer_bound d (by have := Finset.mem_range.mp hl; omega) hk

end Manuscript.RestrictedSupportCost
