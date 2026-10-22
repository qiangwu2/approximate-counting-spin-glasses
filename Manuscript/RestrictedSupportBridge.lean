import Manuscript.RestrictedSupportProgram
import Manuscript.SupportExecution

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSupportBridge
open RestrictedMachine RestrictedLocalSum RestrictedHigherLayer RestrictedLayerSemantics
open RestrictedMaskBridge SupportEvaluation FieldExpansion SpinGlass.Expansion

/-- Reordering raw edge records changes no local spin average. -/
theorem localG_reindex {N M : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (order : Fin M ≃ E) (incidence : E→Finset (Fin N)) (w : E→ℝ) (h : ℝ)
    (U : Finset (Fin N)) :
    localG (fun j => incidence (order j)) Finset.univ h (fun j => w (order j)) U=
      localG incidence Finset.univ h w U := by
  unfold localG
  congr 1
  funext σ
  simp only [Finset.prod_filter]
  apply Fintype.prod_equiv order
  intro j
  rfl

theorem layer_value (d : Data) {E : Type*} [Fintype E] [DecidableEq E]
    (order : Fin d.M ≃ E) (incidence : E→Finset (Fin d.N)) (w : E→ℝ) (h : ℝ)
    (hE : ∀ e : Fin d.M,d.natMemory (d.edgeBase+e.val)=encode (incidence (order e)))
    (hW : ∀ e : Fin d.M,d.realMemory (d.weightBase+2*e.val)=w (order e))
    (hp : d.plus=spinWeight h false) (hm : d.minus=spinWeight h true) (k l : ℕ) :
    RestrictedLayerSemantics.value d k l=
      (SupportExecution.layer incidence Finset.univ (spinWeight h) w k l).value := by
  unfold RestrictedLayerSemantics.value
  rw [support_masks_sum,SupportExecution.layer_value]
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro U hU
  congr 1
  change ((RestrictedCubes.masks d.N (encode U) 0 1).map (term {d with U:=encode U})).sum=_
  rw [cube_terms_eq_localG d (fun j => incidence (order j)) (fun j => w (order j)) h U hE hW hp hm,
    localG_reindex]

theorem totalValue_range (d : Data) (k i m : ℕ) :
    RestrictedSupportProgram.totalValue d k i m=
      ∑j∈Finset.range m,RestrictedLayerSemantics.value d k (i+j) := by
  induction m generalizing i with
  | zero => simp [RestrictedSupportProgram.totalValue]
  | succ m ih =>
      rw [RestrictedSupportProgram.totalValue,Finset.sum_range_succ']
      simp only [Nat.add_zero]
      rw [ih,add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem coefficient_full_zero {N l : ℕ} (hl : l<N) : coefficient N N l=0 := by
  unfold coefficient
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem full_layer {N : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (incidence : E→Finset (Fin N)) (w : E→ℝ) (h : ℝ) :
    (SupportExecution.layer incidence Finset.univ (spinWeight h) w N N).value=
      localG incidence Finset.univ h w Finset.univ := by
  rw [SupportExecution.layer_value]
  have he : (Finset.univ : Finset (Fin N)).powersetCard N={Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin N))
  simp [coefficient,he]

theorem support_value (d : Data) {E : Type*} [Fintype E] [DecidableEq E]
    (order : Fin d.M ≃ E) (incidence : E→Finset (Fin d.N)) (w : E→ℝ) (h : ℝ)
    (hE : ∀ e : Fin d.M,d.natMemory (d.edgeBase+e.val)=encode (incidence (order e)))
    (hW : ∀ e : Fin d.M,d.realMemory (d.weightBase+2*e.val)=w (order e))
    (hp : d.plus=spinWeight h false) (hm : d.minus=spinWeight h true)
    (k : ℕ) (hk : k≤d.N) :
    RestrictedSupportProgram.totalValue d k 0 (k+1)=
      (SupportExecution.supportSum incidence Finset.univ (spinWeight h) w k).value := by
  rw [totalValue_range]
  simp only [Nat.zero_add]
  simp_rw [layer_value d order incidence w h hE hW hp hm]
  unfold SupportExecution.supportSum
  split_ifs with hlt
  · simp [SupportExecution.truncated]
  · have heq : k=d.N := by simp only [Fintype.card_fin] at hlt; omega
    subst k
    rw [Finset.sum_eq_single d.N]
    · rw [full_layer,SupportLocalExecution.localEvaluator_value]
    · intro l hl hne
      rw [SupportExecution.layer_value]
      simp only [Fintype.card_fin]
      have hln : l<d.N := by have := Finset.mem_range.mp hl; omega
      simp [coefficient_full_zero hln]
    · simp

/-- This bridge handles arbitrary raw record order and both k<N and k=N. -/
theorem graph_sum_value (d : Data) {E : Type*} [Fintype E] [DecidableEq E]
    (order : Fin d.M ≃ E) (incidence : E→Finset (Fin d.N)) (w : E→ℝ) (h : ℝ)
    (hE : ∀ e : Fin d.M,d.natMemory (d.edgeBase+e.val)=encode (incidence (order e)))
    (hW : ∀ e : Fin d.M,d.realMemory (d.weightBase+2*e.val)=w (order e))
    (hp : d.plus=spinWeight h false) (hm : d.minus=spinWeight h true)
    (k : ℕ) (hk : k≤d.N) :
    RestrictedSupportProgram.totalValue d k 0 (k+1)=
      ∑ Γ∈(Finset.univ : Finset E).powerset with (support incidence Γ).card≤k,
        graphWeight incidence h w Γ := by
  rw [support_value d order incidence w h hE hW hp hm k hk,SupportExecution.supportSum_value]

end Manuscript.RestrictedSupportBridge
