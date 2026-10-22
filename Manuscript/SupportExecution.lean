import Manuscript.SupportLocalExecution
import Manuscript.SupportCoefficientExecution

/-! The collapsed SupportSum program evaluates each retained local average once. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SupportExecution
open SpinGlass.ArithmeticEvaluation Manuscript.SupportEvaluation
open Manuscript.FieldExpansion Manuscript.SupportIndices
open Manuscript.SupportLocalExecution
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

def layer (incidence : E → Finset V) (edges : Finset E) (b : Bool → ℝ)
    (w : E → ℝ) (k s : ℕ) : Computation :=
  let c := SupportCoefficientExecution.coefficient (Fintype.card V) k s
  let sets := certifiedChoices s (Finset.univ : Finset V).toList (Finset.nodup_toList _)
  let result := sumList (sets.map (fun U =>
    mul (literal c.value) (localEvaluator incidence edges b w U)))
  ⟨result.value, result.operations+c.operations+
    (chooseExecution s (Finset.univ : Finset V).toList).work+sets.length⟩

def truncated (incidence : E → Finset V) (edges : Finset E) (b : Bool → ℝ)
    (w : E → ℝ) (k : ℕ) : Computation :=
  sumFinset (Finset.range (k+1)) (layer incidence edges b w k)

/-- The full-support branch performs just the single ambient local average. -/
def supportSum (incidence : E → Finset V) (edges : Finset E) (b : Bool → ℝ)
    (w : E → ℝ) (k : ℕ) : Computation :=
  if k < Fintype.card V then truncated incidence edges b w k
  else localEvaluator incidence edges b w Finset.univ

@[simp] theorem layer_value (incidence : E → Finset V) (edges : Finset E) (h : ℝ)
    (w : E → ℝ) (k s : ℕ) :
    (layer incidence edges (spinWeight h) w k s).value =
      ∑ U ∈ (Finset.univ : Finset V).powersetCard s,
        SupportEvaluation.coefficient (Fintype.card V) k s * localG incidence edges h w U := by
  simp only [layer,sumList_value,List.map_map,Function.comp_def,mul,literal,
    SupportCoefficientExecution.coefficient_value,SupportLocalExecution.localEvaluator_value,certifiedChoices_eq]
  exact chosenFinsets_sum _ _ _

@[simp] theorem truncated_value (incidence : E → Finset V) (edges : Finset E) (h : ℝ)
    (w : E → ℝ) (k : ℕ) (hk : k < Fintype.card V) :
    (truncated incidence edges (spinWeight h) w k).value =
      ∑ Γ ∈ edges.powerset with (support incidence Γ).card ≤ k,
        graphWeight incidence h w Γ := by
  simp only [truncated,sumFinset_value,layer_value]
  rw [← collapsed_local_sum incidence edges h w k hk]
  calc
    _ = ∑ s ∈ Finset.range (k+1), ∑ U ∈ (Finset.univ : Finset V).powerset
      with U.card=s, SupportEvaluation.coefficient (Fintype.card V) k U.card *
        localG incidence edges h w U := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.powersetCard_eq_filter]
      apply Finset.sum_congr rfl
      intro U hU
      rw [(Finset.mem_filter.mp hU).2]
    _ = _ := by
      rw [Finset.sum_fiberwise_eq_sum_filter]
      simp only [Finset.mem_range, Nat.lt_succ_iff]

@[simp] theorem supportSum_value (incidence : E → Finset V) (edges : Finset E) (h : ℝ)
    (w : E → ℝ) (k : ℕ) :
    (supportSum incidence edges (spinWeight h) w k).value =
      ∑ Γ ∈ edges.powerset with (support incidence Γ).card ≤ k,
        graphWeight incidence h w Γ := by
  unfold supportSum
  split_ifs with hk
  · exact truncated_value incidence edges h w k hk
  · rw [SupportLocalExecution.localEvaluator_value,localG_univ]
    congr 1
    symm
    apply Finset.filter_true_of_mem
    intro Γ hΓ
    exact (Finset.card_le_univ _).trans (by omega)

/-- A polynomial local overhead multiplies only the local cube size. -/
def localConstant (N M : ℕ) : ℕ := 30*(M+1)*(N+1)^2

theorem local_cost (incidence : E → Finset V) (edges : Finset E)
    (b : Bool → ℝ) (w : E → ℝ) (U : Finset V) :
    (localEvaluator incidence edges b w U).operations ≤
      localConstant (Fintype.card V) edges.card * 2^U.card := by
  have h := localEvaluator_operations_le incidence edges b w U
  have hs := Finset.card_le_univ U
  have ht : 1 ≤ 2^U.card := Nat.one_le_pow _ _ (by omega)
  have hNS : Fintype.card V * U.card+1 ≤ 2*(Fintype.card V+1)^2 := by nlinarith
  have hS : 2*U.card+4 ≤ 4*(Fintype.card V+1)^2 := by nlinarith
  have hSm : U.card+1 ≤ (Fintype.card V+1)^2 := by nlinarith
  have hN : Fintype.card V ≤ (Fintype.card V+1)^2 := by nlinarith
  have hm1 := Nat.mul_le_mul_left edges.card hS
  have hm2 := Nat.mul_le_mul_left edges.card hNS
  have ht1 := Nat.mul_le_mul_right (2^U.card) hm1
  have ht2 := Nat.mul_le_mul_right (2^U.card) hSm
  have ht3 := Nat.mul_le_mul_left (2*edges.card*(Fintype.card V+1)^2) ht
  have ht4 := Nat.mul_le_mul_left ((Fintype.card V+1)^2) ht
  unfold localConstant
  nlinarith

/-- Per-layer scalar coefficients are computed once and then reused. -/
theorem layer_operations (incidence : E → Finset V) (edges : Finset E) (b : Bool → ℝ)
    (w : E → ℝ) (k s : ℕ) :
    (layer incidence edges b w k s).operations =
      (∑ U ∈ (Finset.univ : Finset V).powersetCard s,
        ((localEvaluator incidence edges b w U).operations+1)) +
      (Fintype.card V).choose s + (6*(k-s)+8) +
      chooseWork (Fintype.card V) s + (Fintype.card V).choose s := by
  simp only [layer,sumList_operations,List.map_map,Function.comp_def,mul,literal,
    Nat.zero_add,SupportCoefficientExecution.coefficient_operations,certifiedChoices_eq,
    chosenFinsets_length,List.length_map,Finset.length_toList,Finset.card_univ,
    chooseExecution_work]
  rw [chosenFinsets_sum]

/-- The complete counted layer has the binomial-times-cube work required by
Lemma 5.1; no additional ambient exponential enumeration is performed. -/
def layerConstant (N M : ℕ) : ℕ := 60*(M+1)*(N+1)^2

theorem layer_cost (incidence : E → Finset V) (edges : Finset E) (b : Bool → ℝ)
    (w : E → ℝ) {k s : ℕ} (hs : s ≤ k) (hk : k ≤ Fintype.card V) :
    (layer incidence edges b w k s).operations+1 ≤
      layerConstant (Fintype.card V) edges.card * ((Fintype.card V).choose s * 2^s) := by
  have hsn := hs.trans hk
  have hc : 1 ≤ (Fintype.card V).choose s := Nat.choose_pos hsn
  have ht : 1 ≤ 2^s := Nat.one_le_pow _ _ (by omega)
  have hg := chooseWork_with_pack hsn
  have hu : (∑ U ∈ (Finset.univ : Finset V).powersetCard s,
        ((localEvaluator incidence edges b w U).operations+1)) ≤
      (Fintype.card V).choose s * (localConstant (Fintype.card V) edges.card*2^s+1) := by
    calc
      _ ≤ ∑ U ∈ (Finset.univ : Finset V).powersetCard s,
        (localConstant (Fintype.card V) edges.card*2^s+1) := by
          apply Finset.sum_le_sum
          intro U hU
          have hcard := (Finset.mem_powersetCard.mp hU).2
          have hh := local_cost incidence edges b w U
          rw [hcard] at hh
          omega
      _ = _ := by simp
  rw [layer_operations]
  have hmul := Nat.mul_le_mul hc ht
  have hN : 6*k+9 ≤ 9*(Fintype.card V+1)^2 := by nlinarith
  have hh := Nat.mul_le_mul_left (9*(Fintype.card V+1)^2) hmul
  have hgg := Nat.mul_le_mul_right ((Fintype.card V).choose s) (show 1 ≤ 2^s from ht)
  have hg2 := Nat.mul_le_mul_left (4*(Fintype.card V+1)^2) hgg
  have hchoose := Nat.mul_le_mul_left ((Fintype.card V).choose s) ht
  unfold layerConstant localConstant at *
  nlinarith [Nat.sub_le k s]

/-- A direct operation bound for the actual collapsed support algorithm. -/
theorem truncated_cost (incidence : E → Finset V) (edges : Finset E) (b : Bool → ℝ)
    (w : E → ℝ) {k : ℕ} (hk : k ≤ Fintype.card V) :
    (truncated incidence edges b w k).operations ≤
      layerConstant (Fintype.card V) edges.card *
        ∑ s ∈ Finset.range (k+1), (Fintype.card V).choose s * 2^s := by
  simp only [truncated,sumFinset_operations]
  have he : (Finset.range (k+1)).card = ∑ i ∈ Finset.range (k+1), (1 : ℕ) := by simp
  rw [he, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  exact layer_cost incidence edges b w (by have := Finset.mem_range.mp hs; omega) hk

/-- Proposition 3.3's single operation bound also covers the exact `k=N`
branch, which performs one ambient spin average. -/
theorem supportSum_cost (incidence : E → Finset V) (edges : Finset E) (b : Bool → ℝ)
    (w : E → ℝ) {k : ℕ} (hk : k ≤ Fintype.card V) :
    (supportSum incidence edges b w k).operations ≤
      layerConstant (Fintype.card V) edges.card *
        ∑ s ∈ Finset.range (k+1), (Fintype.card V).choose s * 2^s := by
  unfold supportSum
  split_ifs with hlt
  · exact truncated_cost incidence edges b w hk
  · have heq : k = Fintype.card V := by omega
    subst k
    have hc := local_cost incidence edges b w (Finset.univ : Finset V)
    simp only [Finset.card_univ] at hc
    have hconst : localConstant (Fintype.card V) edges.card ≤
        layerConstant (Fintype.card V) edges.card := by
      unfold localConstant layerConstant
      nlinarith
    have hsum : 2^Fintype.card V ≤
        ∑ s ∈ Finset.range (Fintype.card V+1), (Fintype.card V).choose s * 2^s := by
      have hh := Finset.single_le_sum (fun s hs => Nat.zero_le ((Fintype.card V).choose s * 2^s))
        (show Fintype.card V ∈ Finset.range (Fintype.card V+1) by simp)
      simpa only [Nat.choose_self,one_mul] using hh
    exact hc.trans (Nat.mul_le_mul hconst hsum)

end Manuscript.SupportExecution
