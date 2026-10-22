import Manuscript.SKChargedPrimitiveCounts
import Manuscript.SKChargedExecution
import SpinGlass.SKColorfulCatalog

/-! # Exact coordinate identities for every member of the actual finite catalogs -/
noncomputable section
namespace Manuscript.SKChargedPrimitiveValues
open SpinGlass
open Manuscript.SKAugmentFinset Manuscript.SKChargedPrimitiveCounts
open scoped BigOperators
open SKGraphMonomial SKPrimitiveMonomials SKRing SKFastEvaluator SKActualEvaluator SKTraversal SKColorfulCatalog
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

/-- Charged degree replaces ordinary edge cardinality as the first coordinate. -/
theorem charged_value_of_coordinates {b L : ℕ} (A : Finset (Option V))
    (branch : Fin b → Option V) (χ : Option V → Fin L) (f : Finset (Option V) → ℝ)
    (Γ : Finset (Finset (Option V))) (k : ℕ) (S : Finset (Fin L))
    (d : Fin b → CappedDegree) (hk : SKChargedMonomial.edgeCount charge Γ = k)
    (hS : colors id A χ Γ = S) (hc : Colorful id A χ Γ)
    (hd : (fun a => CappedDegree.ofNat (Expansion.degree id Γ (branch a))) = d) :
    SKChargedMonomial.value charge id A branch χ f Γ =
      insertMonomial k S d (∏ e ∈ Γ, f e) := by
  unfold SKChargedMonomial.value insertMonomial
  change (if hΓ : SKChargedMonomial.edgeCount charge Γ ≤ L then
    if Colorful id A χ Γ then _ else 0 else 0) = _
  simp only [hk, if_pos hc]
  split
  · congr 1
    apply Prod.ext
    · exact Fin.ext hk
    · exact Prod.ext hS hd
  · rfl

theorem path_value {L : ℕ} (A : Finset (Option V)) (hA : none ∈ A) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Option V) → ℝ) (a c : Fin A.card) (hac : a ≠ c) (S : Finset (Fin L)) (hS : 1 ≤ S.card)
    {Γ : Finset (Finset (Option V))} (hΓ : Γ ∈ pathCatalog A χ a c S) :
    SKChargedMonomial.value charge id A (branch A) (totalColor A χ hL) f Γ =
      insertMonomial (S.card - 1 + endpointCharge A a + endpointCharge A c) S (pathDegrees a c) (∏ e ∈ Γ, f e) := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
  have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
  have ho := lifted_list_outside A χ S hl
  have hroot : ∀ d, branch A d ∉ l := fun d hm => ho _ hm (branch_mem A d)
  apply charged_value_of_coordinates
  · have hg : none ∉ l := fun hm => ho _ hm hA
    have hlen : 1 ≤ l.length := by simpa [liftedChains_length Subtype.val χ S hl] using hS
    rw [path_edgeCount (fun h => hac (branch_injective A h)) hn (hroot a) (hroot c) hg hlen,
      liftedChains_length Subtype.val χ S hl]
    rfl
  · rw [colors, path_outside A χ a c S hl]
    exact lifted_list_colors A χ hL S hl
  · rw [Colorful, path_outside A χ a c S hl]
    exact lifted_list_colorful A χ hL S hl
  · exact between_degrees A a c hac l hn ho

theorem return_value {L : ℕ} (A : Finset (Option V)) (hA : none ∈ A) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Option V) → ℝ) (a : Fin A.card) (S : Finset (Fin L)) (hS : 2 ≤ S.card)
    {Γ : Finset (Finset (Option V))} (hΓ : Γ ∈ returnCatalog A χ a S) :
    SKChargedMonomial.value charge id A (branch A) (totalColor A χ hL) f Γ =
      insertMonomial (S.card - 1 + endpointCharge A a + endpointCharge A a) S (pathDegrees a a) (∏ e ∈ Γ, f e) := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
  have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
  have ho := lifted_list_outside A χ S hl
  have hlen : 2 ≤ l.length := by simpa [liftedChains_length Subtype.val χ S hl] using hS
  have hroot : branch A a ∉ l := fun hm => ho _ hm (branch_mem A a)
  apply charged_value_of_coordinates
  · have hg : none ∉ l := fun hm => ho _ hm hA
    rw [return_edgeCount hn hroot hg hlen, liftedChains_length Subtype.val χ S hl]
    rfl
  · rw [colors, return_outside A χ a S hl]
    exact lifted_list_colors A χ hL S hl
  · rw [Colorful, return_outside A χ a S hl]
    exact lifted_list_colorful A χ hL S hl
  · exact return_degrees A a l hn ho hlen

theorem cycle_value {L : ℕ} (A : Finset (Option V)) (hA : none ∈ A) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Option V) → ℝ) (S : Finset (Fin L)) (hS : 3 ≤ S.card)
    {Γ : Finset (Finset (Option V))} (hΓ : Γ ∈ cycleCatalog A χ S) :
    SKChargedMonomial.value charge id A (branch A) (totalColor A χ hL) f Γ =
      insertMonomial S.card S (fun _ => 0) (∏ e ∈ Γ, f e) := by
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hΓ
  have hn := liftedChains_nodup Subtype.val (outside_injective A) χ S hl
  have ho := lifted_list_outside A χ S hl
  have hlen : 3 ≤ l.length := by simpa [liftedChains_length Subtype.val χ S hl] using hS
  apply charged_value_of_coordinates
  · have hg : none ∉ l := fun hm => ho _ hm hA
    rw [cycle_edgeCount hn hg hlen, liftedChains_length Subtype.val χ S hl]
  · rw [colors, cycle_outside A χ S hl]
    exact lifted_list_colors A χ hL S hl
  · rw [Colorful, cycle_outside A χ S hl]
    exact lifted_list_colorful A χ hL S hl
  · exact cycle_degrees A l hn ho hlen

/-- Actual path DP output inserts exactly one copy of every signed path graph. -/
theorem path_sum {L : ℕ} (A : Finset (Option V)) (hA : none ∈ A) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Option V) → ℝ) (a c : Fin A.card) (hac : a ≠ c) (S : Finset (Fin L)) (hS : 1 ≤ S.card) :
    insertMonomial (S.card - 1 + endpointCharge A a + endpointCharge A c) S (pathDegrees a c)
      (pathCoefficient (branch A) Subtype.val χ f a c S) =
      ∑ Γ ∈ pathCatalog A χ a c S, SKChargedMonomial.value charge id A (branch A) (totalColor A χ hL) f Γ := by
  rw [pathCoefficient_eq]
  change insertMonomial _ _ _ (SKPrimitiveTables.pathClosure χ
    (fun i => f {branch A a,i.val}) (fun i j => f {i.val,j.val})
    (fun j => f {j.val,branch A c}) S) = _
  rw [pathClosure_eq_graph_sum Subtype.val (outside_injective A) χ S f
    (fun h => hac (branch_injective A h)) (branch_not_range A a) (branch_not_range A c)]
  rw [insertMonomial_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  exact (path_value A hA χ hL f a c hac S hS hΓ).symm

/-- The two-orientation-normalized return table inserts its precise graph sum. -/
theorem return_sum {L : ℕ} (A : Finset (Option V)) (hA : none ∈ A) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Option V) → ℝ) (a : Fin A.card) (S : Finset (Fin L)) (hS : 2 ≤ S.card) :
    insertMonomial (S.card - 1 + endpointCharge A a + endpointCharge A a) S (pathDegrees a a)
      (returnCoefficient (branch A) Subtype.val χ f a S) =
      ∑ Γ ∈ returnCatalog A χ a S, SKChargedMonomial.value charge id A (branch A) (totalColor A χ hL) f Γ := by
  rw [returnCoefficient_eq]
  change insertMonomial _ _ _ (SKPrimitiveTables.rootedClosure χ
    (fun i => f {branch A a,i.val}) (fun i j => f {i.val,j.val})
    (fun j => f {j.val,branch A a}) S) = _
  rw [rootedClosure_eq_graph_sum Subtype.val (outside_injective A) χ S f
    (branch_not_range A a) hS, insertMonomial_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  exact (return_value A hA χ hL f a S hS hΓ).symm

/-- The full root-and-orientation-normalized cycle table inserts its precise graph sum. -/
theorem cycle_sum {L : ℕ} (A : Finset (Option V)) (hA : none ∈ A) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Option V) → ℝ) (S : Finset (Fin L)) (hS : 3 ≤ S.card) :
    insertMonomial S.card S (fun _ => 0) (cycleCoefficient Subtype.val χ f S) =
      ∑ Γ ∈ cycleCatalog A χ S, SKChargedMonomial.value charge id A (branch A) (totalColor A χ hL) f Γ := by
  rw [cycleCoefficient_eq]
  change insertMonomial _ _ _ (SKPrimitiveTables.outsideClosure χ
    (fun i j => f {i.val,j.val}) S) = _
  rw [outsideClosure_eq_graph_sum Subtype.val (outside_injective A) χ S f hS,
    insertMonomial_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  exact (cycle_value A hA χ hL f S hS hΓ).symm

/-- The direct branch factor is the actual singleton-edge graph monomial. -/
theorem direct_value {L : ℕ} (A : Finset (Option V)) (χ : Outside A → Fin L) (hL : 0 < L)
    (f : Finset (Option V) → ℝ) (a c : Fin A.card) (hac : a ≠ c) :
    SKChargedMonomial.value charge id A (branch A) (totalColor A χ hL) f {{branch A a, branch A c}} =
      SKChargedExecution.direct (L := L) (endpointCharge A) (branch A) f a c := by
  have hout : outside id A ({{branch A a,branch A c}} : Finset (Finset (Option V))) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvU,hvA⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨e,he,hve⟩ := Finset.mem_biUnion.mp hvU
    have heq : e = {branch A a,branch A c} := Finset.mem_singleton.mp he
    simp only [id_eq, heq, Finset.mem_insert, Finset.mem_singleton] at hve
    rcases hve with rfl | rfl <;> exact hvA (branch_mem A _)
  have hc : Colorful id A (totalColor A χ hL) ({{branch A a,branch A c}} : Finset (Finset (Option V))) := by
    rw [Colorful, hout]
    simpa using Set.injOn_empty (totalColor A χ hL)
  have hd := between_degrees A a c hac [] (by simp) (by simp)
  have he : betweenEdges (branch A a) (branch A c) [] = {{branch A a,branch A c}} := by
    simp [betweenEdges, pathEdges, Finset.pair_comm]
  rw [he] at hd
  have ht := charged_value_of_coordinates A (branch A) (totalColor A χ hL) f
    {{branch A a,branch A c}}
    (if branch A a = none ∨ branch A c = none then 0 else 1) ∅ (pathDegrees a c)
    (direct_edgeCount (branch A a) (branch A c))
    (by simp [colors, hout]) hc hd
  have heq : (endpointCharge A a = 0 ∨ endpointCharge A c = 0) ↔
      (branch A a = none ∨ branch A c = none) := by simp [endpointCharge]
  simpa only [SKChargedExecution.direct, heq, pairWeight, Finset.prod_singleton] using ht


end Manuscript.SKChargedPrimitiveValues
