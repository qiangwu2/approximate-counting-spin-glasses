import Manuscript.SKGhostCoefficient

/-! Exact charged-edge and outside-size aggregation of the implemented evaluator. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKGhostCoefficient
open SpinGlass SKActualEvaluator SKChargedMonomial SKGhostAdmissible SKChargedPrimitiveCounts SKAugmentFinset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def byOutsideSize {K : ℕ} (A : Finset V) (χ : V → Fin K) (L m : ℕ)
    (h : ℝ) (w : Finset V → ℝ) : ℝ :=
  SKChargedExecution.byOutsideSize (endpointCharge (distinguished A))
    (branch (distinguished A)) Subtype.val (outsideColor A χ) (edgeWeight h w) L m (accepted A)

/-- Summing coefficient coordinates selects the actual charged budget and size. -/
theorem coordinate_sum {K L : ℕ} (hLK : L ≤ K) (n m : ℕ) (T : Finset (Fin K))
    (P : Prop) [Decidable P] (w : ℝ) :
    (∑ k : Fin (K+1), ∑ S : Finset (Fin K),
      if k.val ≤ L ∧ S.card = m then
        if n = k.val ∧ T = S ∧ P then w else 0 else 0) =
      if n ≤ L ∧ T.card = m ∧ P then w else 0 := by
  by_cases hp : P
  · by_cases hn : n ≤ L
    · let k0 : Fin (K+1) := ⟨n,by omega⟩
      rw [Finset.sum_eq_single k0]
      · rw [Finset.sum_eq_single T]
        · simp [k0,hn,hp]
        · intro S hS hST
          have hTS : T ≠ S := Ne.symm hST
          simp [hTS]
        · simp
      · intro k hk hkk
        have hnne : n ≠ k.val := by intro he; exact hkk (Fin.ext he.symm)
        simp [hnne]
      · simp
    · have hz : ∀ k : Fin (K+1), ∀ S : Finset (Fin K),
          (if k.val ≤ L ∧ S.card = m then if n = k.val ∧ T = S ∧ P then w else 0 else 0) = 0 := by
        intro k S
        by_cases hk : k.val ≤ L
        · have hnne : n ≠ k.val := by omega
          simp [hnne]
        · simp [hk]
      simp [hz,hn]
  · simp [hp]

/-- The returned outside-size vector is precisely the colorful original-graph
sum with at most L original edges and the proposed exact branching set. -/
theorem byOutsideSize_eq {K L : ℕ} (hLK : L ≤ K) (A : Finset V) (χ : V → Fin K)
    (hK : 0 < K) (m : ℕ) (h : ℝ) (w : Finset V → ℝ) :
    byOutsideSize A χ L m h w =
      ∑ Γ ∈ SKBranching.branchFamily A,
        if Γ.card ≤ L ∧ (SKGraph.outside id Γ).card = m ∧ Set.InjOn χ (SKGraph.outside id Γ)
        then FieldExpansion.graphWeight id h w Γ else 0 := by
  unfold byOutsideSize SKChargedExecution.byOutsideSize
  have hs (k : Fin (K+1)) (S : Finset (Fin K)) :
      (∑ d ∈ accepted A, if k.val ≤ L ∧ S.card = m then
        evaluate A χ h w (target k S d) else 0) =
      if k.val ≤ L ∧ S.card = m then
        ∑ d ∈ accepted A, evaluate A χ h w (target k S d) else 0 := by
    by_cases hp : k.val ≤ L ∧ S.card = m <;> simp [hp]
  change (∑ k : Fin (K+1), ∑ S : Finset (Fin K),
    ∑ d ∈ accepted A, if k.val ≤ L ∧ S.card = m then
      evaluate A χ h w (target k S d) else 0) = _
  simp_rw [hs,coefficient_original A χ hK h w,Finset.ite_sum_zero]
  conv_lhs => enter [2,k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [coordinate_sum hLK]
  by_cases hc : Set.InjOn χ (SKGraph.outside id Γ)
  · rw [Finset.card_image_of_injOn hc]
  · simp [hc]

end Manuscript.SKGhostCoefficient
