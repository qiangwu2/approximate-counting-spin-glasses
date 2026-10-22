import Manuscript.SKGhostOutsideSize
import Manuscript.SKColorEstimator

/-! The complete charged evaluator aggregation equals the analyzed color estimator. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKGhostCoefficient
open SpinGlass SKGhostAdmissible
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def singleCoefficient {K : ℕ} (χ : V → Fin K) (Γ : Finset (Finset V)) : ℝ :=
  ColoringProbability.coefficient K (fun v : SKGraph.outside id Γ => χ v)

theorem singleCoefficient_eq {K : ℕ} (χ : V → Fin K) (Γ : Finset (Finset V)) :
    singleCoefficient χ Γ =
      (if Set.InjOn χ (SKGraph.outside id Γ) then 1 else 0) /
        ColoringProbability.probability K (SKGraph.outside id Γ).card := by
  have hi : Function.Injective (fun v : SKGraph.outside id Γ => χ v) ↔
      Set.InjOn χ (SKGraph.outside id Γ) := by
    constructor
    · intro h v hv u hu heq
      exact congrArg Subtype.val (h (show χ (⟨v,hv⟩ : SKGraph.outside id Γ) = χ (⟨u,hu⟩ : SKGraph.outside id Γ) from heq))
    · intro h v u heq
      exact Subtype.ext (h v.property u.property heq)
  simp [singleCoefficient,ColoringProbability.coefficient,ColoringProbability.indicator,hi]

theorem weightedSizeSum_eq {K L : ℕ} (hLK : L ≤ K) (A : Finset V) (χ : V → Fin K)
    (hK : 0 < K) (h : ℝ) (w : Finset V → ℝ) :
    (∑ m ∈ Finset.range (K+1), (ColoringProbability.probability K m)⁻¹ *
      byOutsideSize A χ L m h w) =
    ∑ Γ ∈ SKBranching.branchFamily A,
      if Γ.card ≤ L then singleCoefficient χ Γ * FieldExpansion.graphWeight id h w Γ else 0 := by
  simp_rw [byOutsideSize_eq hLK A χ hK,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hL : Γ.card ≤ L
  · by_cases hc : Set.InjOn χ (SKGraph.outside id Γ)
    · have hcK : (SKGraph.outside id Γ).card ≤ K := by
        rw [← Finset.card_image_of_injOn hc]
        simpa using Finset.card_le_univ ((SKGraph.outside id Γ).image χ)
      rw [Finset.sum_eq_single (SKGraph.outside id Γ).card]
      · simp [hL,hc,singleCoefficient_eq,div_eq_mul_inv]
      · intro m hm hne
        have hn : (SKGraph.outside id Γ).card ≠ m := Ne.symm hne
        simp [hL,hc,hn]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr (by omega)))
    · simp [hL,hc,singleCoefficient_eq]
  · simp [hL]

theorem candidate_sum (D : ℕ) (f : Finset V → ℝ) :
    (∑ b ∈ Finset.range (D+1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b, f A) =
      ∑ A ∈ (Finset.univ : Finset V).powerset.filter (fun A => A.card ≤ D), f A := by
  have hh := Finset.sum_fiberwise_eq_sum_filter ((Finset.univ : Finset V).powerset)
    (Finset.range (D+1)) Finset.card f
  simpa only [← Finset.powersetCard_eq_filter,Finset.mem_range,Nat.lt_succ_iff] using hh

/-- Exact partition by the actual branching set, on the bounded candidate schedule. -/
theorem candidate_graph_sum (D : ℕ) (f : Finset V → Finset (Finset V) → ℝ) :
    (∑ b ∈ Finset.range (D+1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
      ∑ Γ ∈ SKBranching.branchFamily A, f A Γ) =
    ∑ Γ ∈ (SKBranching.pairGraphs V).filter (fun Γ => (SKGraph.branch id Γ).card ≤ D),
      f (SKGraph.branch id Γ) Γ := by
  rw [candidate_sum]
  simp only [SKBranching.branchFamily,Finset.sum_filter,Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hd : (SKGraph.branch id Γ).card ≤ D
  · rw [Finset.sum_eq_single (SKGraph.branch id Γ)]
    · simp [hd]
    · intro A hA hne
      have hn : SKGraph.branch id Γ ≠ A := Ne.symm hne
      simp [hn]
    · simp
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro A hA
    by_cases hb : SKGraph.branch id Γ = A
    · simp [← hb,hd]
    · simp [hb]

def algorithm (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (h : ℝ) (w : Finset V → ℝ) : ℝ :=
  ∑ b ∈ Finset.range (D+1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
    (R : ℝ)⁻¹ * ∑ r : Fin R, ∑ m ∈ Finset.range (2*L+1),
      (ColoringProbability.probability (2*L) m)⁻¹ * byOutsideSize A (χ A r) L m h w

theorem averageSizeSum_eq (L R : ℕ) (hL : 0 < L) (A : Finset V)
    (χ : SKColorEstimator.Colors V L R) (h : ℝ) (w : Finset V → ℝ) :
    (R : ℝ)⁻¹ * (∑ r : Fin R, ∑ m ∈ Finset.range (2*L+1),
      (ColoringProbability.probability (2*L) m)⁻¹ * byOutsideSize A (χ A r) L m h w) =
    ∑ Γ ∈ SKBranching.branchFamily A,
      if Γ.card ≤ L then ((R : ℝ)⁻¹ * ∑ r : Fin R, singleCoefficient (χ A r) Γ) *
        FieldExpansion.graphWeight id h w Γ else 0 := by
  simp_rw [weightedSizeSum_eq (by omega : L ≤ 2*L) A _ (by omega : 0 < 2*L)]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hk : Γ.card ≤ L
  · simp only [hk,if_true]
    rw [← Finset.sum_mul]
    ring
  · simp [hk]

/-- Algorithm 3 is exactly the actual graph estimator analyzed under uniform
colors and the original disorder law. No evaluator-correctness premise remains. -/
theorem algorithm_eq_graph_estimator (D L R : ℕ) (hL : 0 < L)
    (χ : SKColorEstimator.Colors V L R) (h : ℝ) (w : Finset V → ℝ) :
    algorithm D L R χ h w =
    ∑ Γ ∈ (SKBranching.pairGraphs V).filter (SKGraph.Retained id D L),
      SKColorEstimator.coefficient id L R χ Γ * FieldExpansion.graphWeight id h w Γ := by
  unfold algorithm
  simp_rw [averageSizeSum_eq L R hL]
  rw [candidate_graph_sum]
  simp only [Finset.sum_filter,SKGraph.Retained]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  by_cases hd : (SKGraph.branch id Γ).card ≤ D <;> by_cases he : Γ.card ≤ L
  · simp only [hd,he,and_self,if_true]
    rfl
  · simp [hd,he]
  · simp [hd,he]
  · simp [hd,he]

theorem algorithm_eq_disorder (D L R : ℕ) (hL : 0 < L)
    (χ : SKColorEstimator.Colors V L R) (h : ℝ) (a : Finset V → ℝ) (J : Finset V → ℝ) :
    algorithm D L R χ h (fun e => Real.tanh (a e * J e)) =
      SKColorEstimator.estimator id ((Finset.univ : Finset V).powersetCard 2) D L R h a χ J := by
  rw [algorithm_eq_graph_estimator D L R hL]
  rfl

end Manuscript.SKGhostCoefficient
