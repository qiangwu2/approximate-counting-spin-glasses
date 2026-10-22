import Manuscript.SupportDegrees
import Manuscript.Model
import SpinGlass.SupportScalar
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Finite support grouping and generating-product bounds for mixed hypergraphs. -/
noncomputable section
open scoped BigOperators

namespace Manuscript.SupportMassCounting
open Manuscript.FieldExpansion Manuscript.SupportEvaluation

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

def supportFamily (incidence : E → Finset V) (edges : Finset E) (v : ℕ) :
    Finset (Finset E) := edges.powerset.filter (fun Γ => (support incidence Γ).card = v)

def supportMass (incidence : E → Finset V) (edges : Finset E) (h : ℝ)
    (r : E → ℝ) (v : ℕ) : ℝ :=
  ∑ Γ ∈ supportFamily incidence edges v,
    Real.tanh h ^ (2 * (boundary incidence Γ).card) * ∏ e ∈ Γ, r e

/-- A simple edge array contains at most `choose |S| p` interactions of order `p` in `S`. -/
theorem induced_order_card_le (incidence : E → Finset V) (edges : Finset E)
    (hinj : Set.InjOn incidence edges) (S : Finset V) (p : ℕ) :
    ((edges.filter (fun e => incidence e ⊆ S)).filter
      (fun e => (incidence e).card = p)).card ≤ S.card.choose p := by
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn incidence
  · intro e he
    obtain ⟨heS, hep⟩ := Finset.mem_filter.mp he
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp heS).2, hep⟩
  · intro e he f hf hef
    exact hinj (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1 hef

/-- Positive local scale converts a binomial interaction count into a linear support bound. -/
theorem choose_scaled_le (v p : ℕ) (hv : 0 < v) (hp : 0 < p)
    (c : ℝ) (hc : 0 ≤ c) :
    (v.choose p : ℝ) * (c / (v : ℝ) ^ (p - 1)) ≤ (v : ℝ) * c / p.factorial := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have heq : (v : ℝ)^p = (v : ℝ) * (v : ℝ)^(p-1) := by
    rw [← pow_succ']; congr 1; omega
  calc
    _ ≤ ((v : ℝ)^p / p.factorial) * (c / (v : ℝ)^(p-1)) :=
      mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div p v) (by positivity)
    _ = _ := by rw [heq]; field_simp

/-- The residual edge fugacities have total at most `v * sum c_p/p!` on `v` vertices. -/
theorem induced_scale_sum_le (incidence : E → Finset V) (edges : Finset E)
    (hinj : Set.InjOn incidence edges) (P : Finset ℕ)
    (hP : ∀ e ∈ edges, (incidence e).card ∈ P) (hp : ∀ p ∈ P, 0 < p)
    (S : Finset V) (v : ℕ) (hSv : S.card = v) (hv : 0 < v)
    (c : ℕ → ℝ) (hc : ∀ p ∈ P, 0 ≤ c p) :
    (∑ e ∈ edges.filter (fun e => incidence e ⊆ S),
      c (incidence e).card / (v : ℝ)^((incidence e).card-1)) ≤
        (v : ℝ) * ∑ p ∈ P, c p / p.factorial := by
  have hmap : ∀ e ∈ edges.filter (fun e => incidence e ⊆ S), (incidence e).card ∈ P :=
    fun e he => hP e (Finset.mem_filter.mp he).1
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpP
  have heq : (∑ e ∈ (edges.filter (fun e => incidence e ⊆ S)).filter
      (fun e => (incidence e).card = p), c (incidence e).card / (v : ℝ)^((incidence e).card-1)) =
      (((edges.filter (fun e => incidence e ⊆ S)).filter
        (fun e => (incidence e).card = p)).card : ℝ) * (c p / (v : ℝ)^(p-1)) := by
    calc
      _ = ∑ _e ∈ (edges.filter (fun e => incidence e ⊆ S)).filter
        (fun e => (incidence e).card = p), c p / (v : ℝ)^(p-1) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [(Finset.mem_filter.mp he).2]
      _ = _ := by simp [nsmul_eq_mul]
  rw [heq]
  have hcard := induced_order_card_le incidence edges hinj S p
  rw [hSv] at hcard
  have hcardR : (((edges.filter (fun e => incidence e ⊆ S)).filter
      (fun e => (incidence e).card = p)).card : ℝ) ≤ (v.choose p : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ (v.choose p : ℝ) * (c p / (v : ℝ)^(p-1)) :=
      mul_le_mul_of_nonneg_right hcardR (div_nonneg (hc p hpP) (by positivity))
    _ ≤ _ := by simpa only [mul_div_assoc] using choose_scaled_le v p hv (hp p hpP) (c p) (hc p hpP)

/-- Exact-support graphs form a subfamily of the complete induced powerset. -/
theorem support_fiber_subset (incidence : E → Finset V) (edges : Finset E)
    (v : ℕ) (S : Finset V) :
    (supportFamily incidence edges v).filter (fun Γ => support incidence Γ = S) ⊆
      (edges.filter (fun e => incidence e ⊆ S)).powerset := by
  intro Γ hΓ
  obtain ⟨hΓfam, hs⟩ := Finset.mem_filter.mp hΓ
  have hΓedges := Finset.mem_powerset.mp (Finset.mem_filter.mp hΓfam).1
  apply Finset.mem_powerset.mpr
  intro e he
  apply Finset.mem_filter.mpr
  refine ⟨hΓedges he, ?_⟩
  intro x hx
  rw [← hs]
  exact (SupportDegrees.mem_support_iff incidence Γ x).mpr ⟨e, he, hx⟩

/-- Support selection followed by the exact finite generating product. -/
theorem support_sum_le_generating_product
    (incidence : E → Finset V) (edges : Finset E) (v : ℕ)
    (w : Finset E → ℝ) (q : E → ℝ) (hq : ∀ e ∈ edges, 0 ≤ q e)
    (K T : ℝ) (hK : 0 ≤ K)
    (hpoint : ∀ Γ ∈ supportFamily incidence edges v, w Γ ≤ K * ∏ e ∈ Γ, q e)
    (hlocal : ∀ S ∈ (Finset.univ : Finset V).powersetCard v,
      (∑ e ∈ edges.filter (fun e => incidence e ⊆ S), q e) ≤ T) :
    (∑ Γ ∈ supportFamily incidence edges v, w Γ) ≤
      ((Fintype.card V).choose v : ℝ) * K * Real.exp T := by
  have hmap : ∀ Γ ∈ supportFamily incidence edges v,
      support incidence Γ ∈ (Finset.univ : Finset V).powersetCard v := by
    intro Γ hΓ
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_filter.mp hΓ).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hbound : ∀ S ∈ (Finset.univ : Finset V).powersetCard v,
      (∑ Γ ∈ (supportFamily incidence edges v).filter (fun Γ => support incidence Γ = S), w Γ) ≤
        K * Real.exp T := by
    intro S hS
    calc
      _ ≤ ∑ Γ ∈ (supportFamily incidence edges v).filter
          (fun Γ => support incidence Γ = S), K * ∏ e ∈ Γ, q e := by
            exact Finset.sum_le_sum (fun Γ hΓ => hpoint Γ (Finset.mem_filter.mp hΓ).1)
      _ ≤ ∑ Γ ∈ (edges.filter (fun e => incidence e ⊆ S)).powerset,
          K * ∏ e ∈ Γ, q e := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (support_fiber_subset incidence edges v S)
            intro Γ hΓ hnot
            apply mul_nonneg hK
            apply Finset.prod_nonneg
            intro e he
            exact hq e (Finset.mem_filter.mp ((Finset.mem_powerset.mp hΓ) he)).1
      _ = K * ∏ e ∈ edges.filter (fun e => incidence e ⊆ S), (1 + q e) := by
            rw [← Finset.mul_sum, Finset.prod_one_add]
      _ ≤ K * Real.exp (∑ e ∈ edges.filter (fun e => incidence e ⊆ S), q e) := by
            apply mul_le_mul_of_nonneg_left _ hK
            calc
              _ ≤ ∏ e ∈ edges.filter (fun e => incidence e ⊆ S), Real.exp (q e) := by
                apply Finset.prod_le_prod
                · intro e he
                  linarith [hq e (Finset.mem_filter.mp he).1]
                · intro e he
                  linarith [Real.add_one_le_exp (q e)]
              _ = _ := (Real.exp_sum _ _).symm
      _ ≤ K * Real.exp T :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hlocal S hS)) hK
  calc
    _ ≤ ∑ _S ∈ (Finset.univ : Finset V).powersetCard v, K * Real.exp T :=
      Finset.sum_le_sum hbound
    _ = _ := by simp [Finset.card_powersetCard, nsmul_eq_mul, mul_assoc]

end Manuscript.SupportMassCounting
