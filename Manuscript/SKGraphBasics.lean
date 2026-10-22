import Manuscript.SupportDegrees

/-!
# Original-edge SK graph predicates

The branching threshold is three before augmentation. All counts in this file
refer to original pair interactions; a later ghost augmentation does not change
the edge budget used here.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKGraph

open SpinGlass.Expansion Manuscript.SupportEvaluation Manuscript.SupportDegrees

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The actual branching vertices before adding the ghost. -/
def branch (incidence : E → Finset V) (Γ : Finset E) : Finset V :=
  Finset.univ.filter (fun v => 3 ≤ degree incidence Γ v)

/-- Exactly the original vertices that receive colors for this graph. -/
def outside (incidence : E → Finset V) (Γ : Finset E) : Finset V :=
  support incidence Γ \ branch incidence Γ

/-- Both cutoffs apply to the original graph. -/
def Retained (incidence : E → Finset V) (D L : ℕ) (Γ : Finset E) : Prop :=
  (branch incidence Γ).card ≤ D ∧ Γ.card ≤ L

instance (incidence : E → Finset V) (D L : ℕ) (Γ : Finset E) :
    Decidable (Retained incidence D L Γ) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem mem_branch (incidence : E → Finset V) (Γ : Finset E) (v : V) :
    v ∈ branch incidence Γ ↔ 3 ≤ degree incidence Γ v := by simp [branch]

theorem branch_subset_support (incidence : E → Finset V) (Γ : Finset E) :
    branch incidence Γ ⊆ support incidence Γ := by
  intro v hv
  exact (degree_pos_iff_mem_support incidence Γ v).mp (by
    have h := (mem_branch incidence Γ v).mp hv
    omega)

theorem pair_totalDegree (incidence : E → Finset V) (Γ : Finset E)
    (hp : ∀ e ∈ Γ, (incidence e).card = 2) :
    totalDegree incidence Γ = 2 * Γ.card := by
  unfold totalDegree
  rw [Finset.sum_congr rfl hp]
  simp [Nat.mul_comm]

/-- No parity restriction is needed for the palette bound of Section 4.4. -/
theorem outside_card_le_twice_edges (incidence : E → Finset V) (Γ : Finset E)
    (hp : ∀ e ∈ Γ, (incidence e).card = 2) :
    (outside incidence Γ).card ≤ 2 * Γ.card := by
  have h := support_card_le_totalDegree incidence Γ
  rw [pair_totalDegree incidence Γ hp] at h
  exact (Finset.card_le_card Finset.sdiff_subset).trans h

/-- Every graph in the retained family fits into the manuscript's `2L` colors. -/
theorem retained_outside_card (incidence : E → Finset V) (D L : ℕ)
    (Γ : Finset E) (hp : ∀ e ∈ Γ, (incidence e).card = 2)
    (hkeep : Retained incidence D L Γ) : (outside incidence Γ).card ≤ 2 * L :=
  (outside_card_le_twice_edges incidence Γ hp).trans (Nat.mul_le_mul_left 2 hkeep.2)

/-- The branching-degree bound used in the large-branching edge tail. -/
theorem three_branch_le_twice_edges (incidence : E → Finset V) (Γ : Finset E)
    (hp : ∀ e ∈ Γ, (incidence e).card = 2) :
    3 * (branch incidence Γ).card ≤ 2 * Γ.card := by
  calc
    3 * (branch incidence Γ).card = ∑ _v ∈ branch incidence Γ, (3 : ℕ) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ branch incidence Γ, degree incidence Γ v := by
      exact Finset.sum_le_sum (fun v hv => (mem_branch incidence Γ v).mp hv)
    _ ≤ ∑ v : V, degree incidence Γ v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = 2 * Γ.card := by rw [sum_degrees, pair_totalDegree incidence Γ hp]

end Manuscript.SKGraph
