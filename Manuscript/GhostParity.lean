import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

/-!
# The SK ghost augmentation and degree states

This file proves the finite graph assertions at the beginning of Section 4.2
and the degree-state arithmetic used in Section 4.3. The graph is
constructed from its actual adjacency relation: `none` is the ghost vertex,
and `some v` is the original vertex `v`.

It does not assert the path/cycle decomposition or the color-coded algorithm.
-/

namespace Manuscript.GhostParity

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Add one ghost edge at precisely each original odd-degree vertex. -/
def augment (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some v, some w => G.Adj v w
    | none, some w => Odd (G.degree w)
    | some v, none => Odd (G.degree v)
    | none, none => False
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro x
    cases x <;> simp⟩

instance augmentDecidable (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (augment G).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [augment] <;> infer_instance

omit [DecidableEq V] in
@[simp] theorem augment_original_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (v w : V) : (augment G).Adj (some v) (some w) ↔ G.Adj v w := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem augment_ghost_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (augment G).Adj none (some v) ↔ Odd (G.degree v) := Iff.rfl

private theorem neighbor_original (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (augment G).neighborFinset (some v) =
      if Odd (G.degree v) then insert none ((G.neighborFinset v).image some)
      else (G.neighborFinset v).image some := by
  classical
  ext x
  cases x <;> by_cases h : Odd (G.degree v) <;> simp [augment, h]

/-- The original degree increases by one if and only if it was odd. -/
theorem degree_original (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (augment G).degree (some v) = G.degree v + if Odd (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, neighbor_original]
  by_cases h : Odd (G.degree v) <;>
    simp [h, Finset.card_image_of_injective _ (Option.some_injective V)]

/-- The ghost degree is the number of odd-degree vertices of the original graph. -/
theorem degree_ghost (G : SimpleGraph V) [DecidableRel G.Adj] :
    (augment G).degree none = (Finset.univ.filter (fun v => Odd (G.degree v))).card := by
  classical
  have h : (augment G).neighborFinset none =
      (Finset.univ.filter (fun v => Odd (G.degree v))).image some := by
    ext x
    cases x <;> simp [augment]
  rw [SimpleGraph.degree, h, Finset.card_image_of_injective _ (Option.some_injective V)]

/-- Every degree of the explicitly constructed augmented graph is even. -/
theorem even_degree_augment (G : SimpleGraph V) [DecidableRel G.Adj] (x : Option V) :
    Even ((augment G).degree x) := by
  cases x with
  | none =>
      rw [degree_ghost]
      exact G.even_card_odd_degree_vertices
  | some v =>
      rw [degree_original]
      by_cases h : Odd (G.degree v)
      · simp only [h, if_true]
        exact h.add_odd (by decide)
      · simpa [h] using Nat.not_odd_iff_even.mp h

/-- The branching threshold is exactly four after augmentation. -/
theorem branching_iff (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    3 ≤ G.degree v ↔ 4 ≤ (augment G).degree (some v) := by
  rw [degree_original]
  by_cases h : Odd (G.degree v)
  · simp only [h, if_true]
    omega
  · simp only [h, if_false, Nat.add_zero]
    have he := Nat.even_iff.mp (Nat.not_odd_iff_even.mp h)
    omega

omit [DecidableEq V] in
/-- Removing the ghost leaves the original adjacency relation. -/
theorem erase_augment (G : SimpleGraph V) [DecidableRel G.Adj] :
    (augment G).comap some = G := by
  ext v w
  rfl

private theorem degree_remove_ghost (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
    (v : V) :
    H.degree (some v) = (H.comap some).degree v + if H.Adj (some v) none then 1 else 0 := by
  classical
  have hn : H.neighborFinset (some v) =
      if H.Adj (some v) none then insert none (((H.comap some).neighborFinset v).image some)
      else ((H.comap some).neighborFinset v).image some := by
    ext x
    cases x <;> by_cases h : H.Adj (some v) none <;> simp [h]
  rw [SimpleGraph.degree, hn]
  by_cases h : H.Adj (some v) none <;>
    simp [h, Finset.card_image_of_injective _ (Option.some_injective V)]

/-- Evenness forces each ghost edge; it is not an additional choice. -/
theorem ghost_adj_forced (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
    (v : V) (h : Even (H.degree (some v))) :
    H.Adj (some v) none ↔ Odd ((H.comap some).degree v) := by
  rw [degree_remove_ghost] at h
  rw [Nat.even_iff] at h
  rw [Nat.odd_iff]
  by_cases ha : H.Adj (some v) none
  · simp only [ha, if_true] at h
    exact ⟨fun _ => by omega, fun _ => ha⟩
  · simp only [ha, if_false, Nat.add_zero] at h
    constructor
    · intro hx
      exact (ha hx).elim
    · intro hodd
      omega

/-- Any graph even at its original vertices is the augmentation of its restriction.
Thus the augmentation bijection in Section 4.2 follows without assuming a decomposition. -/
theorem augment_erase (H : SimpleGraph (Option V)) [DecidableRel H.Adj]
    (h : ∀ v : V, Even (H.degree (some v))) :
    augment (H.comap some) = H := by
  ext x y
  cases x with
  | none =>
      cases y with
      | none => simp [augment]
      | some v =>
          simpa [augment, H.adj_comm] using (ghost_adj_forced H v (h v)).symm
  | some v =>
      cases y with
      | none => exact (ghost_adj_forced H v (h v)).symm
      | some w => rfl

/-- The six degree states in Section 4.3. -/
def degreeState (d : ℕ) : ℕ := if d < 4 then d else 4 + d % 2

theorem degreeState_lt_six (d : ℕ) : degreeState d < 6 := by
  unfold degreeState
  split <;> omega

theorem degreeState_parity (d : ℕ) : degreeState d % 2 = d % 2 := by
  unfold degreeState
  split <;> omega

theorem degreeState_eq_four (d : ℕ) : degreeState d = 4 ↔ 4 ≤ d ∧ Even d := by
  simp only [degreeState, Nat.even_iff]
  split <;> omega

/-- Reduction may be performed after every array multiplication. -/
theorem degreeState_add (d e : ℕ) :
    degreeState (degreeState d + degreeState e) = degreeState (d + e) := by
  unfold degreeState
  split_ifs <;> omega

theorem degreeState_even (d : ℕ) :
    degreeState d = 0 ∨ degreeState d = 2 ∨ degreeState d = 4 ↔ Even d := by
  simp only [degreeState, Nat.even_iff]
  split <;> omega

end Manuscript.GhostParity
