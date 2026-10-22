import Manuscript.SKAugmentFinset
import SpinGlass.SKPrimitiveMonomialValues

/-! Exact physical-edge counts in ghost-augmented path and cycle primitives. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKChargedPrimitiveCounts
open SpinGlass SpinGlass.Expansion SpinGlass.SKTraversal SpinGlass.SKActualEvaluator
open Manuscript.SKAugmentFinset Manuscript.SKChargedMonomial
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Ordinary distinguished endpoints contribute one charged boundary edge. -/
def endpointCharge (A : Finset (Option V)) (a : Fin A.card) : ℕ :=
  if branch A a = none then 0 else 1

/-- Each uncharged edge is exactly one incidence at the ghost. -/
theorem edgeCount_add_ghost_degree (Γ : Finset (Finset (Option V))) :
    edgeCount charge Γ + degree id Γ none = Γ.card := by
  simpa only [edgeCount, charge, decide_eq_true_eq, degree, id_eq, not_not] using
    Finset.card_filter_add_card_filter_not (s := Γ) (fun e => none ∉ e)

theorem path_edgeCount {a c : Option V} {l : List (Option V)}
    (hac : a ≠ c) (hn : l.Nodup) (ha : a ∉ l) (hc : c ∉ l)
    (hg : none ∉ l) (hlen : 1 ≤ l.length) :
    edgeCount charge (betweenEdges a c l) =
      l.length - 1 + (if a = none then 0 else 1) + (if c = none then 0 else 1) := by
  have he := edgeCount_add_ghost_degree (betweenEdges a c l)
  rw [betweenEdges_card hac hn ha hc, betweenEdges_degree hac hn ha hc] at he
  simp only [hg, if_false] at he
  by_cases hag : a = none <;> by_cases hcg : c = none
  · exact (hac (hag.trans hcg.symm)).elim
  all_goals simp only [hag, hcg, eq_comm, if_true, if_false, true_or, or_true,
    false_or, or_false] at he ⊢ <;> omega

theorem return_edgeCount {a : Option V} {l : List (Option V)}
    (hn : l.Nodup) (ha : a ∉ l) (hg : none ∉ l) (hlen : 2 ≤ l.length) :
    edgeCount charge (rootedEdges a l) =
      l.length - 1 + (if a = none then 0 else 1) + (if a = none then 0 else 1) := by
  have he := edgeCount_add_ghost_degree (rootedEdges a l)
  rw [rootedEdges_card hn ha hlen, rootedEdges_degree hn ha hlen] at he
  by_cases hag : a = none
  all_goals simp only [hg, hag, eq_comm, if_true, if_false, false_or, or_false] at he ⊢ <;> omega

theorem cycle_edgeCount {l : List (Option V)} (hn : l.Nodup)
    (hg : none ∉ l) (hlen : 3 ≤ l.length) :
    edgeCount charge (cycleEdges l) = l.length := by
  have he := edgeCount_add_ghost_degree (cycleEdges l)
  rw [cycleEdges_card hn hlen, cycleEdges_degree hn hlen] at he
  simpa [hg] using he

theorem direct_edgeCount (a c : Option V) :
    edgeCount charge ({({a,c} : Finset (Option V))} : Finset (Finset (Option V))) =
      if a = none ∨ c = none then 0 else 1 := by
  have hg : (none ∉ ({a,c} : Finset (Option V))) ↔ ¬(a = none ∨ c = none) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, eq_comm]
  unfold edgeCount charge
  simp only [decide_eq_true_eq, Finset.filter_singleton, hg]
  split_ifs <;> simp_all

end Manuscript.SKChargedPrimitiveCounts
