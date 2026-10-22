import Manuscript.SupportEvaluation
import Manuscript.SupportExponent
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Actual hypergraph degree bounds for Lemma 3.1

The support and odd boundary are the same finite sets used in the field
expansion and local-support evaluator. The degree estimates below are proved
from their finite incidences, without uniformity assumptions on edge sizes.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.SupportDegrees

open SpinGlass.Expansion Manuscript.FieldExpansion Manuscript.SupportEvaluation

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- Total incidence degree, counted by interactions. -/
def totalDegree (incidence : E → Finset V) (Γ : Finset E) : ℕ :=
  ∑ e ∈ Γ, (incidence e).card

omit [Fintype V] in
/-- A vertex belongs to the support precisely when some selected edge uses it. -/
theorem mem_support_iff (incidence : E → Finset V) (Γ : Finset E) (v : V) :
    v ∈ support incidence Γ ↔ ∃ e ∈ Γ, v ∈ incidence e := by
  simp [support]

omit [Fintype V] in
/-- Positive degree is equivalent to membership in the actual vertex support. -/
theorem degree_pos_iff_mem_support (incidence : E → Finset V) (Γ : Finset E) (v : V) :
    0 < degree incidence Γ v ↔ v ∈ support incidence Γ := by
  rw [degree, Finset.card_pos, mem_support_iff]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hv⟩⟩

omit [Fintype V] in
/-- Unused vertices have degree zero. -/
theorem degree_zero_of_not_mem_support (incidence : E → Finset V) (Γ : Finset E)
    (v : V) (hv : v ∉ support incidence Γ) : degree incidence Γ v = 0 := by
  have hn : ¬ 0 < degree incidence Γ v :=
    fun hpos => hv ((degree_pos_iff_mem_support incidence Γ v).mp hpos)
  omega

/-- Double counting all ambient vertex-edge incidences gives the total degree. -/
theorem sum_degrees (incidence : E → Finset V) (Γ : Finset E) :
    (∑ v : V, degree incidence Γ v) = totalDegree incidence Γ := by
  have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun (v : V) (e : E) => v ∈ incidence e)
    (s := Finset.univ) (t := Γ)
  simpa [degree, totalDegree, Finset.bipartiteAbove, Finset.bipartiteBelow] using hh

omit [Fintype V] in
/-- The same total is obtained by summing only the used vertices. -/
theorem sum_support_degrees (incidence : E → Finset V) (Γ : Finset E) :
    (∑ v ∈ support incidence Γ, degree incidence Γ v) = totalDegree incidence Γ := by
  calc
    (∑ v ∈ support incidence Γ, degree incidence Γ v) =
        ∑ e ∈ Γ, ((support incidence Γ).filter (fun v => v ∈ incidence e)).card := by
      exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := fun (v : V) (e : E) => v ∈ incidence e)
    _ = totalDegree incidence Γ := by
      unfold totalDegree
      apply Finset.sum_congr rfl
      intro e he
      congr 1
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun hh => hh.2, fun hv =>
        ⟨(mem_support_iff incidence Γ v).mpr ⟨e, he, hv⟩, hv⟩⟩

omit [Fintype V] in
/-- Every used vertex contributes at least one incidence: `v ≤ d`. -/
theorem support_card_le_totalDegree (incidence : E → Finset V) (Γ : Finset E) :
    (support incidence Γ).card ≤ totalDegree incidence Γ := by
  rw [← sum_support_degrees]
  calc
    (support incidence Γ).card = ∑ _v ∈ support incidence Γ, (1 : ℕ) := by simp
    _ ≤ ∑ v ∈ support incidence Γ, degree incidence Γ v := by
      apply Finset.sum_le_sum
      intro v hv
      exact (degree_pos_iff_mem_support incidence Γ v).mpr hv

/-- Every odd-degree vertex lies in the actual support. -/
theorem boundary_subset_support (incidence : E → Finset V) (Γ : Finset E) :
    boundary incidence Γ ⊆ support incidence Γ := by
  intro v hv
  have hodd := (Finset.mem_filter.mp hv).2
  apply (degree_pos_iff_mem_support incidence Γ v).mp
  by_contra hn
  have hz : degree incidence Γ v = 0 := by omega
  simp [hz] at hodd

/-- A used vertex contributes at least two to degree plus its odd-boundary
indicator, since a used even-degree vertex has degree at least two. -/
theorem degree_add_odd_indicator_ge_two (incidence : E → Finset V) (Γ : Finset E)
    (v : V) (hv : v ∈ support incidence Γ) :
    2 ≤ degree incidence Γ v + if v ∈ boundary incidence Γ then 1 else 0 := by
  have hpos := (degree_pos_iff_mem_support incidence Γ v).mpr hv
  by_cases hb : v ∈ boundary incidence Γ
  · rw [if_pos hb]
    omega
  · rw [if_neg hb]
    have heven : Even (degree incidence Γ v) := by
      simpa [boundary] using hb
    obtain ⟨a, ha⟩ := heven
    omega

/-- Summing the odd-boundary indicators over support counts each odd vertex once. -/
theorem sum_odd_indicators (incidence : E → Finset V) (Γ : Finset E) :
    (∑ v ∈ support incidence Γ, if v ∈ boundary incidence Γ then (1 : ℕ) else 0) =
      (boundary incidence Γ).card := by
  rw [← Finset.sum_filter]
  have hf : (support incidence Γ).filter (fun v => v ∈ boundary incidence Γ) =
      boundary incidence Γ := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun hh => hh.2, fun hv => ⟨boundary_subset_support incidence Γ hv, hv⟩⟩
  rw [hf]
  simp

/-- The central degree/boundary inequality of Lemma 3.1: `2v ≤ d + |∂Γ|`. -/
theorem twice_support_le_totalDegree_add_boundary
    (incidence : E → Finset V) (Γ : Finset E) :
    2 * (support incidence Γ).card ≤ totalDegree incidence Γ + (boundary incidence Γ).card := by
  have hh : (∑ _v ∈ support incidence Γ, (2 : ℕ)) ≤
      ∑ v ∈ support incidence Γ,
        (degree incidence Γ v + if v ∈ boundary incidence Γ then 1 else 0) := by
    apply Finset.sum_le_sum
    intro v hv
    exact degree_add_odd_indicator_ge_two incidence Γ v hv
  rw [Finset.sum_add_distrib, sum_support_degrees, sum_odd_indicators] at hh
  simpa [Nat.mul_comm] using hh

/-- The number of odd-degree vertices is at least the truncated degree deficit. -/
theorem boundary_card_ge_deficit (incidence : E → Finset V) (Γ : Finset E) :
    2 * (support incidence Γ).card - totalDegree incidence Γ ≤ (boundary incidence Γ).card := by
  have hh := twice_support_le_totalDegree_add_boundary incidence Γ
  omega

/-- At zero boundary, every used vertex contributes at least two incidences. -/
theorem twice_support_le_totalDegree_of_boundary_empty
    (incidence : E → Finset V) (Γ : Finset E) (hb : boundary incidence Γ = ∅) :
    2 * (support incidence Γ).card ≤ totalDegree incidence Γ := by
  simpa [hb] using twice_support_le_totalDegree_add_boundary incidence Γ

/-- The degree/boundary inequality with real-valued positive-part notation, as
used in the field-factor estimate. -/
theorem real_boundary_card_ge_deficit (incidence : E → Finset V) (Γ : Finset E) :
    max (2 * ((support incidence Γ).card : ℝ) - (totalDegree incidence Γ : ℝ)) 0 ≤
      ((boundary incidence Γ).card : ℝ) := by
  apply max_le
  · have hh := twice_support_le_totalDegree_add_boundary incidence Γ
    have hr : 2 * ((support incidence Γ).card : ℝ) ≤
        (totalDegree incidence Γ : ℝ) + ((boundary incidence Γ).card : ℝ) := by exact_mod_cast hh
    linarith
  · positivity

omit [Fintype V] in
/-- Applying the scalar tradeoff to the actual graph degree no longer needs an
assumed lower bound `d ≥ v`; that bound follows from the finite incidence data. -/
theorem actual_degreeExponent_ge_kappa (incidence : E → Finset V) (Γ : Finset E)
    (p alpha : ℝ) (hp : 1 ≤ p) :
    SupportExponent.kappa p alpha * ((support incidence Γ).card : ℝ) ≤
      SupportExponent.degreeExponent p alpha
        ((support incidence Γ).card : ℝ) (totalDegree incidence Γ : ℝ) := by
  apply SupportExponent.degreeExponent_ge_kappa p alpha _ _ hp (by positivity)
  exact_mod_cast support_card_le_totalDegree incidence Γ

end Manuscript.SupportDegrees
