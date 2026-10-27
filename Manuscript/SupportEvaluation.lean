import Manuscript.FieldExpansion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
# Exact support evaluation in a homogeneous field

This module proves the finite biased local-spin formula (28), support Möbius
inversion, and the exact retained-support sum for arbitrary indexed hyperedges.
No assumptions on disorder, edge order, positivity of weights, or runtimes occur.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.SupportEvaluation

open Manuscript.FieldExpansion SpinGlass.Expansion

section Mobius
variable {V I R : Type*} [DecidableEq V] [CommRing R]

/-- The alternating sum over all subsets cancels unless the ground set is empty. -/
theorem alternating_powerset_sum (U : Finset V) :
    (∑ S ∈ U.powerset, (-1 : R) ^ S.card) = if U = ∅ then 1 else 0 := by
  have h := Finset.sum_pow_mul_eq_add_pow (-1 : R) 1 U
  simp only [one_pow, mul_one, neg_add_cancel] at h
  rw [h]
  by_cases hU : U = ∅ <;> simp [hU]

/-- Complementation converts the subsets containing `T` into subsets of `U \ T`. -/
theorem superset_alternating_sum (T U : Finset V) (hTU : T ⊆ U) :
    (∑ S ∈ U.powerset with T ⊆ S, (-1 : R) ^ (U.card - S.card)) =
      if T = U then 1 else 0 := by
  calc
    (∑ S ∈ U.powerset with T ⊆ S, (-1 : R) ^ (U.card - S.card)) =
        ∑ D ∈ (U \ T).powerset, (-1 : R) ^ D.card := by
      apply Finset.sum_bij (fun S _ => U \ S)
      · intro S hS
        exact Finset.mem_powerset.mpr
          (Finset.sdiff_subset_sdiff_right U (Finset.mem_filter.mp hS).2)
      · intro S hS W hW heq
        have hSU := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
        have hWU := Finset.mem_powerset.mp (Finset.mem_filter.mp hW).1
        have h := congrArg (fun B => U \ B) heq
        simpa only [Finset.sdiff_sdiff_eq_self hSU,
          Finset.sdiff_sdiff_eq_self hWU] using h
      · intro D hD
        have hDT : D ⊆ U \ T := Finset.mem_powerset.mp hD
        have hDU : D ⊆ U := Finset.Subset.trans hDT Finset.sdiff_subset
        refine ⟨U \ D, ?_, Finset.sdiff_sdiff_eq_self hDU⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
        intro v hv
        apply Finset.mem_sdiff.mpr
        refine ⟨hTU hv, ?_⟩
        intro hvD
        exact (Finset.mem_sdiff.mp (hDT hvD)).2 hv
      · intro S hS
        rw [Finset.card_sdiff_of_subset
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)]
    _ = if U \ T = ∅ then 1 else 0 := alternating_powerset_sum (U \ T)
    _ = if T = U then 1 else 0 := by
      by_cases hEq : T = U
      · simp [hEq]
      · have hne : U \ T ≠ ∅ := by
          intro hempty
          exact hEq (Finset.Subset.antisymm hTU
            (Finset.sdiff_eq_empty_iff_subset.mp hempty))
        simp [hne, hEq]

/-- The Möbius kernel isolates exactly one support, including outside supports. -/
theorem subset_cancellation (T U : Finset V) :
    (∑ S ∈ U.powerset,
      if T ⊆ S then (-1 : R) ^ (U.card - S.card) else 0) =
      if T = U then 1 else 0 := by
  by_cases hTU : T ⊆ U
  · simpa only [Finset.sum_filter] using
      (superset_alternating_sum (R := R) T U hTU)
  · have hsum : (∑ S ∈ U.powerset,
        if T ⊆ S then (-1 : R) ^ (U.card - S.card) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      apply if_neg
      intro hTS
      exact hTU (Finset.Subset.trans hTS (Finset.mem_powerset.mp hS))
    have hne : T ≠ U := by
      intro heq
      subst T
      exact hTU Finset.Subset.rfl
    simp [hsum, hne]

/-- Total weight of objects whose supports are contained in a prescribed set. -/
def containedSum [DecidableEq I] (family : Finset I) (support : I → Finset V)
    (weight : I → R) (U : Finset V) : R :=
  ∑ i ∈ family with support i ⊆ U, weight i

/-- Total weight of objects whose supports equal a prescribed set. -/
def exactSupportSum [DecidableEq I] (family : Finset I) (support : I → Finset V)
    (weight : I → R) (U : Finset V) : R :=
  ∑ i ∈ family with support i = U, weight i

/-- The paper's alternating subset transform. -/
def transform (G : Finset V → R) (U : Finset V) : R :=
  ∑ S ∈ U.powerset, (-1 : R) ^ (U.card - S.card) * G S

/-- Exact-support inversion for an arbitrary finite weighted family. -/
theorem transform_containedSum [DecidableEq I] (family : Finset I)
    (support : I → Finset V) (weight : I → R) (U : Finset V) :
    transform (containedSum family support weight) U =
      exactSupportSum family support weight U := by
  unfold transform containedSum exactSupportSum
  simp_rw [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (fun a : R => a * weight i)
    (subset_cancellation (R := R) (support i) U)
  simpa only [Finset.sum_mul, ite_mul, zero_mul, one_mul] using h


end Mobius

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The union of the vertices incident with the selected interactions. -/
def support (incidence : E → Finset V) (Γ : Finset E) : Finset V :=
  Γ.biUnion incidence

/-- Restrict interaction incidences to the local vertex type. -/
def localIncidence (incidence : E → Finset V) (U : Finset V) (e : E) : Finset U :=
  (incidence e).subtype (fun v => v ∈ U)

/-- Local spin assignments and the unused coordinates form the ambient cube. -/
def splitSpins (U : Finset V) :
    (V → Bool) ≃ (U → Bool) × ({v : V // v ∉ U} → Bool) :=
  Equiv.piEquivPiSubtypeProd (fun v => v ∈ U) (fun _ => Bool)

/-- Biased independent spin averaging commutes with restriction to a vertex set. -/
theorem fieldMean_restrict (h : ℝ) (U : Finset V) (f : (U → Bool) → ℝ) :
    fieldMean h (fun σ : V → Bool => f (fun v : U => σ v)) = fieldMean h f := by
  classical
  have hsplit : (∑ σ : V → Bool,
      (∏ v, spinWeight h (σ v)) * f (fun v : U => σ v)) =
      ∑ τ : (U → Bool) × ({v : V // v ∉ U} → Bool),
        ((∏ v : U, spinWeight h (τ.1 v)) *
          ∏ v : {v : V // v ∉ U}, spinWeight h (τ.2 v)) * f τ.1 := by
    apply Fintype.sum_equiv (splitSpins U)
    intro σ
    change (∏ v, spinWeight h (σ v)) * f (fun v : U => σ v) =
      ((∏ v : U, spinWeight h (σ v)) *
        ∏ v : {v : V // v ∉ U}, spinWeight h (σ v)) * f (fun v : U => σ v)
    convert congrArg (fun a : ℝ => a * f (fun v : U => σ v))
      (Fintype.prod_subtype_mul_prod_subtype (fun v => v ∈ U)
        (fun v => spinWeight h (σ v))).symm using 1
    congr 4
    exact Subsingleton.elim _ _
  unfold fieldMean
  rw [hsplit, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro τ hτ
  have hunused : (∑ υ : {v : V // v ∉ U} → Bool,
      ∏ v, spinWeight h (υ v)) = 1 := by
    simpa [fieldMean] using
      (fieldMean_one (V := {v : V // v ∉ U}) h)
  calc
    (∑ υ : {v : V // v ∉ U} → Bool,
      ((∏ v : U, spinWeight h (τ v)) * ∏ v, spinWeight h (υ v)) * f τ) =
        ((∏ v : U, spinWeight h (τ v)) * f τ) *
          ∑ υ : {v : V // v ∉ U} → Bool, ∏ v, spinWeight h (υ v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro υ hυ
      ring
    _ = _ := by rw [hunused, mul_one]

omit [Fintype V] [DecidableEq E] in
/-- A contained edge has the same spin character in local and ambient spins. -/
theorem edgeCharacter_restrict (incidence : E → Finset V) (U : Finset V)
    (e : E) (he : incidence e ⊆ U) (σ : V → Bool) :
    edgeCharacter (localIncidence incidence U) (fun v : U => σ v) e =
      edgeCharacter incidence σ e := by
  exact Finset.prod_subtype_of_mem (fun v => spinSign (σ v)) (fun v hv => he hv)

/-- Equation (28), expressed as a product of normalized single-spin weights. -/
def localG (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (U : Finset V) : ℝ :=
  fieldMean h (fun σ : U → Bool =>
    ∏ e ∈ edges.filter (fun e => incidence e ⊆ U),
      (1 + w e * edgeCharacter (localIncidence incidence U) σ e))

omit [Fintype V] [DecidableEq E] in
/-- The exact exponential-weight expression of equation (28), with only `|U|`
spin coordinates rather than the full ambient cube. -/
theorem localG_eq_exp_spin_sum (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (U : Finset V) :
    localG incidence edges h w U =
      (1 / (2 * Real.cosh h) ^ U.card) *
        ∑ σ : U → Bool, Real.exp (h * ∑ v : U, spinSign (σ v)) *
          ∏ e ∈ edges.filter (fun e => incidence e ⊆ U),
            (1 + w e * edgeCharacter (localIncidence incidence U) σ e) := by
  unfold localG fieldMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [spinWeight, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe, Finset.mul_sum, Real.exp_sum]
  ring

omit [DecidableEq E] in
/-- The local cube average equals the ambient biased average of the induced
interaction polynomial; all unused coordinates have been summed out. -/
theorem localG_eq_ambient (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (U : Finset V) :
    localG incidence edges h w U =
      fieldMean h (fun σ : V → Bool =>
        ∏ e ∈ edges.filter (fun e => incidence e ⊆ U),
          (1 + w e * edgeCharacter incidence σ e)) := by
  unfold localG
  rw [← fieldMean_restrict h U]
  congr 1
  funext σ
  apply Finset.prod_congr rfl
  intro e he
  rw [edgeCharacter_restrict incidence U e (Finset.mem_filter.mp he).2]

omit [Fintype V] [DecidableEq E] in
/-- Selecting induced edges is equivalent to selecting ambient edges whose
vertex union is contained in the local set. -/
theorem subset_induced_iff (incidence : E → Finset V) (edges Γ : Finset E)
    (U : Finset V) :
    Γ ⊆ edges.filter (fun e => incidence e ⊆ U) ↔
      Γ ⊆ edges ∧ support incidence Γ ⊆ U := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro e he
      exact (Finset.mem_filter.mp (h he)).1
    · rw [support, Finset.biUnion_subset]
      intro e he
      exact (Finset.mem_filter.mp (h he)).2
  · rintro ⟨hΓ, hU⟩ e he
    apply Finset.mem_filter.mpr
    exact ⟨hΓ he, (Finset.biUnion_subset.mp hU) e he⟩

omit [Fintype V] [DecidableEq E] in
/-- The finite families on both sides are literally the same indexed graphs. -/
theorem induced_graph_family (incidence : E → Finset V) (edges : Finset E)
    (U : Finset V) :
    (edges.filter (fun e => incidence e ⊆ U)).powerset =
      edges.powerset.filter (fun Γ => support incidence Γ ⊆ U) := by
  ext Γ
  simp only [Finset.mem_filter, Finset.mem_powerset, subset_induced_iff]

/-- The local spin expression sums exactly all graph weights with support in `U`.
This includes the field factor at every odd-degree vertex. -/
theorem localG_eq_containedSum (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (U : Finset V) :
    localG incidence edges h w U =
      containedSum edges.powerset (support incidence) (graphWeight incidence h w) U := by
  rw [localG_eq_ambient, FieldExpansion.graphical_expansion, induced_graph_family]
  rfl

/-- Möbius inversion of the actual local spin averages selects the exact support. -/
theorem transform_localG_eq_exact_support (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (U : Finset V) :
    transform (localG incidence edges h w) U =
      ∑ Γ ∈ edges.powerset with support incidence Γ = U, graphWeight incidence h w Γ := by
  have heq : localG incidence edges h w =
      containedSum edges.powerset (support incidence) (graphWeight incidence h w) := by
    funext S
    exact localG_eq_containedSum incidence edges h w S
  rw [heq, transform_containedSum]
  rfl

/-- Summing exact-support transforms over supports of size at most `k` gives
precisely the retained graph sum of Proposition 3.3, including the empty graph. -/
theorem retained_local_sum (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (k : ℕ) :
    (∑ U ∈ (Finset.univ : Finset V).powerset.filter (fun U => U.card ≤ k),
      transform (localG incidence edges h w) U) =
      ∑ Γ ∈ edges.powerset with (support incidence Γ).card ≤ k,
        graphWeight incidence h w Γ := by
  simp_rw [transform_localG_eq_exact_support]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  ext Γ
  simp


/-- The scalar inclusion-exclusion coefficient in equation (29). -/
def coefficient (N k s : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k - s) * ((N - s - 1).choose (k - s) : ℝ)

/-- Pascal cancellation gives the closed form of the alternating binomial sum
used to collapse the nested support transform. -/
theorem coefficient_eq_alternating_sum (N k s : ℕ) (hs : s ≤ k) (hk : k < N) :
    coefficient N k s =
      ∑ j ∈ Finset.range (k - s + 1), (-1 : ℝ) ^ j * ((N - s).choose j : ℝ) := by
  have hn : N - s - 1 + 1 = N - s := by omega
  have hi := (Int.alternating_sum_range_choose_eq_choose
    (n := N - s - 1) (m := k - s)).symm
  rw [hn] at hi
  unfold coefficient
  exact_mod_cast hi


omit [Fintype V] [DecidableEq E] in
/-- Removing a prescribed support reindexes its supersets by disjoint added
vertices, preserving the inclusion-exclusion exponent and cutoff. -/
theorem superset_sum_eq_complement_sum (Q S : Finset V) (k : ℕ)
    (hSQ : S ⊆ Q) (hk : S.card ≤ k) :
    (∑ U ∈ Q.powerset with U.card ≤ k ∧ S ⊆ U,
      (-1 : ℝ) ^ (U.card - S.card)) =
      ∑ D ∈ (Q \ S).powerset with D.card ≤ k - S.card, (-1 : ℝ) ^ D.card := by
  apply Finset.sum_bij (fun U _ => U \ S)
  · intro U hU
    have hUQ := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    have hUk := (Finset.mem_filter.mp hU).2.1
    have hSU := (Finset.mem_filter.mp hU).2.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff_left S hUQ), ?_⟩
    rw [Finset.card_sdiff_of_subset hSU]
    omega
  · intro U hU W hW heq
    have hSU := (Finset.mem_filter.mp hU).2.2
    have hSW := (Finset.mem_filter.mp hW).2.2
    have hh := congrArg (fun D => D ∪ S) heq
    simpa only [Finset.sdiff_union_of_subset hSU,
      Finset.sdiff_union_of_subset hSW] using hh
  · intro D hD
    have hDS := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
    have hDk := (Finset.mem_filter.mp hD).2
    have hdisj : Disjoint D S := Finset.disjoint_left.mpr (by
      intro v hvD hvS
      exact (Finset.mem_sdiff.mp (hDS hvD)).2 hvS)
    refine ⟨D ∪ S, ?_, Finset.union_sdiff_cancel_right hdisj⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.union_subset
      (Finset.Subset.trans hDS Finset.sdiff_subset) hSQ), ?_, Finset.subset_union_right⟩
    rw [Finset.card_union_of_disjoint hdisj]
    omega
  · intro U hU
    rw [Finset.card_sdiff_of_subset (Finset.mem_filter.mp hU).2.2]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- Grouping a truncated subset sum by its cardinality gives the alternating
binomial sum, with no enumeration or asymptotic assumption. -/
theorem bounded_alternating_powerset_sum (Q : Finset V) (m : ℕ) (hm : m ≤ Q.card) :
    (∑ D ∈ Q.powerset with D.card ≤ m, (-1 : ℝ) ^ D.card) =
      ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * (Q.card.choose j : ℝ) := by
  rw [Finset.sum_filter, Finset.sum_powerset]
  have hinner : ∀ j, (∑ D ∈ Q.powersetCard j,
      if D.card ≤ m then (-1 : ℝ) ^ D.card else 0) =
      if j ≤ m then (-1 : ℝ) ^ j * (Q.card.choose j : ℝ) else 0 := by
    intro j
    rw [Finset.sum_powersetCard j Q (fun n => if n ≤ m then (-1 : ℝ) ^ n else 0)]
    split_ifs <;> simp [nsmul_eq_mul, mul_comm]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

omit [Fintype V] [DecidableEq E] in
/-- The coefficient of a particular local spin average in the collected
support transform is exactly the stated inclusion-exclusion coefficient. -/
theorem superset_coefficient (Q S : Finset V) (k : ℕ)
    (hSQ : S ⊆ Q) (hs : S.card ≤ k) (hk : k < Q.card) :
    (∑ U ∈ Q.powerset with U.card ≤ k ∧ S ⊆ U,
      (-1 : ℝ) ^ (U.card - S.card)) = coefficient Q.card k S.card := by
  rw [superset_sum_eq_complement_sum Q S k hSQ hs]
  have hcard : (Q \ S).card = Q.card - S.card := Finset.card_sdiff_of_subset hSQ
  have hbound : k - S.card ≤ (Q \ S).card := by rw [hcard]; omega
  rw [bounded_alternating_powerset_sum (Q \ S) (k - S.card) hbound, hcard]
  exact (coefficient_eq_alternating_sum Q.card k S.card hs hk).symm


omit [Fintype V] [DecidableEq E] in
/-- Collecting the local averages in the nested Möbius transform evaluates each
local average once, with the explicit binomial coefficient from equation (29). -/
theorem collapsed_transform (Q : Finset V) (k : ℕ) (hk : k < Q.card)
    (G : Finset V → ℝ) :
    (∑ U ∈ Q.powerset.filter (fun U => U.card ≤ k), transform G U) =
      ∑ S ∈ Q.powerset.filter (fun S => S.card ≤ k), coefficient Q.card k S.card * G S := by
  let supports := Q.powerset.filter (fun S => S.card ≤ k)
  have hinner : ∀ U ∈ supports, transform G U =
      ∑ S ∈ supports, if S ⊆ U then (-1 : ℝ) ^ (U.card - S.card) * G S else 0 := by
    intro U hU
    have hUQ := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
    have hUk := (Finset.mem_filter.mp hU).2
    have hsub : U.powerset ⊆ supports := by
      intro S hS
      have hSU := Finset.mem_powerset.mp hS
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.Subset.trans hSU hUQ), (Finset.card_le_card hSU).trans hUk⟩
    calc
      transform G U = ∑ S ∈ U.powerset,
          if S ⊆ U then (-1 : ℝ) ^ (U.card - S.card) * G S else 0 := by
        unfold transform
        apply Finset.sum_congr rfl
        intro S hS
        rw [if_pos (Finset.mem_powerset.mp hS)]
      _ = ∑ S ∈ supports,
          if S ⊆ U then (-1 : ℝ) ^ (U.card - S.card) * G S else 0 := by
        apply Finset.sum_subset hsub
        intro S hS hnot
        exact if_neg (fun hSU => hnot (Finset.mem_powerset.mpr hSU))
  change (∑ U ∈ supports, transform G U) =
    ∑ S ∈ supports, coefficient Q.card k S.card * G S
  calc
    (∑ U ∈ supports, transform G U) =
        ∑ U ∈ supports, ∑ S ∈ supports,
          if S ⊆ U then (-1 : ℝ) ^ (U.card - S.card) * G S else 0 :=
      Finset.sum_congr rfl hinner
    _ = ∑ S ∈ supports, ∑ U ∈ supports,
          if S ⊆ U then (-1 : ℝ) ^ (U.card - S.card) * G S else 0 :=
      Finset.sum_comm
    _ = ∑ S ∈ supports, coefficient Q.card k S.card * G S := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSQ := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hSk := (Finset.mem_filter.mp hS).2
      rw [← superset_coefficient Q S k hSQ hSk hk, Finset.sum_mul]
      dsimp [supports]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro U hU
      split_ifs <;> simp_all

/-- The collapsed local-spin sum for arbitrary indexed mixed hyperedges and arbitrary real
weights: the collapsed local-spin evaluator equals the retained support sum. -/
theorem collapsed_local_sum (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) (k : ℕ) (hk : k < Fintype.card V) :
    (∑ S ∈ (Finset.univ : Finset V).powerset.filter (fun S => S.card ≤ k),
      coefficient (Fintype.card V) k S.card * localG incidence edges h w S) =
      ∑ Γ ∈ edges.powerset with (support incidence Γ).card ≤ k,
        graphWeight incidence h w Γ := by
  have hcard : k < (Finset.univ : Finset V).card := by simpa using hk
  have hh := collapsed_transform (Finset.univ : Finset V) k hcard
    (localG incidence edges h w)
  rw [Finset.card_univ] at hh
  rw [← hh]
  exact retained_local_sum incidence edges h w k

/-- In the full-support branch one local average is the complete graph sum. -/
theorem localG_univ (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (w : E → ℝ) :
    localG incidence edges h w Finset.univ =
      ∑ Γ ∈ edges.powerset, graphWeight incidence h w Γ := by
  rw [localG_eq_containedSum]
  simp [containedSum]

end Manuscript.SupportEvaluation
