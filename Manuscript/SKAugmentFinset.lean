import Manuscript.SKGraphBasics
import Manuscript.SKChargedMonomial
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Actual finite-edge ghost augmentation, preserving original-edge charging. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKAugmentFinset
open SpinGlass.Expansion Manuscript.FieldExpansion
variable {V : Type*} [Fintype V] [DecidableEq V]

def liftEdge (e : Finset V) : Finset (Option V) := e.image some

def ghostEdge (v : V) : Finset (Option V) := {none, some v}

def augment (Γ : Finset (Finset V)) : Finset (Finset (Option V)) :=
  Γ.image liftEdge ∪ (boundary id Γ).image ghostEdge

def charge (e : Finset (Option V)) : Bool := decide (none ∉ e)

@[simp] theorem some_mem_liftEdge (v : V) (e : Finset V) :
    some v ∈ liftEdge e ↔ v ∈ e := by simp [liftEdge]

@[simp] theorem none_not_mem_liftEdge (e : Finset V) : none ∉ liftEdge e := by simp [liftEdge]

@[simp] theorem some_mem_ghostEdge (v w : V) : some v ∈ ghostEdge w ↔ v = w := by
  simp [ghostEdge]

@[simp] theorem none_mem_ghostEdge (v : V) : none ∈ ghostEdge v := by simp [ghostEdge]

theorem liftEdge_injective : Function.Injective (liftEdge : Finset V → Finset (Option V)) := by
  intro e f hef
  ext v
  rw [← some_mem_liftEdge v e, hef, some_mem_liftEdge]

theorem ghostEdge_injective : Function.Injective (ghostEdge : V → Finset (Option V)) := by
  intro v w h
  have hm : some v ∈ ghostEdge w := h ▸ (by simp)
  simpa using hm

theorem lift_ghost_disjoint (Γ : Finset (Finset V)) (S : Finset V) :
    Disjoint (Γ.image liftEdge) (S.image ghostEdge) := by
  apply Finset.disjoint_left.mpr
  rintro e he hS
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨v,hv,hvf⟩ := Finset.mem_image.mp hS
  exact none_not_mem_liftEdge f (hvf ▸ none_mem_ghostEdge v)

theorem degree_lift_some (Γ : Finset (Finset V)) (v : V) :
    degree id (Γ.image liftEdge) (some v) = degree id Γ v := by
  unfold degree
  rw [Finset.filter_image]
  simpa only [id_eq, some_mem_liftEdge] using
    Finset.card_image_of_injective (Γ.filter (fun e => v ∈ e)) liftEdge_injective

theorem degree_lift_none (Γ : Finset (Finset V)) :
    degree id (Γ.image liftEdge) none = 0 := by
  unfold degree
  rw [Finset.filter_image]
  simp

theorem degree_ghost_some (S : Finset V) (v : V) :
    degree id (S.image ghostEdge) (some v) = if v ∈ S then 1 else 0 := by
  unfold degree
  rw [Finset.filter_image]
  simp only [id_eq, some_mem_ghostEdge]
  rw [Finset.card_image_of_injective _ ghostEdge_injective]
  by_cases hv : v ∈ S
  · have heq : S.filter (fun w => v = w) = {v} := by ext w; simp; aesop
    rw [heq]
    simp [hv]
  · have heq : S.filter (fun w => v = w) = ∅ := by ext w; simp; aesop
    rw [heq]
    simp [hv]

theorem degree_ghost_none (S : Finset V) :
    degree id (S.image ghostEdge) none = S.card := by
  unfold degree
  rw [Finset.filter_image]
  simpa using Finset.card_image_of_injective S ghostEdge_injective

/-- The extra field edge changes exactly the odd original degrees. -/
theorem degree_augment_some (Γ : Finset (Finset V)) (v : V) :
    degree id (augment Γ) (some v) = degree id Γ v + if ¬Even (degree id Γ v) then 1 else 0 := by
  rw [augment, SKChargedMonomial.degree_union id _ _ (lift_ghost_disjoint Γ (boundary id Γ)),
    degree_lift_some, degree_ghost_some]
  simp [boundary]

/-- The ghost degree is the number of odd original vertices. -/
theorem degree_augment_none (Γ : Finset (Finset V)) :
    degree id (augment Γ) none = (boundary id Γ).card := by
  rw [augment, SKChargedMonomial.degree_union id _ _ (lift_ghost_disjoint Γ (boundary id Γ)),
    degree_lift_none, degree_ghost_none, zero_add]

theorem boundary_even (Γ : Finset (Finset V)) (hΓ : ∀ e ∈ Γ, e.card = 2) :
    Even (boundary id Γ).card := by
  have hs : ∑ v : V, degree id Γ v = 2 * Γ.card := by
    rw [SupportDegrees.sum_degrees, SKGraph.pair_totalDegree id Γ hΓ]
  have hz := congrArg (fun n : ℕ => (n : ZMod 2)) hs
  simp only [Nat.cast_sum,Nat.cast_mul,ZMod.natCast_self,zero_mul] at hz
  rw [← Finset.sum_filter_ne_zero] at hz
  rw [Finset.sum_congr (g := fun _v => (1 : ZMod 2)) rfl] at hz
  · simp only [Finset.sum_const, nsmul_eq_mul,mul_one] at hz
    rw [← ZMod.natCast_eq_zero_iff_even]
    convert hz using 1
    congr 2
    ext v
    simp [boundary,ZMod.natCast_eq_zero_iff_even]
  · intro v hv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv
    exact ZMod.natCast_eq_one_iff_odd.mpr
      (Nat.not_even_iff_odd.mp (ZMod.natCast_eq_zero_iff_even.not.mp hv))

theorem even_degree_augment (Γ : Finset (Finset V)) (hΓ : ∀ e ∈ Γ, e.card = 2)
    (v : Option V) : Even (degree id (augment Γ) v) := by
  cases v with
  | none => rw [degree_augment_none]; exact boundary_even Γ hΓ
  | some v =>
    rw [degree_augment_some]
    by_cases hv : Even (degree id Γ v)
    · simpa [hv] using hv
    · simp only [hv,not_false_eq_true,if_true]
      exact (Nat.not_even_iff_odd.mp hv).add_odd (by decide)

theorem branching_iff (Γ : Finset (Finset V)) (v : V) :
    v ∈ SKGraph.branch id Γ ↔ 4 ≤ degree id (augment Γ) (some v) := by
  rw [SKGraph.mem_branch,degree_augment_some]
  by_cases hv : Even (degree id Γ v)
  · simp only [hv,not_true_eq_false,if_false,Nat.add_zero]
    have := Nat.even_iff.mp hv
    omega
  · simp only [hv,not_false_eq_true,if_true]
    omega

/-- Charging excludes every new field edge and keeps every original edge. -/
theorem edgeCount_augment (Γ : Finset (Finset V)) :
    SKChargedMonomial.edgeCount charge (augment Γ) = Γ.card := by
  unfold SKChargedMonomial.edgeCount augment
  rw [Finset.filter_union,Finset.filter_image,Finset.filter_image]
  simp [charge,Finset.card_image_of_injective _ liftEdge_injective]


end Manuscript.SKAugmentFinset
