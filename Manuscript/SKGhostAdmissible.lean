import Manuscript.SKGhostBijection
import Manuscript.SKChargedGraphSum
import Manuscript.SKBranchingFinite

/-! Exact degree-state characterization of the augmented original graph family. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKGhostAdmissible
open SpinGlass SpinGlass.Expansion SKActualEvaluator SKChargedMonomial
open SKAugmentFinset
variable {V : Type*} [Fintype V] [DecidableEq V]
attribute [local instance] Classical.propDecidable

def distinguished (A : Finset V) : Finset (Option V) := insert none (A.image some)

@[simp] theorem none_mem_distinguished (A : Finset V) : none ∈ distinguished A := by
  simp [distinguished]

@[simp] theorem some_mem_distinguished (A : Finset V) (v : V) :
    some v ∈ distinguished A ↔ v ∈ A := by simp [distinguished]

@[simp] theorem distinguished_card (A : Finset V) : (distinguished A).card = A.card + 1 := by
  simp [distinguished,Finset.card_image_of_injective _ (Option.some_injective V)]

/-- Three even ghost states and state four at each original distinguished vertex.
The labels come from the actual finite set, so the ghost may occupy any index. -/
def accepted (A : Finset V) : Finset (Fin (distinguished A).card → CappedDegree) :=
  Finset.univ.filter (fun d => ∀ i, if branch (distinguished A) i = none then
    d i = CappedDegree.ofNat 0 ∨ d i = CappedDegree.ofNat 2 ∨ d i = CappedDegree.ofNat 4
    else d i = CappedDegree.ofNat 4)

/-- Exactly one label denotes the ghost, so at most three degree vectors pass. -/
theorem accepted_card_le_three (A : Finset V) : (accepted A).card ≤ 3 := by
  obtain ⟨i0,hi0⟩ := (branch_range (distinguished A) none).mp (none_mem_distinguished A)
  have hinj : Set.InjOn (fun d : Fin (distinguished A).card → CappedDegree => d i0) (accepted A) := by
    intro d hd e he hde
    funext i
    have hd' := (Finset.mem_filter.mp hd).2 i
    have he' := (Finset.mem_filter.mp he).2 i
    by_cases hi : branch (distinguished A) i = none
    · have hii : i = i0 := branch_injective (distinguished A) (hi.trans hi0.symm)
      simpa only [hii] using hde
    · rw [if_neg hi] at hd' he'
      exact hd'.trans he'.symm
  have hsub : (accepted A).image (fun d => d i0) ⊆
      {CappedDegree.ofNat 0,CappedDegree.ofNat 2,CappedDegree.ofNat 4} := by
    intro q hq
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hq
    have hi := (Finset.mem_filter.mp hd).2 i0
    simpa only [hi0,if_true,Finset.mem_insert,Finset.mem_singleton] using hi
  calc
    (accepted A).card = ((accepted A).image (fun d => d i0)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ ({CappedDegree.ofNat 0,CappedDegree.ofNat 2,CappedDegree.ofNat 4} : Finset CappedDegree).card :=
      Finset.card_le_card hsub
    _ ≤ 3 := by
      apply (Finset.card_insert_le _ _).trans
      apply Nat.add_le_add_right
      apply (Finset.card_insert_le _ _).trans
      simp

theorem degrees_accepted_iff (A : Finset V) (Δ : Finset (Finset (Option V))) :
    degrees id (branch (distinguished A)) Δ ∈ accepted A ↔
      ∀ x ∈ distinguished A, Even (degree id Δ x) ∧ (x ≠ none → 4 ≤ degree id Δ x) := by
  simp only [accepted,Finset.mem_filter,Finset.mem_univ,true_and,degrees]
  constructor
  · intro hd x hx
    obtain ⟨i,rfl⟩ := (branch_range (distinguished A) x).mp hx
    have hi := hd i
    by_cases he : branch (distinguished A) i = none
    · rw [if_pos he] at hi
      exact ⟨(capped_even_states_iff _).mp hi,by simp [he]⟩
    · rw [if_neg he] at hi
      have hh := (capped_eq_four_iff _).mp hi
      exact ⟨hh.2,fun _ => hh.1⟩
  · intro hd i
    have hi := hd (branch (distinguished A) i) (branch_mem _ _)
    by_cases he : branch (distinguished A) i = none
    · rw [if_pos he]
      exact (capped_even_states_iff _).mpr hi.1
    · rw [if_neg he]
      exact (capped_eq_four_iff _).mpr ⟨hi.2 he,hi.1⟩

theorem augment_simple (Γ : Finset (Finset V)) (hΓ : ∀ e ∈ Γ, e.card = 2) :
    ∀ e ∈ augment Γ, e.card = 2 := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨f,hf,heq⟩ := Finset.mem_image.mp he
    rw [← heq]
    simpa only [liftEdge,Finset.card_image_of_injective _ (Option.some_injective V)] using hΓ f hf
  · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    simp [ghostEdge]

theorem degree_pos_augment_iff (Γ : Finset (Finset V)) (v : V) :
    0 < degree id (augment Γ) (some v) ↔ 0 < degree id Γ v := by
  rw [degree_augment_some]
  by_cases hv : degree id Γ v = 0
  · simp [hv]
  · omega

/-- The colored outside vertices are exactly the original support outside A. -/
theorem outside_augment (A : Finset V) (Γ : Finset (Finset V)) :
    SKChargedMonomial.outside id (distinguished A) (augment Γ) =
      (SupportEvaluation.support id Γ \ A).image some := by
  ext x
  cases x with
  | none => simp [SKChargedMonomial.outside]
  | some v =>
    change (some v ∈ SupportEvaluation.support id (augment Γ) \ distinguished A) ↔ _
    simp only [Finset.mem_sdiff,some_mem_distinguished,Finset.mem_image,Option.some_inj]
    rw [← SupportDegrees.degree_pos_iff_mem_support,degree_pos_augment_iff,
      SupportDegrees.degree_pos_iff_mem_support]
    simp only [exists_eq_right]

/-- Unused outside vertices have degree zero and used ones have degree two. -/
theorem outside_degree_cases (A : Finset (Option V)) (Δ : Finset (Finset (Option V)))
    (hΔ : SKColorfulGraphSum.GraphCondition A Δ) (x : Option V) (hx : x ∉ A) :
    degree id Δ x = 0 ∨ degree id Δ x = 2 := by
  by_cases hu : x ∈ SupportEvaluation.support id Δ
  · exact Or.inr (hΔ.2 x (Finset.mem_sdiff.mpr ⟨hu,hx⟩))
  · exact Or.inl (SupportDegrees.degree_zero_of_not_mem_support id Δ x hu)

def Admissible (A : Finset V) (Δ : Finset (Finset (Option V))) : Prop :=
  SKColorfulGraphSum.GraphCondition (distinguished A) Δ ∧
    degrees id (branch (distinguished A)) Δ ∈ accepted A

theorem augment_admissible (A : Finset V) (Γ : Finset (Finset V))
    (hΓ : ∀ e ∈ Γ, e.card = 2) (hbranch : SKGraph.branch id Γ = A) :
    Admissible A (augment Γ) := by
  have heven := even_degree_augment Γ hΓ
  refine ⟨⟨augment_simple Γ hΓ,?_⟩,?_⟩
  · intro x hx
    have hxA : x ∉ distinguished A := (Finset.mem_sdiff.mp hx).2
    have hpos : 0 < degree id (augment Γ) x :=
      (SupportDegrees.degree_pos_iff_mem_support id (augment Γ) x).mpr (Finset.mem_sdiff.mp hx).1
    cases x with
    | none => exact False.elim (hxA (none_mem_distinguished A))
    | some v =>
      have hvA : v ∉ SKGraph.branch id Γ := by simpa [hbranch] using hxA
      have hsmall : ¬4 ≤ degree id (augment Γ) (some v) := by
        exact fun h => hvA ((branching_iff Γ v).mpr h)
      have he := Nat.even_iff.mp (heven (some v))
      omega
  · rw [degrees_accepted_iff]
    intro x hx
    refine ⟨heven x,?_⟩
    intro hxn
    cases x with
    | none => exact False.elim (hxn rfl)
    | some v =>
      apply (branching_iff Γ v).mp
      rw [hbranch]
      exact (some_mem_distinguished A v).mp hx

theorem admissible_even (A : Finset V) (Δ : Finset (Finset (Option V)))
    (hΔ : Admissible A Δ) (x : Option V) : Even (degree id Δ x) := by
  by_cases hx : x ∈ distinguished A
  · exact ((degrees_accepted_iff A Δ).mp hΔ.2 x hx).1
  · rcases outside_degree_cases _ Δ hΔ.1 x hx with h | h <;> simp [h]

theorem admissible_erase_branch (A : Finset V) (Δ : Finset (Finset (Option V)))
    (hΔ : Admissible A Δ) : SKGraph.branch id (erase Δ) = A := by
  have he := augment_erase Δ hΔ.1.1 (fun v => admissible_even A Δ hΔ (some v))
  ext v
  rw [branching_iff,he]
  constructor
  · intro hv
    by_contra hvA
    have hx : some v ∉ distinguished A := by simpa using hvA
    rcases outside_degree_cases _ Δ hΔ.1 (some v) hx with hd | hd <;> omega
  · intro hv
    exact ((degrees_accepted_iff A Δ).mp hΔ.2 (some v)
      ((some_mem_distinguished A v).mpr hv)).2 (by simp)

/-- Exact two-sided correspondence for the family enumerated by degree extraction. -/
theorem admissible_iff (A : Finset V) (Δ : Finset (Finset (Option V))) :
    Admissible A Δ ↔ ∃ Γ, Γ ∈ SKBranching.branchFamily A ∧ augment Γ = Δ := by
  constructor
  · intro hΔ
    refine ⟨erase Δ,?_,augment_erase Δ hΔ.1.1 (fun v => admissible_even A Δ hΔ (some v))⟩
    refine Finset.mem_filter.mpr ⟨?_,admissible_erase_branch A Δ hΔ⟩
    apply Finset.mem_powerset.mpr
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,erase_simple Δ hΔ.1.1 e he⟩
  · rintro ⟨Γ,hΓ,rfl⟩
    exact augment_admissible A Γ (SKBranching.branchFamily_simple A hΓ) (Finset.mem_filter.mp hΓ).2

theorem admissible_family (A : Finset V) :
    (Finset.univ.filter (Admissible A) : Finset (Finset (Finset (Option V)))) =
      (SKBranching.branchFamily A).image augment := by
  ext Δ
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,admissible_iff]

end Manuscript.SKGhostAdmissible
