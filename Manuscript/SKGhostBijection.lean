import Manuscript.SKAugmentFinset

/-! The finite-edge augmentation bijection and its exact signed weights. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKAugmentFinset
open SpinGlass.Expansion Manuscript.FieldExpansion
variable {V : Type*} [Fintype V] [DecidableEq V]

def lowerEdge (e : Finset (Option V)) : Finset V := Finset.univ.filter (fun v => some v ∈ e)

def erase (Δ : Finset (Finset (Option V))) : Finset (Finset V) :=
  (Δ.filter (fun e => none ∉ e)).image lowerEdge

def ghostSupport (Δ : Finset (Finset (Option V))) : Finset V :=
  Finset.univ.filter (fun v => ghostEdge v ∈ Δ)

@[simp] theorem lower_lift (e : Finset V) : lowerEdge (liftEdge e) = e := by
  ext v
  simp [lowerEdge]

theorem lift_lower (e : Finset (Option V)) (he : none ∉ e) : liftEdge (lowerEdge e) = e := by
  ext v
  cases v <;> simp [lowerEdge,he]

@[simp] theorem lift_erase (Δ : Finset (Finset (Option V))) :
    (erase Δ).image liftEdge = Δ.filter (fun e => none ∉ e) := by
  unfold erase
  rw [Finset.image_image]
  ext e
  constructor
  · rintro he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    change liftEdge (lowerEdge f) ∈ _
    rw [lift_lower f (Finset.mem_filter.mp hf).2]
    exact hf
  · intro he
    exact Finset.mem_image.mpr ⟨e,he,lift_lower e (Finset.mem_filter.mp he).2⟩

@[simp] theorem erase_augment (Γ : Finset (Finset V)) : erase (augment Γ) = Γ := by
  unfold erase augment
  rw [Finset.filter_union,Finset.filter_image,Finset.filter_image]
  simp only [none_not_mem_liftEdge,Finset.filter_true,none_mem_ghostEdge,
    not_true_eq_false,Finset.filter_false,Finset.image_empty,Finset.union_empty]
  rw [Finset.image_image]
  simp [Function.comp_def]

theorem augment_injective : Function.Injective (augment : Finset (Finset V) → _) := by
  intro Γ Γ' h
  simpa using congrArg erase h

theorem pair_with_ghost (e : Finset (Option V)) (he : e.card = 2) (hn : none ∈ e) :
    ∃ v, e = ghostEdge v := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp he
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · cases y with
    | none => exact False.elim (hxy rfl)
    | some v => exact ⟨v,rfl⟩
  · cases x with
    | none => exact False.elim (hxy rfl)
    | some v => exact ⟨v,Finset.pair_comm _ _⟩

theorem ghost_part (Δ : Finset (Finset (Option V))) (hΔ : ∀ e ∈ Δ, e.card = 2) :
    (ghostSupport Δ).image ghostEdge = Δ.filter (fun e => none ∈ e) := by
  ext e
  constructor
  · rintro he
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).2,none_mem_ghostEdge v⟩
  · intro he
    obtain ⟨he,hn⟩ := Finset.mem_filter.mp he
    obtain ⟨v,rfl⟩ := pair_with_ghost e (hΔ e he) hn
    exact Finset.mem_image.mpr ⟨v,by simpa [ghostSupport] using he,rfl⟩

theorem split_parts (Δ : Finset (Finset (Option V))) (hΔ : ∀ e ∈ Δ, e.card = 2) :
    Δ = (erase Δ).image liftEdge ∪ (ghostSupport Δ).image ghostEdge := by
  rw [lift_erase,ghost_part Δ hΔ]
  ext e
  simp only [Finset.mem_union,Finset.mem_filter]
  tauto

theorem erase_simple (Δ : Finset (Finset (Option V))) (hΔ : ∀ e ∈ Δ, e.card = 2) :
    ∀ e ∈ erase Δ, e.card = 2 := by
  intro e he
  have hm : liftEdge e ∈ Δ := by
    have hi : liftEdge e ∈ (erase Δ).image liftEdge := Finset.mem_image.mpr ⟨e,he,rfl⟩
    rw [lift_erase] at hi
    exact (Finset.mem_filter.mp hi).1
  have hc := hΔ _ hm
  simpa only [liftEdge,Finset.card_image_of_injective _ (Option.some_injective V)] using hc

theorem degree_split_some (Δ : Finset (Finset (Option V)))
    (hΔ : ∀ e ∈ Δ, e.card = 2) (v : V) :
    degree id Δ (some v) = degree id (erase Δ) v + if v ∈ ghostSupport Δ then 1 else 0 := by
  conv_lhs => rw [split_parts Δ hΔ]
  rw [SKChargedMonomial.degree_union id _ _ (lift_ghost_disjoint _ _),
    degree_lift_some,degree_ghost_some]

/-- Evenness of the original vertices uniquely determines the entire ghost part. -/
theorem forced_ghostSupport (Δ : Finset (Finset (Option V)))
    (hΔ : ∀ e ∈ Δ, e.card = 2) (heven : ∀ v, Even (degree id Δ (some v))) :
    ghostSupport Δ = boundary id (erase Δ) := by
  ext v
  have he := Nat.even_iff.mp (heven v)
  rw [degree_split_some Δ hΔ v] at he
  simp only [boundary,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hv : v ∈ ghostSupport Δ
  · simp only [hv,if_true] at he
    simp only [hv,true_iff,Nat.even_iff]
    omega
  · simp only [hv,if_false,Nat.add_zero] at he
    simp [hv,Nat.even_iff,he]

/-- The actual augmented finite graph is reconstructed from the original edges;
no decomposition or existence premise is left in this inverse theorem. -/
theorem augment_erase (Δ : Finset (Finset (Option V)))
    (hΔ : ∀ e ∈ Δ, e.card = 2) (heven : ∀ v, Even (degree id Δ (some v))) :
    augment (erase Δ) = Δ := by
  rw [augment,← forced_ghostSupport Δ hΔ heven]
  exact (split_parts Δ hΔ).symm

def edgeWeight (h : ℝ) (w : Finset V → ℝ) (e : Finset (Option V)) : ℝ :=
  if none ∈ e then Real.tanh h else w (lowerEdge e)

@[simp] theorem edgeWeight_lift (h : ℝ) (w : Finset V → ℝ) (e : Finset V) :
    edgeWeight h w (liftEdge e) = w e := by simp [edgeWeight]

@[simp] theorem edgeWeight_ghost (h : ℝ) (w : Finset V → ℝ) (v : V) :
    edgeWeight h w (ghostEdge v) = Real.tanh h := by simp [edgeWeight]

/-- The original signed graph weight is exactly the product over augmented edges. -/
theorem weight_augment (Γ : Finset (Finset V)) (h : ℝ) (w : Finset V → ℝ) :
    (∏ e ∈ augment Γ, edgeWeight h w e) =
      Real.tanh h ^ (boundary id Γ).card * ∏ e ∈ Γ, w e := by
  rw [augment,Finset.prod_union (lift_ghost_disjoint Γ (boundary id Γ)),
    Finset.prod_image (fun _ _ _ _ heq => liftEdge_injective heq),
    Finset.prod_image (fun _ _ _ _ heq => ghostEdge_injective heq)]
  simp [mul_comm]

end Manuscript.SKAugmentFinset
