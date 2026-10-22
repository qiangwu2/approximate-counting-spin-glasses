import SpinGlass.SKGraphMonomial

/-!
# Concrete graph monomials and coefficient extraction

The graph encoding records the number of charged distinct edges, outside color
set, signed edge-weight product, and reduced degree at each specified branch
vertex. Multiplication agrees with disjoint graph union and rejects color reuse.
-/

noncomputable section
namespace Manuscript.SKChargedMonomial
open SpinGlass

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open SKRing

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- Only physical edges are charged; ghost edges have charge false. -/
def edgeCount (charge : E → Bool) (Γ : Finset E) : ℕ := (Γ.filter fun e => charge e).card

@[simp] theorem edgeCount_union (charge : E → Bool) (Γ Δ : Finset E)
    (hd : Disjoint Γ Δ) : edgeCount charge (Γ ∪ Δ) = edgeCount charge Γ + edgeCount charge Δ := by
  unfold edgeCount
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

variable (charge : E → Bool)

/-- The outside vertex support of an actual edge family. -/
def outside (incidence : E → Finset V) (A : Finset V) (Γ : Finset E) : Finset V :=
  Γ.biUnion incidence \ A

/-- Outside colors, each represented once in the square-zero algebra. -/
def colors {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ : Finset E) : Finset (Fin L) :=
  (outside incidence A Γ).image χ

/-- The edge family uses no outside color more than once. -/
def Colorful {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ : Finset E) : Prop :=
  Set.InjOn χ (outside incidence A Γ)

/-- Actual reduced graph coordinate; the edge bound is the algebra's t cutoff. -/
def basis {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (Γ : Finset E) (hΓ : edgeCount charge Γ ≤ L) :
    SKCoefficient.Basis b L :=
  (⟨edgeCount charge Γ, Nat.lt_succ_of_le hΓ⟩, colors incidence A χ Γ,
    fun a => CappedDegree.ofNat (Expansion.degree incidence Γ (branch a)))

/-- Signed graph weight is the product over its distinct edges. -/
def weight (w : E → ℝ) (Γ : Finset E) : ℝ := ∏ e ∈ Γ, w e

/-- The graph monomial, including annihilation by budget or repeated color. -/
def value {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ : Finset E) : Element b L := by
  classical
  exact if hΓ : edgeCount charge Γ ≤ L then
    if Colorful incidence A χ Γ then monomial (basis charge incidence A branch χ Γ hΓ) (weight w Γ)
    else 0
  else 0

@[simp] theorem outside_union (incidence : E → Finset V) (A : Finset V) (Γ Δ : Finset E) :
    outside incidence A (Γ ∪ Δ) = outside incidence A Γ ∪ outside incidence A Δ := by
  ext v
  simp only [outside, Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨⟨e, he | he, hv⟩, ha⟩
    · exact Or.inl ⟨⟨e, he, hv⟩, ha⟩
    · exact Or.inr ⟨⟨e, he, hv⟩, ha⟩
  · rintro (⟨⟨e, he, hv⟩, ha⟩ | ⟨⟨e, he, hv⟩, ha⟩)
    · exact ⟨⟨e, Or.inl he, hv⟩, ha⟩
    · exact ⟨⟨e, Or.inr he, hv⟩, ha⟩

@[simp] theorem colors_union {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ Δ : Finset E) :
    colors incidence A χ (Γ ∪ Δ) = colors incidence A χ Γ ∪ colors incidence A χ Δ := by
  simp [colors, Finset.image_union]

/-- Distinct edge families add actual incidence degrees, including at branches. -/
theorem degree_union (incidence : E → Finset V) (Γ Δ : Finset E)
    (hd : Disjoint Γ Δ) (v : V) :
    Expansion.degree incidence (Γ ∪ Δ) v =
      Expansion.degree incidence Γ v + Expansion.degree incidence Δ v := by
  simp only [Expansion.degree, Finset.filter_union]
  exact Finset.card_union_of_disjoint (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

theorem weight_union (w : E → ℝ) (Γ Δ : Finset E) (hd : Disjoint Γ Δ) :
    weight w (Γ ∪ Δ) = weight w Γ * weight w Δ := Finset.prod_union hd

/-- Colorfulness of disjoint outside supports is exactly internal and cross compatibility. -/
theorem colorful_union_iff {L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (χ : V → Fin L) (Γ Δ : Finset E)
    (hd : Disjoint (outside incidence A Γ) (outside incidence A Δ)) :
    Colorful incidence A χ (Γ ∪ Δ) ↔ Colorful incidence A χ Γ ∧
      Colorful incidence A χ Δ ∧ Disjoint (colors incidence A χ Γ) (colors incidence A χ Δ) := by
  classical
  unfold Colorful
  rw [outside_union, Finset.coe_union, Set.injOn_union (by exact_mod_cast hd)]
  simp only [colors, Finset.disjoint_left, Finset.mem_image]
  constructor
  · rintro ⟨hΓ, hΔ, hcross⟩
    refine ⟨hΓ, hΔ, ?_⟩
    rintro c ⟨v, hv, rfl⟩ ⟨u, hu, heq⟩
    exact hcross v hv u hu heq.symm
  · rintro ⟨hΓ, hΔ, hcross⟩
    refine ⟨hΓ, hΔ, ?_⟩
    intro v hv u hu heq
    exact hcross ⟨v, hv, rfl⟩ ⟨u, hu, heq.symm⟩

/-- Surviving multiplication records the union's exact graph coordinate. -/
theorem combine_basis {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (Γ Δ : Finset E)
    (hd : Disjoint Γ Δ) (hΓ : edgeCount charge Γ ≤ L) (hΔ : edgeCount charge Δ ≤ L)
    (h : SKCoefficient.compatible (basis charge incidence A branch χ Γ hΓ)
      (basis charge incidence A branch χ Δ hΔ)) :
    SKCoefficient.combine (basis charge incidence A branch χ Γ hΓ)
      (basis charge incidence A branch χ Δ hΔ) h =
    basis charge incidence A branch χ (Γ ∪ Δ)
      (by rw [edgeCount_union charge Γ Δ hd]; exact h.1) := by
  apply Prod.ext
  · apply Fin.ext
    exact (edgeCount_union charge Γ Δ hd).symm
  · apply Prod.ext
    · exact (colors_union incidence A χ Γ Δ).symm
    · funext a
      exact (CappedDegree.ofNat_add _ _).symm.trans
        (congrArg CappedDegree.ofNat (degree_union incidence Γ Δ hd (branch a)).symm)

/-- Actual disjoint edge/outside-vertex union is exactly algebra multiplication.
No colorfulness assumption is needed: collisions are annihilated on both sides. -/
theorem value_mul {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ Δ : Finset E)
    (he : Disjoint Γ Δ)
    (hv : Disjoint (outside incidence A Γ) (outside incidence A Δ)) :
    value charge incidence A branch χ w Γ * value charge incidence A branch χ w Δ =
      value charge incidence A branch χ w (Γ ∪ Δ) := by
  classical
  have hcard := edgeCount_union charge Γ Δ he
  have hcolor := colorful_union_iff incidence A χ Γ Δ hv
  by_cases hΓ : edgeCount charge Γ ≤ L
  · by_cases hΔ : edgeCount charge Δ ≤ L
    · by_cases hcΓ : Colorful incidence A χ Γ
      · by_cases hcΔ : Colorful incidence A χ Δ
        · by_cases ht : edgeCount charge (Γ ∪ Δ) ≤ L
          · by_cases hc : Disjoint (colors incidence A χ Γ) (colors incidence A χ Δ)
            · have hcomp : SKCoefficient.compatible (basis charge incidence A branch χ Γ hΓ)
                  (basis charge incidence A branch χ Δ hΔ) := ⟨by simpa [basis, hcard] using ht, hc⟩
              have hcu := hcolor.mpr ⟨hcΓ, hcΔ, hc⟩
              simp only [value, dif_pos hΓ, dif_pos hΔ, if_pos hcΓ, if_pos hcΔ,
                dif_pos ht, if_pos hcu]
              apply ext
              change SKCoefficient.mul (SKCoefficient.single _ _) (SKCoefficient.single _ _) =
                SKCoefficient.single _ _
              rw [SKCoefficient.mul_single_single_accepted _ _ _ _ hcomp,
                combine_basis charge incidence A branch χ Γ Δ he hΓ hΔ hcomp,
                weight_union w Γ Δ he]
            · have hcu : ¬ Colorful incidence A χ (Γ ∪ Δ) := fun h => hc (hcolor.mp h).2.2
              simp only [value, dif_pos hΓ, dif_pos hΔ, if_pos hcΓ, if_pos hcΔ,
                dif_pos ht, if_neg hcu]
              apply ext
              apply SKCoefficient.mul_single_single_rejected
              exact fun h => hc h.2
          · simp only [value, dif_pos hΓ, dif_pos hΔ, if_pos hcΓ, if_pos hcΔ, dif_neg ht]
            apply ext
            apply SKCoefficient.mul_single_single_rejected
            intro h
            exact ht (by simpa [basis, hcard] using h.1)
        · have hcu : ¬ Colorful incidence A χ (Γ ∪ Δ) := fun h => hcΔ (hcolor.mp h).2.1
          simp [value, hΓ, hΔ, hcΔ, hcu]
      · have hcu : ¬ Colorful incidence A χ (Γ ∪ Δ) := fun h => hcΓ (hcolor.mp h).1
        simp [value, hΓ, hΔ, hcΓ, hcu]
    · have ht : ¬ edgeCount charge (Γ ∪ Δ) ≤ L := by omega
      simp [value, hΔ, ht]
  · have ht : ¬ edgeCount charge (Γ ∪ Δ) ≤ L := by omega
    simp [value, hΓ, ht]


/-- A target is allowed an arbitrary distinguished-vertex degree vector. -/
def target {b L : ℕ} (k : Fin (L + 1)) (S : Finset (Fin L))
    (d : Fin b → CappedDegree) : SKCoefficient.Basis b L := (k, S, d)

def degrees {b : ℕ} (incidence : E → Finset V) (branch : Fin b → V) (Γ : Finset E) :
    Fin b → CappedDegree := fun a => CappedDegree.ofNat (Expansion.degree incidence Γ (branch a))

theorem basis_eq_target_iff {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (Γ : Finset E) (hΓ : edgeCount charge Γ ≤ L)
    (k : Fin (L + 1)) (S : Finset (Fin L)) (d : Fin b → CappedDegree) :
    basis charge incidence A branch χ Γ hΓ = target k S d ↔
      edgeCount charge Γ = k.val ∧ colors incidence A χ Γ = S ∧ degrees incidence branch Γ = d := by
  constructor
  · intro h
    exact ⟨congrArg (fun z => z.1.val) h, congrArg (fun z => z.2.1) h,
      congrArg (fun z => z.2.2) h⟩
  · rintro ⟨hk, hS, hd⟩
    exact Prod.ext (Fin.ext hk) (Prod.ext hS hd)

/-- Ghost edges change the degree vector and weight, but not the charged
edge coordinate. Coefficient extraction sees exactly this distinction. -/
theorem value_coefficient {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ : Finset E)
    (k : Fin (L + 1)) (S : Finset (Fin L)) (d : Fin b → CappedDegree) :
    (value charge incidence A branch χ w Γ).coeff (target k S d) =
      if edgeCount charge Γ = k.val ∧ colors incidence A χ Γ = S ∧
        Colorful incidence A χ Γ ∧ degrees incidence branch Γ = d then weight w Γ else 0 := by
  classical
  by_cases hΓ : edgeCount charge Γ ≤ L
  · by_cases hc : Colorful incidence A χ Γ
    · simp [value, hΓ, hc, monomial, SKCoefficient.single, basis_eq_target_iff]
    · simp [value, hΓ, hc]
  · have hk : edgeCount charge Γ ≠ k.val := by have := k.isLt; omega
    simp [value, hΓ, hk]

/-- Extraction from any finite collection of degree states counts a graph once. -/
theorem value_coefficient_sum {b L : ℕ} (incidence : E → Finset V) (A : Finset V)
    (branch : Fin b → V) (χ : V → Fin L) (w : E → ℝ) (Γ : Finset E)
    (k : Fin (L + 1)) (S : Finset (Fin L)) (D : Finset (Fin b → CappedDegree)) :
    (∑ d ∈ D, (value charge incidence A branch χ w Γ).coeff (target k S d)) =
      if edgeCount charge Γ = k.val ∧ colors incidence A χ Γ = S ∧
        Colorful incidence A χ Γ ∧ degrees incidence branch Γ ∈ D then weight w Γ else 0 := by
  simp_rw [value_coefficient]
  by_cases hk : edgeCount charge Γ = k.val
  · by_cases hS : colors incidence A χ Γ = S
    · by_cases hc : Colorful incidence A χ Γ
      · simp [hk, hS, hc, eq_comm]
      · simp [hc]
    · simp [hS]
  · simp [hk]

/-- The three accepted states at the ghost and state four at every ordinary
distinguished vertex. The ghost is the first coordinate. -/
def ghostStates (b : ℕ) : Finset (Fin (b + 1) → CappedDegree) :=
  ({CappedDegree.ofNat 0, CappedDegree.ofNat 2, CappedDegree.ofNat 4} : Finset CappedDegree).image
    (fun d => Fin.cons d (fun _ : Fin b => CappedDegree.ofNat 4))

theorem mem_ghostStates_iff {b : ℕ} (d : Fin (b + 1) → CappedDegree) :
    d ∈ ghostStates b ↔
      (d 0 = CappedDegree.ofNat 0 ∨ d 0 = CappedDegree.ofNat 2 ∨ d 0 = CappedDegree.ofNat 4) ∧
        ∀ a : Fin b, d a.succ = CappedDegree.ofNat 4 := by
  constructor
  · intro h
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
    simpa using And.intro (by simpa using hs :
      s = CappedDegree.ofNat 0 ∨ s = CappedDegree.ofNat 2 ∨ s = CappedDegree.ofNat 4)
      (show ∀ _a : Fin b, CappedDegree.ofNat 4 = CappedDegree.ofNat 4 from fun _ => rfl)
  · rintro ⟨hs, hd⟩
    apply Finset.mem_image.mpr
    refine ⟨d 0, by simpa using hs, ?_⟩
    funext a
    refine Fin.cases ?_ (fun i => ?_) a
    · simp
    · simpa using (hd i).symm

theorem ghostStates_card (b : ℕ) : (ghostStates b).card = 3 := by
  rw [ghostStates, Finset.card_image_of_injective]
  · decide
  · intro d e h
    simpa using congrFun h 0

theorem capped_eq_four_iff (n : ℕ) :
    CappedDegree.ofNat n = CappedDegree.ofNat 4 ↔ 4 ≤ n ∧ Even n := by
  constructor
  · intro h
    have hh : rho n = 4 := by simpa using congrArg CappedDegree.val h
    exact ⟨(rho_eq_four_iff n).mp hh |>.1, Nat.even_iff.mpr ((rho_eq_four_iff n).mp hh).2⟩
  · rintro ⟨hn, he⟩
    apply CappedDegree.ext_val
    simpa using (rho_eq_four_iff n).mpr ⟨hn, Nat.even_iff.mp he⟩

theorem capped_even_states_iff (n : ℕ) :
    CappedDegree.ofNat n = CappedDegree.ofNat 0 ∨
      CappedDegree.ofNat n = CappedDegree.ofNat 2 ∨
      CappedDegree.ofNat n = CappedDegree.ofNat 4 ↔ Even n := by
  have hz : CappedDegree.ofNat n = CappedDegree.ofNat 0 ↔ rho n = 0 :=
    ⟨fun h => by simpa using congrArg CappedDegree.val h,
      fun h => CappedDegree.ext_val (by simpa using h)⟩
  have ht : CappedDegree.ofNat n = CappedDegree.ofNat 2 ↔ rho n = 2 :=
    ⟨fun h => by simpa using congrArg CappedDegree.val h,
      fun h => CappedDegree.ext_val (by simpa using h)⟩
  rw [hz, ht, capped_eq_four_iff, Nat.even_iff, rho_eq_small_iff n 0 (by decide),
    rho_eq_small_iff n 2 (by decide)]
  omega

theorem degrees_mem_ghostStates_iff {b : ℕ} (incidence : E → Finset V)
    (branch : Fin (b + 1) → V) (Γ : Finset E) :
    degrees incidence branch Γ ∈ ghostStates b ↔
      Even (Expansion.degree incidence Γ (branch 0)) ∧
        ∀ a : Fin b, 4 ≤ Expansion.degree incidence Γ (branch a.succ) ∧
          Even (Expansion.degree incidence Γ (branch a.succ)) := by
  rw [mem_ghostStates_iff]
  simp only [degrees]
  rw [capped_even_states_iff]
  simp only [capped_eq_four_iff]

end Manuscript.SKChargedMonomial
