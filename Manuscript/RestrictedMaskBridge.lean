import Manuscript.RestrictedMaskArithmetic
import Manuscript.SKBasisEncoding
import Manuscript.FieldExpansion

/-! Identification of integer-mask arithmetic with the manuscript's finite
vertex sets and spin characters. These are value theorems for the actual
digit-scanning programs, with no supplied character or product oracle. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedMaskBridge
open RestrictedMaskArithmetic SKBasisEncoding SpinGlass.Expansion

def encode {N : ℕ} (S : Finset (Fin N)) : ℕ := (maskEquiv N S).val
def spin {N : ℕ} (T : Finset (Fin N)) (v : Fin N) : Bool := decide (v∈T)

theorem encode_sum {N : ℕ} (S : Finset (Fin N)) : encode S=∑v∈S,2^v.val := by
  simp [encode,mask_formula]

theorem encode_digit {N : ℕ} (S : Finset (Fin N)) (v : Fin N) :
    encode S/2^v.val%2=if v∈S then 1 else 0 := mask_digit S v

theorem character_product (n e u t : ℕ) :
    character n e u t = ∏ j∈Finset.range n,
      characterFactor (e/2^j) (u/2^j) (t/2^j) := by
  induction n generalizing e u t with
  | zero => simp [character]
  | succ n ih =>
    rw [character,Finset.prod_range_succ']
    simp only [pow_zero,Nat.div_one]
    rw [ih]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Nat.div_div_eq_div_mul,pow_succ']

theorem field_product (plus minus : ℝ) (n u t : ℕ) :
    fieldProduct plus minus n u t = ∏ j∈Finset.range n,
      fieldFactor plus minus (u/2^j) (t/2^j) := by
  induction n generalizing u t with
  | zero => simp [fieldProduct]
  | succ n ih =>
    rw [fieldProduct,Finset.prod_range_succ']
    simp only [pow_zero,Nat.div_one]
    rw [ih]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Nat.div_div_eq_div_mul,pow_succ']

theorem character_mask_factor {N : ℕ} (E U T : Finset (Fin N)) (v : Fin N) :
    characterFactor (encode E/2^v.val) (encode U/2^v.val) (encode T/2^v.val)=
      if v∈E then (if v∈U then spinSign (spin T v) else 0) else 1 := by
  simp only [characterFactor,encode_digit]
  by_cases he : v∈E <;> by_cases hu : v∈U <;> by_cases ht : v∈T <;>
    norm_num [he,hu,ht,spin,spinSign]

theorem character_finset {N : ℕ} (E U T : Finset (Fin N)) :
    character N (encode E) (encode U) (encode T)=
      if E⊆U then ∏v∈E,spinSign (spin T v) else 0 := by
  rw [character_product,←Fin.prod_univ_eq_prod_range]
  simp_rw [character_mask_factor]
  rw [Finset.prod_ite_mem,Finset.univ_inter]
  by_cases h : E⊆U
  · simp only [if_pos h]
    apply Finset.prod_congr rfl
    intro v hv
    rw [if_pos (h hv)]
  · simp only [if_neg h]
    obtain ⟨v,hv,hu⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hv
    simp [hu]

theorem field_mask_factor {N : ℕ} (U T : Finset (Fin N)) (v : Fin N) (plus minus : ℝ) :
    fieldFactor plus minus (encode U/2^v.val) (encode T/2^v.val)=
      if v∈U then (if v∈T then minus else plus) else 1 := by
  simp only [fieldFactor,encode_digit]
  by_cases hu : v∈U <;> by_cases ht : v∈T <;> simp [hu,ht]

theorem field_finset {N : ℕ} (U T : Finset (Fin N)) (plus minus : ℝ) :
    fieldProduct plus minus N (encode U) (encode T)=
      ∏v∈U,if v∈T then minus else plus := by
  rw [field_product,←Fin.prod_univ_eq_prod_range]
  simp_rw [field_mask_factor]
  rw [Finset.prod_ite_mem]
  simp

theorem field_spinWeight {N : ℕ} (U T : Finset (Fin N)) (h : ℝ) :
    fieldProduct (FieldExpansion.spinWeight h false) (FieldExpansion.spinWeight h true)
      N (encode U) (encode T)=∏v∈U,FieldExpansion.spinWeight h (spin T v) := by
  rw [field_finset]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases ht : v∈T <;> simp [spin,ht]

theorem character_edge {N : ℕ} {E : Type*} (incidence : E→Finset (Fin N))
    (e : E) (U T : Finset (Fin N)) :
    character N (encode (incidence e)) (encode U) (encode T)=
      if incidence e⊆U then edgeCharacter incidence (spin T) e else 0 :=
  character_finset (incidence e) U T

end Manuscript.RestrictedMaskBridge
