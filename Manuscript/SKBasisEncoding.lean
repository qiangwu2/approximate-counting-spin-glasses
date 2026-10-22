import Manuscript.SKRestrictedAlgebra
import Mathlib.Algebra.BigOperators.Fin

/-! Explicit mixed-radix addresses for the actual SK coefficient basis.  These
equivalences identify the natural-register scans with every basis coordinate;
the encoding is binary for colors and base six for capped branch degrees. -/
noncomputable section
namespace Manuscript.SKBasisEncoding
open SpinGlass SKCoefficient
open scoped BigOperators

def subsetDigits (K : ℕ) : Finset (Fin K) ≃ (Fin K → Fin 2) where
  toFun S i := if i ∈ S then 1 else 0
  invFun f := Finset.univ.filter (fun i => f i = 1)
  left_inv S := by ext i; simp
  right_inv f := by
    funext i
    have h : f i = 0 ∨ f i = 1 := by have := (f i).isLt; omega
    rcases h with h | h <;> simp [h]

def maskEquiv (K : ℕ) : Finset (Fin K) ≃ Fin (2^K) :=
  (subsetDigits K).trans finFunctionFinEquiv

def degreeEquiv (b : ℕ) : (Fin b → CappedDegree) ≃ Fin (6^b) :=
  (Equiv.piCongrRight (fun _ => CappedDegree.equivFin)).trans finFunctionFinEquiv

def basisEquiv (b K : ℕ) : Basis b K ≃ Fin (((K+1)*2^K)*6^b) :=
  (Equiv.prodCongr (Equiv.refl (Fin (K+1)))
    (Equiv.prodCongr (maskEquiv K) (degreeEquiv b))).trans
    ((Equiv.prodAssoc (Fin (K+1)) (Fin (2^K)) (Fin (6^b))).symm.trans
      ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin (6^b)))).trans finProdFinEquiv))

def encode {b K : ℕ} (x : Basis b K) : ℕ := (basisEquiv b K x).val

theorem encode_injective (b K : ℕ) : Function.Injective (@encode b K) := by
  intro x y h
  exact (basisEquiv b K).injective (Fin.ext h)

theorem encode_lt {b K : ℕ} (x : Basis b K) : encode x < (K+1)*2^K*6^b :=
  (basisEquiv b K x).isLt

theorem encode_surjective (b K : ℕ) {i : ℕ} (hi : i < (K+1)*2^K*6^b) :
    ∃ x : Basis b K, encode x = i := by
  exact ⟨(basisEquiv b K).symm ⟨i, hi⟩, congrArg Fin.val ((basisEquiv b K).apply_symm_apply _)⟩

theorem mask_formula {K : ℕ} (S : Finset (Fin K)) :
    (maskEquiv K S).val = ∑ i : Fin K, if i ∈ S then 2^i.val else 0 := by
  change (∑ i : Fin K, ((if i ∈ S then 1 else 0 : Fin 2) : ℕ)*2^i.val) = _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [hi]

theorem degree_formula {b : ℕ} (d : Fin b → CappedDegree) :
    (degreeEquiv b d).val = ∑ i : Fin b, (d i).val * 6^i.val := rfl

theorem encode_formula {b K : ℕ} (x : Basis b K) :
    encode x = (x.1.val*2^K+(maskEquiv K x.2.1).val)*6^b+
      (degreeEquiv b x.2.2).val := by
  simp [encode, basisEquiv, finProdFinEquiv]
  ring

theorem degree_digit {b : ℕ} (d : Fin b → CappedDegree) (i : Fin b) :
    (degreeEquiv b d).val / 6^i.val % 6 = (d i).val := by
  have h := finFunctionFinEquiv_symm_apply_val
    (finFunctionFinEquiv (fun j : Fin b => (d j).toFin)) i
  change (finFunctionFinEquiv (fun j : Fin b => (d j).toFin)).val / 6^i.val % 6 = (d i).toFin.val
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem mask_digit {K : ℕ} (S : Finset (Fin K)) (i : Fin K) :
    (maskEquiv K S).val / 2^i.val % 2 = if i ∈ S then 1 else 0 := by
  have h := finFunctionFinEquiv_symm_apply_val
    (finFunctionFinEquiv ((subsetDigits K) S)) i
  change (finFunctionFinEquiv ((subsetDigits K) S)).val / 2^i.val % 2 = _
  by_cases hi : i ∈ S <;> simpa [subsetDigits, hi] using h.symm

theorem mask_disjoint_iff {K : ℕ} (S T : Finset (Fin K)) :
    Disjoint S T ↔ ∀ i : Fin K,
      ((maskEquiv K S).val / 2^i.val % 2)*((maskEquiv K T).val / 2^i.val % 2) = 0 := by
  simp only [mask_digit]
  constructor
  · intro h i
    by_cases hi : i ∈ S
    · have hni : i ∉ T := fun ht => Finset.disjoint_left.mp h hi ht
      simp [hi, hni]
    · simp [hi]
  · intro h
    apply Finset.disjoint_left.mpr
    intro i hi ht
    simpa [hi, ht] using h i

theorem mask_union {K : ℕ} (S T : Finset (Fin K)) (h : Disjoint S T) :
    (maskEquiv K (S ∪ T)).val = (maskEquiv K S).val+(maskEquiv K T).val := by
  rw [mask_formula, mask_formula, mask_formula, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · have hni : i ∉ T := fun ht => Finset.disjoint_left.mp h hi ht
    simp [hi, hni]
  · by_cases ht : i ∈ T <;> simp [hi, ht]

theorem degree_add_formula {b : ℕ} (d e : Fin b → CappedDegree) :
    (degreeEquiv b (fun i => d i+e i)).val =
      ∑ i : Fin b, SpinGlass.rho
        ((degreeEquiv b d).val/6^i.val%6+(degreeEquiv b e).val/6^i.val%6)*6^i.val := by
  simp only [degree_digit]
  exact degree_formula _

/-- Three consecutive, disjoint dense arrays, with no abstract enumeration. -/
def denseLayout (b K base : ℕ) : SKRestrictedAlgebra.Layout b K where
  left x := base+encode x
  right x := base+(K+1)*2^K*6^b+encode x
  out x := base+2*((K+1)*2^K*6^b)+encode x
  out_injective := by intro x y h; apply encode_injective b K; dsimp at h; omega
  left_ne_out := by intro x z h; have hx := encode_lt x; have hz := encode_lt z; omega
  right_ne_out := by intro x z h; have hx := encode_lt x; have hz := encode_lt z; omega

def basisList (b K : ℕ) : List (Basis b K) :=
  (List.finRange (((K+1)*2^K)*6^b)).map (basisEquiv b K).symm

def pairList (b K : ℕ) : List (Basis b K × Basis b K) :=
  (basisList b K).product (basisList b K)

theorem basisList_nodup (b K : ℕ) : (basisList b K).Nodup := by
  exact (List.nodup_finRange _).map (basisEquiv b K).symm.injective

theorem mem_basisList {b K : ℕ} (x : Basis b K) : x ∈ basisList b K := by
  apply List.mem_map.mpr
  exact ⟨basisEquiv b K x, List.mem_finRange _, (basisEquiv b K).symm_apply_apply x⟩

theorem pairList_permutation (b K : ℕ) :
    (pairList b K).Perm (Finset.univ : Finset (Basis b K × Basis b K)).toList := by
  apply (List.perm_ext_iff_of_nodup
    ((basisList_nodup b K).product (basisList_nodup b K)) (Finset.nodup_toList _)).mpr
  rintro ⟨x, y⟩
  simp [List.mem_product, mem_basisList]

end Manuscript.SKBasisEncoding
