import Manuscript.SKBasisEncoding
import Manuscript.RestrictedIndices
import Manuscript.SKMetadataGeneration

/-! Semantic identification of the runtime digit scanners with SK basis
multiplication. No compatibility test or output index is supplied as an oracle. -/
noncomputable section
namespace Manuscript.SKIndexSpecifications
open RestrictedMachine.IndexGeneration SKBasisEncoding
open SpinGlass SKCoefficient
open scoped BigOperators

def degreeSum (n x y : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, RestrictedMachine.IndexGeneration.rho
    (x/6^i%6+y/6^i%6)*6^i

theorem degreeSum_succ (n x y : ℕ) :
    degreeSum (n+1) x y = RestrictedMachine.IndexGeneration.rho (x%6+y%6)+
      6*degreeSum n (x/6) (y/6) := by
  unfold degreeSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one, Nat.mul_one]
  rw [Nat.add_comm]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  rw [show 6*6^i=6^(i+1) by rw [pow_succ]; omega]
  rw [pow_succ]
  ring

theorem degreeFold_eq_sum (n x y a w : ℕ) :
    degreeFold n x y a w = a+w*degreeSum n x y := by
  induction n generalizing x y a w with
  | zero => simp [degreeFold, degreeSum]
  | succ n ih => rw [degreeFold, ih, degreeSum_succ]; ring

def overlapSum (n x y : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (x/2^i%2)*(y/2^i%2)

theorem overlapSum_succ (n x y : ℕ) :
    overlapSum (n+1) x y = (x%2)*(y%2)+overlapSum n (x/2) (y/2) := by
  unfold overlapSum
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.div_div_eq_div_mul, pow_succ']

theorem overlapFold_eq_sum (n x y a : ℕ) :
    overlapFold n x y a = a+overlapSum n x y := by
  induction n generalizing x y a with
  | zero => simp [overlapFold, overlapSum]
  | succ n ih => rw [overlapFold, ih, overlapSum_succ]; omega

theorem rho_eq (n : ℕ) : RestrictedMachine.IndexGeneration.rho n = SpinGlass.rho n := by
  unfold RestrictedMachine.IndexGeneration.rho SpinGlass.rho
  by_cases hn : 4 ≤ n
  · simp [hn, show ¬n<4 by omega]
  · simp [hn, show n<4 by omega]

theorem degreeFold_add {b : ℕ} (d e : Fin b → CappedDegree) :
    degreeFold b (degreeEquiv b d).val (degreeEquiv b e).val 0 1 =
      (degreeEquiv b (fun i => d i+e i)).val := by
  rw [degreeFold_eq_sum]
  simp only [Nat.zero_add, Nat.one_mul, degreeSum, ← Fin.sum_univ_eq_sum_range]
  rw [degree_add_formula]
  apply Finset.sum_congr rfl
  intro i _
  rw [rho_eq]

theorem overlapFold_zero_iff {K : ℕ} (S T : Finset (Fin K)) :
    overlapFold K (maskEquiv K S).val (maskEquiv K T).val 0 = 0 ↔ Disjoint S T := by
  rw [overlapFold_eq_sum, Nat.zero_add]
  simp only [overlapSum, ← Fin.sum_univ_eq_sum_range, Finset.sum_eq_zero_iff,
    Finset.mem_univ, forall_const]
  exact (mask_disjoint_iff S T).symm

theorem overlapFold_self {K : ℕ} (S : Finset (Fin K)) :
    overlapFold K (maskEquiv K S).val (maskEquiv K S).val 0 = S.card := by
  rw [overlapFold_eq_sum]
  simp only [Nat.zero_add, overlapSum, ← Fin.sum_univ_eq_sum_range, mask_digit]
  have hf (i : Fin K) : (if i ∈ S then 1 else 0)*(if i ∈ S then 1 else 0) =
      (if i ∈ S then 1 else 0 : ℕ) := by split <;> rfl
  simp only [hf]
  simp

theorem mask_singleton {K : ℕ} (c : Fin K) : (maskEquiv K {c}).val = 2^c.val := by
  rw [mask_formula]
  simp

theorem mask_eq_singleton_iff {K : ℕ} (S : Finset (Fin K)) (c : Fin K) :
    (maskEquiv K S).val = 2^c.val ↔ S = {c} := by
  rw [← mask_singleton c]
  exact ⟨fun h => (maskEquiv K).injective (Fin.ext h), fun h => congrArg (fun U => (maskEquiv K U).val) h⟩

theorem mask_erase {K : ℕ} (S : Finset (Fin K)) (c : Fin K) (hc : c ∈ S) :
    (maskEquiv K S).val-2^c.val = (maskEquiv K (S.erase c)).val := by
  have h := mask_union (S.erase c) {c} (by simp)
  have hu : S.erase c ∪ {c} = S := by
    ext i
    by_cases hi : i = c <;> simp [hi, hc]
  rw [hu, mask_singleton] at h
  omega

theorem combine_encode {b K : ℕ} (x y : Basis b K) (h : compatible x y) :
    encode (combine x y h) =
      ((x.1.val+y.1.val)*2^K+(maskEquiv K x.2.1).val+(maskEquiv K y.2.1).val)*6^b+
        degreeFold b (degreeEquiv b x.2.2).val (degreeEquiv b y.2.2).val 0 1 := by
  rw [encode_formula, degreeFold_add]
  simp only [combine]
  rw [mask_union _ _ h.2]
  ring

theorem compatible_digit_test {b K : ℕ} (x y : Basis b K) :
    compatible x y ↔ x.1.val+y.1.val ≤ K ∧
      overlapFold K (maskEquiv K x.2.1).val (maskEquiv K y.2.1).val 0 = 0 := by
  rw [overlapFold_zero_iff]
  rfl

theorem encode_div_degree {b K : ℕ} (x : Basis b K) :
    encode x / 6^b = x.1.val*2^K+(maskEquiv K x.2.1).val := by
  rw [encode_formula, Nat.mul_comm _ (6^b), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (degreeEquiv b x.2.2).isLt, Nat.add_zero]

theorem encode_mod_degree {b K : ℕ} (x : Basis b K) :
    encode x % 6^b = (degreeEquiv b x.2.2).val := by
  rw [encode_formula, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (degreeEquiv b x.2.2).isLt]

theorem encode_charge {b K : ℕ} (x : Basis b K) :
    (encode x / 6^b) / 2^K = x.1.val := by
  rw [encode_div_degree, Nat.mul_comm _ (2^K), Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt (maskEquiv K x.2.1).isLt, Nat.add_zero]

theorem encode_mask {b K : ℕ} (x : Basis b K) :
    (encode x / 6^b) % 2^K = (maskEquiv K x.2.1).val := by
  rw [encode_div_degree, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (maskEquiv K x.2.1).isLt]

theorem writeRecord_values (m : ℕ → ℕ) (p : ℕ) (r : PairRecord) :
    writeRecord m p r p = r.accepted ∧
    writeRecord m p r (p+1) = r.left ∧
    writeRecord m p r (p+2) = r.right ∧
    writeRecord m p r (p+3) = r.target := by
  simp [writeRecord]

/-- Register layout for the actual natural arithmetic generator. -/
def Registers {b K : ℕ} (base : ℕ) (x y : Basis b K) (s : RestrictedMachine.State) : Prop :=
  s.natReg 140 = encode x ∧ s.natReg 141 = encode y ∧
  s.natReg 142 = 6^b ∧ s.natReg 143 = 2^K ∧ s.natReg 144 = K ∧
  s.natReg 145 = b ∧ s.natReg 146 = K ∧
  s.natReg 148 = base ∧ s.natReg 149 = base+(K+1)*2^K*6^b ∧
  s.natReg 150 = base+2*((K+1)*2^K*6^b)

theorem emitted_record_matches {b K : ℕ} (base : ℕ) (x y : Basis b K)
    (s : RestrictedMachine.State) (h : Registers base x y s) :
    SKRestrictedAlgebra.RecordMatches (denseLayout b K base)
      (writeRecord s.natMem (s.natReg 147) (pairRecord s)) (s.natReg 147) (x,y) := by
  rcases h with ⟨hx,hy,hq,hp,hcap,hb,hK,hl,hr,ho⟩
  obtain ⟨v0,v1,v2,v3⟩ := writeRecord_values s.natMem (s.natReg 147) (pairRecord s)
  have va : (pairRecord s).accepted =
      (if x.1.val+y.1.val ≤ K then 1 else 0)*
      (if Disjoint x.2.1 y.2.1 then 1 else 0) := by
    simp only [pairRecord, hx, hy, hq, hp, hcap, hK, encode_charge, encode_mask,
      overlapFold_zero_iff]
  have vl : (pairRecord s).left = (denseLayout b K base).left x := by
    simp [pairRecord, hl, hx, denseLayout]
  have vr : (pairRecord s).right = (denseLayout b K base).right y := by
    simp [pairRecord, hr, hy, denseLayout]
  by_cases hc : compatible x y
  · have vt : (pairRecord s).target = (denseLayout b K base).out (combine x y hc) := by
      simp only [pairRecord, hx, hy, hq, hp, hb, ho, encode_charge, encode_mask,
        encode_mod_degree, denseLayout]
      rw [combine_encode]
      ring
    simp only [SKRestrictedAlgebra.RecordMatches, basisMul, dif_pos hc]
    exact ⟨by rw [v0, va]; simp [hc.1, hc.2], v1.trans vl, v2.trans vr, v3.trans vt⟩
  · simp only [SKRestrictedAlgebra.RecordMatches, basisMul, dif_neg hc]
    rw [v0, va]
    unfold compatible at hc
    by_cases he : x.1.val+y.1.val ≤ K <;> simp_all

/-- The generated metadata is proved suitable for the actual scalar scatter
stage, directly from the fixed arithmetic program's execution. -/
theorem record_generation_realized {b K : ℕ} (params : RestrictedMachine.Parameters)
    (input : RestrictedMachine.Inputs) (base : ℕ) (x y : Basis b K)
    (s : RestrictedMachine.State) (h : Registers base x y s) :
    ∃ count t, RestrictedMachine.Exec params input pairProgram s count t ∧
      count ≤ 52*b+29*K+140 ∧
      SKRestrictedAlgebra.RecordMatches (denseLayout b K base) t.natMem (s.natReg 147) (x,y) ∧
      t.realMem = s.realMem ∧ t.natReg 147 = s.natReg 147+4 := by
  obtain ⟨count,t,he,hc,hptr,hmem⟩ := pair_execution params input s
  refine ⟨count,t,he,?_,?_,pair_realMem_frame params input s t count he,hptr⟩
  · rw [h.2.2.2.2.2.1, h.2.2.2.2.2.2.1] at hc
    exact hc
  · rw [hmem]
    exact emitted_record_matches base x y s h

end Manuscript.SKIndexSpecifications
