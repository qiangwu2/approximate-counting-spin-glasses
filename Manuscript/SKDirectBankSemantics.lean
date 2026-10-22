import Manuscript.SKDirectBank
import Manuscript.SKChargedTrialExecution

noncomputable section
namespace Manuscript.SKDirectBankSemantics
open SpinGlass SKCoefficient SKRing SKDirectBank
open scoped BigOperators

theorem segment_product {b K : ℕ} (f : ℕ → Coefficients b K) (i n : ℕ) :
    SKExponential.directProduct (SKDirectBank.segment f i n)=
      (∏ j∈Finset.range n, (1+(⟨f (i+j)⟩ : Element b K))).coeff := by
  induction n generalizing i with
  | zero => simp [SKDirectBank.segment,SKExponential.directProduct]
  | succ n ih =>
    rw [SKDirectBank.segment,SKExponential.directProduct,ih,Finset.prod_range_succ',_root_.mul_comm,coeff_mul]
    simp only [Nat.add_zero,coeff_add,coeff_one]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    congr 3
    omega

theorem pairs_equiv {b : ℕ} (i : Fin (b*b)) :
    pairs i=(finProdFinEquiv : Fin b × Fin b ≃ Fin (b*b)).symm i := by
  ext <;> rfl

theorem bank_product {V : Type*} [DecidableEq V] {b K : ℕ}
    (charge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ) :
    SKExponential.directProduct (SKDirectBank.segment (entry (K:=K) charge branch f) 0 (b*b))=
      (∏ p∈SKChargedExecution.directPairs b,
        (1+SKChargedExecution.direct (L:=K) charge branch f p.1 p.2)).coeff := by
  rw [segment_product]
  simp only [Nat.zero_add,←Fin.prod_univ_eq_prod_range]
  have hprod : (∏ i : Fin (b*b), (1+(⟨entry charge branch f i.val⟩ : Element b K)))=
      ∏ p : Fin b × Fin b, (1+if p.1<p.2 then
        SKChargedExecution.direct (L:=K) charge branch f p.1 p.2 else 0) := by
    apply Fintype.prod_equiv (finProdFinEquiv : Fin b × Fin b ≃ Fin (b*b)).symm
    intro i
    congr 1
    apply SKRing.ext
    by_cases h : i.divNat < i.modNat <;>
      simp [entry,i.isLt,SKDirectFactor.factor,pairs_equiv,h]
  rw [hprod]
  congr 1
  unfold SKChargedExecution.directPairs
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  split_ifs <;> simp

theorem loop_eq {V : Type*} [DecidableEq V] {b K : ℕ}
    (charge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ)
    (acc : Coefficients b K) :
    SKExponential.directLoop (SKDirectBank.segment (entry (K:=K) charge branch f) 0 (b*b)) acc=
      SKExponential.directLoop (SKChargedTrialExecution.directList charge branch f) acc := by
  rw [SKExponential.directLoop_correct,SKExponential.directLoop_correct,bank_product]
  have h := SKPrimitiveExpansion.directProduct_eq
    ((SKChargedExecution.directPairs b).toList.map
      (fun p => SKChargedExecution.direct (L:=K) charge branch f p.1 p.2))
  simp only [List.map_map,Function.comp_def,Finset.prod_map_toList] at h
  rw [SKChargedTrialExecution.directList,h]

@[simp] theorem segment_length {b K : ℕ} (f : ℕ → Coefficients b K) (i n : ℕ) :
    (SKDirectBank.segment f i n).length=n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [SKDirectBank.segment,ih]

end Manuscript.SKDirectBankSemantics
