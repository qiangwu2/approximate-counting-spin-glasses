import Manuscript.SKChargedPrimitiveExecution
import Manuscript.SKChargedAlgebraExecution
import Manuscript.SupportCoefficientExecution
import SpinGlass.ColoringProbability

/-! Counted coefficient extraction with computed inverse coloring probabilities. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKChargedExtractionExecution
open SpinGlass SpinGlass.ArithmeticEvaluation
open SpinGlass.SKCoefficient (Basis Coefficients card_basis)
open Manuscript.InputPreparation

def natPower (x : ℝ) : ℕ → Computation
  | 0 => literal 1
  | m+1 => mul (literal x) (natPower x m)

@[simp] theorem natPower_value (x : ℝ) (m : ℕ) : (natPower x m).value = x ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [natPower, mul, literal, ih, pow_succ, mul_comm]

@[simp] theorem natPower_operations (x : ℝ) (m : ℕ) : (natPower x m).operations = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [natPower, mul, literal, ih]

/-- The rational reweighting is computed from two elementary products. -/
def colorReciprocal (K m : ℕ) : Computation :=
  divide (natPower K m) (SupportCoefficientExecution.descending K m)

@[simp] theorem colorReciprocal_value (K m : ℕ) :
    (colorReciprocal K m).value = (ColoringProbability.probability K m)⁻¹ := by
  simp [colorReciprocal, divide, ColoringProbability.probability, inv_div]

@[simp] theorem colorReciprocal_operations (K m : ℕ) :
    (colorReciprocal K m).operations = 4*m+1 := by
  simp [colorReciprocal, divide]
  omega

/-- Each retained coordinate is read once; the color correction is an executed
arithmetic program, including when the palette is zero. -/
def extract {b K : ℕ} (f : Coefficients b K) (L : ℕ)
    (accepted : Finset (Fin b → CappedDegree)) : Computation :=
  sumFinset Finset.univ (fun z : Basis b K =>
    if z.1.val ≤ L ∧ z.2.2 ∈ accepted then
      mul (colorReciprocal K z.2.1.card) (literal (f z)) else literal 0)

@[simp] theorem extract_value {b K : ℕ} (f : Coefficients b K) (L : ℕ)
    (accepted : Finset (Fin b → CappedDegree)) :
    (extract f L accepted).value =
      ∑ m ∈ Finset.range (K+1), (ColoringProbability.probability K m)⁻¹ *
        (∑ k : Fin (K+1), ∑ S : Finset (Fin K), ∑ d ∈ accepted,
          if k.val ≤ L ∧ S.card = m then f (SKChargedMonomial.target k S d) else 0) := by
  simp only [extract, sumFinset_value, apply_ite, mul, literal, colorReciprocal_value,
    Fintype.sum_prod_type]
  symm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_comm]
  have hm : S.card ∈ Finset.range (K+1) := Finset.mem_range.mpr
    (Nat.lt_succ_of_le (by simpa using Finset.card_le_univ S))
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel]
  by_cases hkL : k.val ≤ L
  · simp [hkL, hm, SKChargedMonomial.target, Finset.sum_ite_mem]
  · simp [hkL]

theorem extract_operations_le {b K : ℕ} (f : Coefficients b K) (L : ℕ)
    (accepted : Finset (Fin b → CappedDegree)) :
    (extract f L accepted).operations ≤ (4*K+3) * SKOperationCount.registers b K := by
  rw [extract, sumFinset_operations]
  have hcell (z : Basis b K) :
      (if z.1.val ≤ L ∧ z.2.2 ∈ accepted then
        mul (colorReciprocal K z.2.1.card) (literal (f z)) else literal 0).operations ≤ 4*K+2 := by
    split_ifs
    · simp only [mul, literal, colorReciprocal_operations]
      have hs : z.2.1.card ≤ K := by simpa using Finset.card_le_univ z.2.1
      omega
    · simp [literal]
  calc
    _ ≤ (∑ _z : Basis b K, (4*K+2)) + Fintype.card (Basis b K) :=
      Nat.add_le_add_right (Finset.sum_le_sum (fun z _ => hcell z)) _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, card_basis,
        SKOperationCount.registers]
      ring

end Manuscript.SKChargedExtractionExecution
