import Manuscript.SKBranchingScalar

/-! Integrating the weak-field Gaussian degree majorant. -/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKBranching

open MeasureTheory SpinGlass.SKBranching

theorem gaussianMean_add (f g : ℝ → ℝ) (hf : GaussianIntegrable f)
    (hg : GaussianIntegrable g) :
    gaussianMean (fun x => f x + g x) = gaussianMean f + gaussianMean g := by
  unfold gaussianMean
  simp_rw [add_mul]
  rw [integral_add hf hg]
  ring

theorem gaussianIntegrable_tilted_monomial (k : ℕ) {t : ℝ} (ht : t < 1) :
    GaussianIntegrable (fun x : ℝ => x ^ (2 * k) * Real.exp (t * x ^ 2 / 2)) := by
  unfold GaussianIntegrable
  convert integrable_even_gaussian k (b := (1 - t) / 2) (by linarith) using 1
  funext x
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

def gaussianPair (b : ℕ) (t x : ℝ) : ℝ :=
  Real.exp (t * x ^ 2 / 2) + x ^ (4 * b) * Real.exp (t * x ^ 2 / 2)

theorem gaussianPair_integrable (b : ℕ) {t : ℝ} (ht : t < 1) :
    GaussianIntegrable (gaussianPair b t) := by
  have h0 := gaussianIntegrable_tilted_monomial 0 ht
  have hb := gaussianIntegrable_tilted_monomial (2 * b) ht
  unfold GaussianIntegrable gaussianPair at *
  convert h0.add hb using 1
  · rfl
  · funext x
    simp only [Pi.add_apply, mul_zero, pow_zero, one_mul,
      show 2 * (2 * b) = 4 * b by omega, add_mul]

theorem gaussianPair_mean (b : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    gaussianMean (gaussianPair b (1 - δ)) =
      δ ^ (-(1 / 2 : ℝ)) + (Nat.doubleFactorial (4 * b - 1) : ℝ) *
        δ ^ (-((2 * b : ℕ) : ℝ) - 1 / 2) := by
  have ht : 1 - δ < 1 := by linarith
  have h0 := gaussianIntegrable_tilted_monomial 0 ht
  have hb := gaussianIntegrable_tilted_monomial (2 * b) ht
  have hm0 := gaussianMean_tilted_even_moment 0 ht
  have hmb := gaussianMean_tilted_even_moment (2 * b) ht
  simp only [mul_zero, pow_zero, one_mul, Nat.cast_zero, zero_add,
    show 1 - (1 - δ) = δ by ring] at hm0
  simp only [show 2 * (2 * b) = 4 * b by omega,
    show 1 - (1 - δ) = δ by ring] at hmb
  rw [show -((2 * b : ℕ) : ℝ) - 1 / 2 = -(((2 * b : ℕ) : ℝ) + 1 / 2) by ring]
  unfold gaussianPair
  rw [gaussianMean_add _ _ (by simpa using h0)
    (by simpa only [show 2 * (2 * b) = 4 * b by omega] using hb), hm0, hmb]
  norm_num

theorem gaussianPair_mean_le (b : ℕ) (hb : 0 < b) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    gaussianMean (gaussianPair b (1 - δ)) ≤
      2 * δ ^ (-(1 / 2 : ℝ)) * ((4 * (b : ℝ)) ^ (2 * b) / δ ^ (2 * b)) := by
  rw [gaussianPair_mean b hδ, SpinGlass.SKBranchingScalar.tilt_power_eq hδ]
  have hp := SpinGlass.SKBranchingScalar.four_doubleFactorial_le b
  have hδpow : 0 < δ ^ (2 * b) := pow_pos hδ _
  have hm : 0 ≤ δ ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hδ _).le
  have hbR : (1 : ℝ) ≤ 4 * (b : ℝ) := by exact_mod_cast (by omega : 1 ≤ 4 * b)
  have hbig : 1 ≤ (4 * (b : ℝ)) ^ (2 * b) / δ ^ (2 * b) := by
    apply (one_le_div hδpow).mpr
    exact pow_le_pow_left₀ hδ.le (hδ1.trans hbR) _
  have hbase := mul_le_mul_of_nonneg_left hbig hm
  have hterm := mul_le_mul_of_nonneg_right hp
    (div_nonneg hm hδpow.le)
  calc
    _ ≤ δ ^ (-(1 / 2 : ℝ)) * ((4 * (b : ℝ)) ^ (2 * b) / δ ^ (2 * b)) +
        δ ^ (-(1 / 2 : ℝ)) * ((4 * (b : ℝ)) ^ (2 * b) / δ ^ (2 * b)) := by
      apply add_le_add
      · simpa only [mul_one] using hbase
      · convert hterm using 1 <;> ring
    _ = _ := by ring

theorem gaussian_moment_constant_identity (b : ℕ) (hb : 0 < b) (δ : ℝ) :
    (2 : ℝ) ^ (b - 1) * 2 * ((4 * (b : ℝ)) ^ (2 * b) / δ ^ (2 * b)) =
      (32 / δ ^ 2) ^ b * (b : ℝ) ^ (2 * b) := by
  rw [← pow_succ, show b - 1 + 1 = b by omega]
  have h32 : (2 : ℝ) ^ b * 16 ^ b = 32 ^ b := by rw [← mul_pow]; norm_num
  rw [pow_mul, pow_mul, pow_mul]
  rw [show (4 * (b : ℝ)) ^ 2 = 16 * (b : ℝ) ^ 2 by ring]
  simp only [div_pow, mul_pow]
  calc
    _ = ((2 : ℝ) ^ b * 16 ^ b) * ((b : ℝ) ^ 2) ^ b / (δ ^ 2) ^ b := by ring
    _ = _ := by rw [h32]; ring

theorem gaussian_power_majorant {x : ℝ} (b : ℕ) (t : ℝ) :
    (1 + x ^ 4) ^ b * Real.exp (t * x ^ 2 / 2) ≤
      (2 : ℝ) ^ (b - 1) * gaussianPair b t x := by
  have hp := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ x ^ 4) b
  have hmul := mul_le_mul_of_nonneg_right hp (Real.exp_pos (t * x ^ 2 / 2)).le
  simp only [one_pow, ← pow_mul] at hmul
  exact hmul.trans_eq (by unfold gaussianPair; ring)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Pointwise physical scaling followed by Gaussian completion of the square. -/
theorem realized_degree_sum_le_scaled (A : Finset V) {B F φ r : ℝ}
    (hN : 0 < Fintype.card V) (hB : 0 ≤ B) (hB1 : B < 1)
    (hF : 0 ≤ F) (hφ : 0 ≤ φ) (hr : 0 ≤ r)
    (hNr : (Fintype.card V : ℝ) * r ≤ B ^ 2)
    (hφN : φ * Real.sqrt (Fintype.card V : ℝ) ≤ F) (x : ℝ) :
    (∑ d ∈ realizedDegrees A, weightedDegreeMonomial φ r d x) ≤
      (degreeConstant B F / (Fintype.card V : ℝ) ^ 2) ^ A.card *
        Real.exp (F ^ 2 * B ^ 2 / (1 - B ^ 2)) *
          ((1 + x ^ 4) ^ A.card * Real.exp ((1 - eta B) * x ^ 2 / 2)) := by
  have hNR : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr hN
  have hd := degreeConstant_nonneg hB hF
  have hc := branchFactor_le hNR hr hB hφ hF hNr hφN x
  have he := gaussianExponent_le hNR.le hr hB hB1 hφ hF hNr hφN x
  apply (realized_degree_sum_le_majorant A hφ hr x).trans
  have hp := mul_le_mul (pow_le_pow_left₀ (by positivity) hc A.card)
    (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
  simpa only [mul_pow, Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using hp

/-- The finite weak-field family, for a nonempty fixed branching set. -/
theorem fixed_branch_mass_bound (A : Finset V) (hA : 0 < A.card)
    {B F φ r : ℝ} (hN : 0 < Fintype.card V)
    (hB : 0 ≤ B) (hB1 : B < 1) (hF : 0 ≤ F) (hφ : 0 ≤ φ) (hr : 0 ≤ r)
    (hNr : (Fintype.card V : ℝ) * r ≤ B ^ 2)
    (hφN : φ * Real.sqrt (Fintype.card V : ℝ) ≤ F) :
    (∑ Γ ∈ branchFamily A, φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) ≤
      massConstant B F * (degreeConstant B F / (Fintype.card V : ℝ) ^ 2) ^ A.card *
        (32 / eta B ^ 2) ^ A.card * (A.card : ℝ) ^ (2 * A.card) := by
  let C := (degreeConstant B F / (Fintype.card V : ℝ) ^ 2) ^ A.card *
    Real.exp (F ^ 2 * B ^ 2 / (1 - B ^ 2))
  have hd := degreeConstant_nonneg hB hF
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hη := eta_pos hB hB1
  have ht : 1 - eta B < 1 := by linarith
  have hi : GaussianIntegrable (fun x => C * (2 : ℝ) ^ (A.card - 1) *
      gaussianPair A.card (1 - eta B) x) := by
    have hp := gaussianPair_integrable A.card ht
    unfold GaussianIntegrable at *
    simpa only [mul_assoc] using hp.const_mul (C * (2 : ℝ) ^ (A.card - 1))
  have hpoint (x : ℝ) :
      (∑ d ∈ realizedDegrees A, weightedDegreeMonomial φ r d x) ≤
        C * (2 : ℝ) ^ (A.card - 1) * gaussianPair A.card (1 - eta B) x := by
    apply (realized_degree_sum_le_scaled A hN hB hB1 hF hφ hr hNr hφN x).trans
    exact (mul_le_mul_of_nonneg_left (gaussian_power_majorant A.card (1 - eta B)) hC).trans_eq
      (by ring)
  apply (branchFamily_mass_le_gaussian A hφ hr).trans
  apply (gaussianMean_mono _ _ (realized_degree_sum_nonneg A hφ hr) hi hpoint).trans
  rw [gaussianMean_const_mul]
  have hp := mul_le_mul_of_nonneg_left
    (gaussianPair_mean_le A.card hA hη (eta_le_one B))
    (mul_nonneg hC (by positivity : 0 ≤ (2 : ℝ) ^ (A.card - 1)))
  apply hp.trans_eq
  have hid := gaussian_moment_constant_identity A.card hA (eta B)
  calc
    _ = C * eta B ^ (-(1 / 2 : ℝ)) *
        ((2 : ℝ) ^ (A.card - 1) * 2 *
          ((4 * (A.card : ℝ)) ^ (2 * A.card) / eta B ^ (2 * A.card))) := by ring
    _ = _ := by rw [hid]; unfold massConstant; dsimp [C]; ring

end Manuscript.SKBranching
