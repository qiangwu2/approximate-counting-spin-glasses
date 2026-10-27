import SpinGlass.NoiseKernel
import SpinGlass.FiniteLowerTail

/-!
# Section 5.2 of the manuscript dated 27 October 2026

The new Lemma 5.3 quotes the general finite-product theorem of
Mossel--Oleszkiewicz--Sen. This module proves the uniform-sign specialization
used in the manuscript, with its explicit resampling kernel and time parameter.
It does not claim the theorem for arbitrary nonuniform finite product measures.
No reverse-hypercontractivity assumption or new axiom is introduced.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.PDF16Noise

open SpinGlass.Expansion SpinGlass.Noise SpinGlass.NoiseKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Keep the current sign with probability `θ`; otherwise resample uniformly. -/
def resamplingWeight (θ : ℝ) (x y : Bool) : ℝ :=
  θ * (if y = x then 1 else 0) + (1 - θ) / 2

/-- The explicit product resampling formula on the uniform sign cube. -/
def resampling (θ : ℝ) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  ∑ y : ι → Bool, f y * ∏ i, resamplingWeight θ (x i) (y i)

theorem resamplingWeight_eq_noiseWeight (θ : ℝ) (x y : Bool) :
    resamplingWeight θ x y = noiseWeight θ (Bool.xor x y) := by
  cases x <;> cases y <;> norm_num [resamplingWeight, noiseWeight] <;> ring

/-- Thus the new resampling notation and the existing noise operator agree. -/
theorem resampling_eq_cubeNoise (θ : ℝ) (f : (ι → Bool) → ℝ) :
    resampling θ f = cubeNoise θ f := by
  funext x
  rw [cubeNoise_eq_kernel_sum]
  simp only [resampling, cubeKernel, resamplingWeight_eq_noiseWeight]
  apply Finset.sum_congr rfl
  intro y hy
  exact mul_comm _ _

/-- The time-parameterized resampling operator in Section 5.2. -/
def semigroup (t : ℝ) (f : (ι → Bool) → ℝ) : (ι → Bool) → ℝ :=
  resampling (Real.exp (-t)) f

theorem semigroup_eq_cubeNoise (t : ℝ) (f : (ι → Bool) → ℝ) :
    semigroup t f = cubeNoise (Real.exp (-t)) f :=
  resampling_eq_cubeNoise _ _

/-- `N_θ = T_log(1/θ)`, with the literal time parameter in the new text. -/
theorem semigroup_log_inv {θ : ℝ} (hθ : 0 < θ) (f : (ι → Bool) → ℝ) :
    semigroup (Real.log (1 / θ)) f = cubeNoise θ f := by
  rw [semigroup_eq_cubeNoise, one_div, Real.log_inv, neg_neg, Real.exp_log hθ]

/-- Lemma 5.3 in precisely the exponent range used to prove Lemma 5.4.
The general nonuniform-space statement quoted in the PDF is not asserted here. -/
theorem lemma_5_3_uniform_signs {p q t : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : q < 0)
    (ht : Real.log ((1 - q) / (1 - p)) ≤ t)
    (f : (ι → Bool) → ℝ) (hf : ∀ x, 0 < f x) :
    (spinMean (fun x => f x ^ p)) ^ (1 / p) ≤
      (spinMean (fun x => (semigroup t f x) ^ q)) ^ (1 / q) := by
  have ha : 0 < 1 - p := by linarith
  have hb : 0 < 1 - q := by linarith
  have hratio : 0 < (1 - q) / (1 - p) := div_pos hb ha
  have htime : Real.exp (-t) ≤ (1 - p) / (1 - q) := by
    calc
      Real.exp (-t) ≤ Real.exp (-Real.log ((1 - q) / (1 - p))) :=
        Real.exp_le_exp.mpr (neg_le_neg ht)
      _ = (1 - p) / (1 - q) := by
        rw [Real.exp_neg, Real.exp_log hratio, inv_div]
  rw [semigroup_eq_cubeNoise]
  exact SpinGlass.ReverseHypercontractivity.reverse_norm hp hp1 hq
    (Real.exp_pos _) htime f hf

/-- Lemma 5.4 (equation 66), using the PDF's `s = (sqrt θ)⁻¹ - 1`. -/
theorem lemma_5_4 {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (f : (ι → Bool) → ℝ) (hf : ∀ x, 0 < f x) (hmean : spinMean f = 1) :
    spinMean (fun x => (cubeNoise θ f x) ^ (-((Real.sqrt θ)⁻¹ - 1))) ≤
      spinMean (fun x => f x ^ 2) := by
  have hs : (1 - Real.sqrt θ) / Real.sqrt θ = (Real.sqrt θ)⁻¹ - 1 := by
    field_simp
  rw [← hs]
  exact SpinGlass.FiniteLowerTail.noisy_negative_moment_le_second_moment
    hθ hθ1 f hf hmean

end Manuscript.PDF16Noise
