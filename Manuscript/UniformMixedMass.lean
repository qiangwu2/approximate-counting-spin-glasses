import Manuscript.MixedEnergy
import Manuscript.MixedThresholdParameters
import Manuscript.UniformBiasedMean
import Manuscript.UniformFieldMoment
import SpinGlass.TanhBound

/-! The unconditional weak-field comparison mass estimate for finite mixtures. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.UniformMixedMass
open SpinGlass.Expansion Manuscript.Model Manuscript.MixedThreshold
open Manuscript.MixedCoefficient Manuscript.MixedEnergy Manuscript.UniformEntropy
open Manuscript.UniformGraphMass Manuscript.UniformBiasedMean Manuscript.UniformFieldMoment

/-- The explicit constant in Proposition 2.2, with `v = β₊²` and
`thresholdSquared = β_f²`. -/
def massConstant (P : Finset ℕ) (a : ℕ → ℝ) (v rho : ℝ) : ℝ :=
  let lam := v / thresholdSquared P a
  Real.exp (v * MixedThreshold.delta P a + (1 + lam) / (2 * (1 - lam)) * rho ^ 4) *
    ((3 + lam) / (1 - lam))

/-- The weak-field hypothesis implies the fourth-power normalization used by
all finite-size estimates. -/
theorem weak_field_fourth (N : ℕ) (hN : 0 < N) {h rho : ℝ}
    (hh : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    (N : ℝ) * h ^ 4 ≤ rho ^ 4 := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh4 := pow_le_pow_left₀ (abs_nonneg h) hh 4
  have hp : ((N : ℝ) ^ (-(1 / 4 : ℝ))) ^ 4 = (N : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
    norm_num
  rw [mul_pow, hp] at hh4
  have hs : (N : ℝ) ^ (-(1 : ℝ)) = (N : ℝ)⁻¹ := by
    rw [Real.rpow_neg hN'.le, Real.rpow_one]
  rw [hs] at hh4
  have habs : |h| ^ 4 = h ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, pow_mul, sq_abs]
  rw [habs] at hh4
  have hh4' : h ^ 4 ≤ rho ^ 4 * (N : ℝ)⁻¹ := hh4
  have hhN := mul_le_mul_of_nonneg_left hh4' hN'.le
  have heq : (N : ℝ) * (rho ^ 4 * (N : ℝ)⁻¹) = rho ^ 4 := by field_simp
  rwa [heq] at hhN

/-- The actual complete graphical comparison sum is uniformly bounded.
No graphical or analytic estimate is a premise. -/
theorem uniform_graphical_mass_fourth (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {v h rho : ℝ} (hv : 0 < v)
    (hvT : v < thresholdSquared P a) (hfield : (N : ℝ) * h ^ 4 ≤ rho ^ 4) :
    graphMass Subtype.val (Finset.univ : Finset (Edge N P)).powerset h
      (comparisonWeight N P a v) ≤ massConstant P a v rho := by
  obtain ⟨p, hpP⟩ := hP
  have hN : 0 < N := by have := hp p hpP; have := hpN p hpP; omega
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hT := thresholdSquared_pos P a ⟨p, hpP⟩ ha hp
  let lam := v / thresholdSquared P a
  have hlam : 0 < lam := div_pos hv hT
  have hlam1 : lam < 1 := (div_lt_one hT).2 hvT
  have hr : ∀ e ∈ (Finset.univ : Finset (Edge N P)),
      |comparisonWeight N P a v e| ≤ 1 := by
    intro e he
    obtain ⟨h0, h1⟩ := comparisonWeight_range N P a ⟨p, hpP⟩ ha hp hpN hv.le hvT e
    rw [abs_of_nonneg h0]
    exact h1.le
  have hb : (N : ℝ) * (Real.tanh h ^ 2) ^ 2 ≤ rho ^ 4 := by
    have ht := SpinGlass.TanhBound.tanh_sq_le_sq h
    have ht2 := pow_le_pow_left₀ (sq_nonneg (Real.tanh h)) ht 2
    have hhN := mul_le_mul_of_nonneg_left ht2 hN'.le
    nlinarith
  have hm := entropy_tilt_moment (V := Fin N) (by simpa using hN) hlam hlam1
    (by simpa using hb)
  have he : ∀ σ : Fin N → Bool,
      (∑ e : Edge N P, comparisonWeight N P a v e * edgeCharacter Subtype.val σ e) +
        Real.tanh h ^ 2 * signSum σ ≤
      v * MixedThreshold.delta P a +
        (lam * ((N : ℝ) * entropy (overlap σ)) + Real.tanh h ^ 2 * signSum σ) := by
    intro σ
    have hh := comparisonEnergy_le_entropy N P a ⟨p, hpP⟩ ha hp hpN hv.le hvT σ
    change (∑ e : Edge N P, comparisonWeight N P a v e * edgeCharacter Subtype.val σ e) ≤
      v * MixedThreshold.delta P a + lam * ((N : ℝ) * entropy (overlap σ)) at hh
    linarith
  calc
    _ ≤ spinMean (fun σ : Fin N → Bool => Real.exp
        ((∑ e : Edge N P, comparisonWeight N P a v e * edgeCharacter Subtype.val σ e) +
          Real.tanh h ^ 2 * signSum σ)) :=
      graphMass_le_exp_moment Subtype.val Finset.univ h _ hr
    _ ≤ spinMean (fun σ : Fin N → Bool =>
        Real.exp (v * MixedThreshold.delta P a) *
          Real.exp (lam * ((N : ℝ) * entropy (overlap σ)) + Real.tanh h ^ 2 * signSum σ)) := by
      apply mean_mono
      intro σ
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (he σ)
    _ = Real.exp (v * MixedThreshold.delta P a) *
        spinMean (fun σ : Fin N → Bool =>
          Real.exp (lam * ((N : ℝ) * entropy (overlap σ)) + Real.tanh h ^ 2 * signSum σ)) :=
      spinMean_mul_left _ _
    _ ≤ Real.exp (v * MixedThreshold.delta P a) *
        (((3 + lam) / (1 - lam)) * Real.exp (((1 + lam) / (1 - lam)) * rho ^ 4 / 2)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [Fintype.card_fin] using hm
    _ = massConstant P a v rho := by
      unfold massConstant
      change _ = Real.exp (v * MixedThreshold.delta P a +
        (1 + lam) / (2 * (1 - lam)) * rho ^ 4) * ((3 + lam) / (1 - lam))
      rw [Real.exp_add]
      have heq : (1 + lam) / (1 - lam) * rho ^ 4 / 2 =
          (1 + lam) / (2 * (1 - lam)) * rho ^ 4 := by
        field_simp
        <;> ring
      rw [heq]
      ring

/-- Proposition 2.2 for the physical weak-field window, including every finite
system whose active interaction orders fit inside it. -/
theorem uniform_graphical_mass (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {v h rho : ℝ} (hv : 0 < v)
    (hvT : v < thresholdSquared P a)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    graphMass Subtype.val (Finset.univ : Finset (Edge N P)).powerset h
      (comparisonWeight N P a v) ≤ massConstant P a v rho := by
  have hN : 0 < N := by obtain ⟨p, hpP⟩ := hP; have := hp p hpP; have := hpN p hpP; omega
  exact uniform_graphical_mass_fourth N P a hP ha hp hpN hv hvT
    (weak_field_fourth N hN hfield)

theorem massConstant_ge_one (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    {v rho : ℝ} (hv : 0 ≤ v) (hvT : v < thresholdSquared P a) :
    1 ≤ massConstant P a v rho := by
  have hT := thresholdSquared_pos P a hP ha hp
  have hlam : 0 ≤ v / thresholdSquared P a := div_nonneg hv hT.le
  have hlam1 : v / thresholdSquared P a < 1 := (div_lt_one hT).2 hvT
  have hden : 0 < 1 - v / thresholdSquared P a := by linarith
  have hfrac : 1 ≤ (3 + v / thresholdSquared P a) / (1 - v / thresholdSquared P a) := by
    apply (le_div_iff₀ hden).2
    linarith
  have he : 1 ≤ Real.exp (v * MixedThreshold.delta P a +
      (1 + v / thresholdSquared P a) / (2 * (1 - v / thresholdSquared P a)) * rho ^ 4) := by
    apply Real.one_le_exp_iff.mpr
    exact add_nonneg (mul_nonneg hv (delta_nonneg P a))
      (mul_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity))
  exact one_le_mul_of_one_le_of_one_le he hfrac

/-- The manuscript's prescribed midpoint inflation specializes the preceding
bound without an additional choice of temperature or constants. -/
theorem uniform_graphical_mass_midpoint (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p)
    (hpN : ∀ p ∈ P, p ≤ N) {B h rho : ℝ} (hB : 0 < B)
    (hBT : B < betaF P a)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    graphMass Subtype.val (Finset.univ : Finset (Edge N P)).powerset h
      (comparisonWeight N P a (betaPlus P a B ^ 2)) ≤
        massConstant P a (betaPlus P a B ^ 2) rho := by
  obtain ⟨hv, hvT⟩ := betaPlus_sq_range P a hP ha hp hB hBT
  exact uniform_graphical_mass N P a hP ha hp hpN hv hvT hfield

end Manuscript.UniformMixedMass
