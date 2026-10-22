import Manuscript.UniformEntropyMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! A weak linear-field exponential moment with the explicit entropy margin. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.UniformFieldMoment
open SpinGlass.Expansion Manuscript.UniformEntropy
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem spinMean_add (f g : (V → Bool) → ℝ) :
    spinMean (fun σ => f σ + g σ) = spinMean f + spinMean g := by
  simp [spinMean, Finset.sum_add_distrib, mul_add]

/-- A normalized finite Hölder estimate, proved directly by convexity of exp.
The first moment bound is deliberately left with exponent one, matching C₊. -/
theorem exp_sum_moment_le (f g : (V → Bool) → ℝ) {p q A B : ℝ}
    (hp : 1 ≤ p) (hq : 0 < q) (hconj : 1 / p + 1 / q = 1) (hA : 1 ≤ A)
    (hf : spinMean (fun σ => Real.exp (p * f σ)) ≤ A)
    (hg : spinMean (fun σ => Real.exp (q * g σ)) ≤ Real.exp (q * B)) :
    spinMean (fun σ => Real.exp (f σ + g σ)) ≤ A * Real.exp B := by
  have hp0 : 0 < p := by linarith
  have hA0 : 0 < A := by linarith
  have hlog : 0 ≤ Real.log A := Real.log_nonneg hA
  have hf' : spinMean (fun σ => Real.exp (p * (f σ - Real.log A))) ≤ 1 := by
    have heq : (fun σ => Real.exp (p * (f σ - Real.log A))) =
        fun σ => Real.exp (-p * Real.log A) * Real.exp (p * f σ) := by
      funext σ
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, spinMean_mul_left]
    calc
      _ ≤ Real.exp (-p * Real.log A) * A :=
        mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le
      _ ≤ Real.exp (-Real.log A) * A :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hA0.le
      _ = 1 := by rw [Real.exp_neg, Real.exp_log hA0, inv_mul_cancel₀ hA0.ne']
  have hg' : spinMean (fun σ => Real.exp (q * (g σ - B))) ≤ 1 := by
    have heq : (fun σ => Real.exp (q * (g σ - B))) =
        fun σ => Real.exp (-q * B) * Real.exp (q * g σ) := by
      funext σ
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, spinMean_mul_left]
    calc
      _ ≤ Real.exp (-q * B) * Real.exp (q * B) :=
        mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
  have hpoint : ∀ σ : V → Bool,
      Real.exp ((f σ - Real.log A) + (g σ - B)) ≤
        (1 / p) * Real.exp (p * (f σ - Real.log A)) +
        (1 / q) * Real.exp (q * (g σ - B)) := by
    intro σ
    have hc := convexOn_exp.2 (Set.mem_univ (p * (f σ - Real.log A)))
      (Set.mem_univ (q * (g σ - B))) (by positivity : 0 ≤ 1 / p)
      (by positivity : 0 ≤ 1 / q) hconj
    simp only [smul_eq_mul] at hc
    have heq : 1 / p * (p * (f σ - Real.log A)) +
        1 / q * (q * (g σ - B)) = (f σ - Real.log A) + (g σ - B) := by
      field_simp
    rwa [heq] at hc
  have hm := mean_mono hpoint
  rw [spinMean_add, spinMean_mul_left, spinMean_mul_left] at hm
  have hnorm : spinMean (fun σ => Real.exp ((f σ - Real.log A) + (g σ - B))) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hf' (by positivity : 0 ≤ 1 / p)
    have h2 := mul_le_mul_of_nonneg_left hg' (by positivity : 0 ≤ 1 / q)
    nlinarith
  have heq : (fun σ => Real.exp (f σ + g σ)) = fun σ =>
      (A * Real.exp B) * Real.exp ((f σ - Real.log A) + (g σ - B)) := by
    funext σ
    rw [show f σ + g σ = (Real.log A + B) +
      ((f σ - Real.log A) + (g σ - B)) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log hA0]
  rw [heq, spinMean_mul_left]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg hA0.le (Real.exp_pos B).le)

/-- Exact subgaussian bound for the finite uniform sum of signs. -/
theorem signSum_mgf_le (t : ℝ) :
    spinMean (fun σ : V → Bool => Real.exp (t * signSum σ)) ≤
      Real.exp ((Fintype.card V : ℝ) * t ^ 2 / 2) := by
  rw [signSum_mgf]
  have hh := pow_le_pow_left₀ (Real.cosh_pos t).le (Real.cosh_le_exp_half_sq t)
    (Fintype.card V)
  rw [← Real.exp_nat_mul] at hh
  convert hh using 1 <;> congr 1 <;> ring

/-- Entropy plus a homogeneous linear tilt. The exponent remains uniform when
`N*b²` is bounded, as happens for `b=tanh(h)²` in a weak field. -/
theorem entropy_tilt_moment (hV : 0 < Fintype.card V) {lam b R : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1)
    (hfield : (Fintype.card V : ℝ) * b ^ 2 ≤ R) :
    spinMean (fun σ : V → Bool =>
      Real.exp (lam * ((Fintype.card V : ℝ) * entropy (overlap σ)) + b * signSum σ)) ≤
      ((3 + lam) / (1 - lam)) * Real.exp (((1 + lam) / (1 - lam)) * R / 2) := by
  let p := (1 + lam) / (2 * lam)
  let q := (1 + lam) / (1 - lam)
  let A := (3 + lam) / (1 - lam)
  let B := q * R / 2
  have hp : 1 ≤ p := by dsimp [p]; apply (le_div_iff₀ (by positivity)).2; linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hconj : 1 / p + 1 / q = 1 := by dsimp [p, q]; field_simp; ring
  have hA : 1 ≤ A := by dsimp [A]; apply (le_div_iff₀ (by linarith)).2; linarith
  have hpLam : p * lam = (1 + lam) / 2 := by dsimp [p]; field_simp
  have hf : spinMean (fun σ : V → Bool =>
      Real.exp (p * (lam * ((Fintype.card V : ℝ) * entropy (overlap σ))))) ≤ A := by
    simp_rw [← mul_assoc p lam, hpLam]
    have hh := entropy_exponential_moment (V := V) hV (lam := (1 + lam) / 2)
      (by linarith) (by linarith)
    have heq : 1 + 2 * ((1 + lam) / 2) / (1 - (1 + lam) / 2) = A := by
      dsimp [A]
      rw [show 1 - (1 + lam) / 2 = (1 - lam) / 2 by ring]
      field_simp [show 1 - lam ≠ 0 by linarith]
      <;> ring
    rwa [heq] at hh
  have hg : spinMean (fun σ : V → Bool => Real.exp (q * (b * signSum σ))) ≤
      Real.exp (q * B) := by
    simp_rw [← mul_assoc q b]
    apply (signSum_mgf_le (V := V) (q * b)).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hfield (sq_nonneg q)
    dsimp [B]
    nlinarith
  exact exp_sum_moment_le _ _ hp hq hconj hA hf hg

end Manuscript.UniformFieldMoment
