import Manuscript.UniformGraphMass

/-! Field-weighted graph mass as an actual biased-spin average. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.UniformBiasedMean
open SpinGlass.Expansion Manuscript.FieldExpansion Manuscript.UniformEntropy
open Manuscript.UniformGraphMass
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- Product spin average with mean `b`; algebraically valid for every real `b`. -/
def biasedMean (b : ℝ) (f : (V → Bool) → ℝ) : ℝ :=
  spinMean (fun σ => tiltedWeight b σ * f σ)

theorem biasedMean_mul_left (b c : ℝ) (f : (V → Bool) → ℝ) :
    biasedMean b (fun σ => c * f σ) = c * biasedMean b f := by
  simp only [biasedMean, spinMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

theorem biasedMean_sum {I : Type*} (b : ℝ) (s : Finset I)
    (f : I → (V → Bool) → ℝ) :
    biasedMean b (fun σ => ∑ i ∈ s, f i σ) = ∑ i ∈ s, biasedMean b (f i) := by
  simp only [biasedMean, spinMean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem sum_biased_spin_pow (b : ℝ) (n : ℕ) :
    (∑ s : Bool, (1 + b * spinSign s) * spinSign s ^ n) =
      2 * (if Even n then 1 else b) := by
  rcases Nat.even_or_odd n with hn | hn
  · simp [spinSign, hn, hn.neg_one_pow]
    ring
  · simp [spinSign, Nat.not_even_iff_odd.mpr hn, hn.neg_one_pow]
    ring

theorem biasedMean_character (b : ℝ) (incidence : E → Finset V) (Γ : Finset E) :
    biasedMean b (fun σ : V → Bool => ∏ e ∈ Γ, edgeCharacter incidence σ e) =
      b ^ (boundary incidence Γ).card := by
  unfold biasedMean spinMean tiltedWeight
  simp_rw [character_eq_degree, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun v (s : Bool) =>
    (1 + b * spinSign s) * spinSign s ^ degree incidence Γ v)]
  simp_rw [sum_biased_spin_pow]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num)), one_mul]
  have hf : (∏ v : V, if Even (degree incidence Γ v) then (1 : ℝ) else b) =
      ∏ v ∈ boundary incidence Γ, b := by
    rw [boundary, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro v hv
    split_ifs <;> rfl
  rw [hf]
  simp

theorem biased_graphical_expansion (b : ℝ) (incidence : E → Finset V)
    (edges : Finset E) (r : E → ℝ) :
    biasedMean b (fun σ : V → Bool =>
      ∏ e ∈ edges, (1 + r e * edgeCharacter incidence σ e)) =
      ∑ Γ ∈ edges.powerset, b ^ (boundary incidence Γ).card * ∏ e ∈ Γ, r e := by
  simp_rw [Finset.prod_one_add, Finset.prod_mul_distrib]
  rw [biasedMean_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [biasedMean_mul_left, biasedMean_character, mul_comm]

theorem graphMass_eq_biasedMean (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (r : E → ℝ) :
    graphMass incidence edges.powerset h r =
      biasedMean (Real.tanh h ^ 2) (fun σ : V → Bool =>
        ∏ e ∈ edges, (1 + r e * edgeCharacter incidence σ e)) := by
  rw [biased_graphical_expansion]
  simp only [graphMass, pow_mul]

theorem spin_product_nonneg (incidence : E → Finset V) (edges : Finset E)
    (r : E → ℝ) (hr : ∀ e ∈ edges, |r e| ≤ 1) (σ : V → Bool) :
    0 ≤ ∏ e ∈ edges, (1 + r e * edgeCharacter incidence σ e) := by
  apply Finset.prod_nonneg
  intro e he
  have hh : |r e * edgeCharacter incidence σ e| ≤ 1 := by
    simpa only [abs_mul, abs_edgeCharacter, mul_one] using hr e he
  linarith [(abs_le.mp hh).1]

theorem spin_product_le_exp_sum (incidence : E → Finset V) (edges : Finset E)
    (r : E → ℝ) (hr : ∀ e ∈ edges, |r e| ≤ 1) (σ : V → Bool) :
    (∏ e ∈ edges, (1 + r e * edgeCharacter incidence σ e)) ≤
      Real.exp (∑ e ∈ edges, r e * edgeCharacter incidence σ e) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro e he
    have hh : |r e * edgeCharacter incidence σ e| ≤ 1 := by
      simpa only [abs_mul, abs_edgeCharacter, mul_one] using hr e he
    linarith [(abs_le.mp hh).1]
  · intro e he
    simpa only [add_comm] using Real.add_one_le_exp (r e * edgeCharacter incidence σ e)

theorem tiltedWeight_le_exp (b : ℝ) (hb : |b| ≤ 1) (σ : V → Bool) :
    tiltedWeight b σ ≤ Real.exp (b * signSum σ) := by
  unfold tiltedWeight signSum
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro v hv
    have hh : |b * spinSign (σ v)| ≤ 1 := by
      simpa only [abs_mul, abs_spinSign, mul_one] using hb
    linarith [(abs_le.mp hh).1]
  · intro v hv
    simpa only [add_comm] using Real.add_one_le_exp (b * spinSign (σ v))

/-- The squared-field graph mass is bounded by a uniform spin exponential
moment with linear tilt `tanh(h)^2`; no inverse hyperbolic function is needed. -/
theorem graphMass_le_exp_moment (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (r : E → ℝ) (hr : ∀ e ∈ edges, |r e| ≤ 1) :
    graphMass incidence edges.powerset h r ≤
      spinMean (fun σ : V → Bool =>
        Real.exp ((∑ e ∈ edges, r e * edgeCharacter incidence σ e) +
          Real.tanh h ^ 2 * signSum σ)) := by
  rw [graphMass_eq_biasedMean]
  unfold biasedMean
  apply mean_mono
  intro σ
  rw [Real.exp_add]
  have ht : |Real.tanh h ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hh := Real.abs_tanh_lt_one h
    nlinarith [sq_nonneg (Real.tanh h), abs_nonneg (Real.tanh h), sq_abs (Real.tanh h)]
  have h1 := tiltedWeight_le_exp (Real.tanh h ^ 2) ht σ
  have h2 := spin_product_le_exp_sum incidence edges r hr σ
  have hh := mul_le_mul h1 h2 (spin_product_nonneg incidence edges r hr σ) (Real.exp_pos _).le
  simpa only [mul_comm] using hh

end Manuscript.UniformBiasedMean
