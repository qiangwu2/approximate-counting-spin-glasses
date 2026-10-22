import Manuscript.SignPolynomial
import SpinGlass.FiniteLowerTail

/-!
# The weak-field conditional negative moment

The reverse-hypercontractive estimate is proved in the imported source, not
introduced as an axiom. This file proves the conditional sign-cube step of
Proposition 5.4. The right-hand side is the actual inflated graphical mass;
the uniform bound on its disorder average remains a separate obligation.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.ConditionalLowerTail

open SpinGlass.Expansion SpinGlass.Noise
open Manuscript.FieldExpansion Manuscript.SignPolynomial

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The negative exponent used in equation (60), written without a negative square root. -/
def exponent (θ : ℝ) : ℝ := (1 - Real.sqrt θ) / Real.sqrt θ

theorem exponent_pos {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 < exponent θ := SpinGlass.LowerTail.negativeExponent_pos hθ hθ1

theorem exponent_eq_inv_sqrt_sub_one {θ : ℝ} (hθ : 0 < θ) :
    exponent θ = (Real.sqrt θ)⁻¹ - 1 := by
  unfold exponent
  field_simp

/-- Lemma 5.3, in the manuscript's negative-exponent norm formulation. -/
theorem reverse_hypercontractivity {θ q s : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hs : 0 < s)
    (hθ : 0 < θ) (hparam : θ ≤ (1 - q) / (1 + s))
    (f : (E → Bool) → ℝ) (hf : ∀ η, 0 < f η) :
    (spinMean (fun η => f η ^ q)) ^ (1 / q) ≤
      (spinMean (fun η => (cubeNoise θ f η) ^ (-s))) ^ (1 / (-s)) := by
  exact SpinGlass.ReverseHypercontractivity.reverse_norm hq hq1 (by linarith)
    hθ (by simpa only [sub_neg_eq_add] using hparam) f hf

/-- The conditional negative moment, without a presumed graphical-mass bound. -/
theorem negative_moment_le_graph_mass
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (a : E → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (ha : ∀ e ∈ edges, |a e / θ| ≤ 1 / 2) :
    spinMean (fun η => polynomial incidence edges.powerset h a η ^ (-exponent θ)) ≤
      ∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (boundary incidence Γ).card) *
        ∏ e ∈ Γ, (a e / θ) ^ 2 := by
  have hf := inflated_polynomial_pos incidence edges h a θ ha
  have hm := mean_one incidence edges h (fun e => a e / θ)
  have hb := SpinGlass.FiniteLowerTail.noisy_negative_moment_le_second_moment
    hθ hθ1 (polynomial incidence edges.powerset h (fun e => a e / θ)) hf hm
  simp_rw [noise_inflation_identity incidence edges.powerset h a θ (ne_of_gt hθ)] at hb
  rw [second_moment] at hb
  exact hb

/-- Conditional lower-tail bound as an actual fraction of sign configurations.
This does not assume a bound on the second moment for each magnitude array. -/
theorem lower_tail_le_graph_mass
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (a : E → ℝ)
    {θ z : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z)
    (ha : ∀ e ∈ edges, |a e / θ| ≤ 1 / 2) :
    ((Finset.univ.filter (fun η : E → Bool =>
      polynomial incidence edges.powerset h a η < z)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card E ≤
      (∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (boundary incidence Γ).card) *
        ∏ e ∈ Γ, (a e / θ) ^ 2) * z ^ exponent θ := by
  have hf := inflated_polynomial_pos incidence edges h a θ ha
  have hm := mean_one incidence edges h (fun e => a e / θ)
  have hb := SpinGlass.FiniteLowerTail.noisy_lower_tail_le_second_moment
    hθ hθ1 hz (polynomial incidence edges.powerset h (fun e => a e / θ)) hf hm
  simp_rw [noise_inflation_identity incidence edges.powerset h a θ (ne_of_gt hθ)] at hb
  rw [second_moment] at hb
  exact hb

/-- The same conditional bound for the actual normalized exponential
partition function, with signed real interaction coefficients. -/
theorem partition_negative_moment_le_graph_mass
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (x : E → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hx : ∀ e ∈ edges, |Real.tanh (x e) / θ| ≤ 1 / 2) :
    spinMean (fun η : E → Bool =>
      normalizedPartition incidence edges h (fun e => x e * spinSign (η e)) ^
        (-exponent θ)) ≤
      ∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (boundary incidence Γ).card) *
        ∏ e ∈ Γ, (Real.tanh (x e) / θ) ^ 2 := by
  simp_rw [normalizedPartition_signed]
  exact negative_moment_le_graph_mass incidence edges h (fun e => Real.tanh (x e)) hθ hθ1 hx

/-- A fraction-of-signs estimate for the actual normalized partition function. -/
theorem partition_lower_tail_le_graph_mass
    (incidence : E → Finset V) (edges : Finset E) (h : ℝ) (x : E → ℝ)
    {θ z : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z)
    (hx : ∀ e ∈ edges, |Real.tanh (x e) / θ| ≤ 1 / 2) :
    ((Finset.univ.filter (fun η : E → Bool =>
      normalizedPartition incidence edges h (fun e => x e * spinSign (η e)) < z)).card : ℝ) /
        (2 : ℝ) ^ Fintype.card E ≤
      (∑ Γ ∈ edges.powerset, Real.tanh h ^ (2 * (boundary incidence Γ).card) *
        ∏ e ∈ Γ, (Real.tanh (x e) / θ) ^ 2) * z ^ exponent θ := by
  simp_rw [normalizedPartition_signed]
  exact lower_tail_le_graph_mass incidence edges h (fun e => Real.tanh (x e)) hθ hθ1 hz hx

end Manuscript.ConditionalLowerTail
