import Manuscript.FieldExpansion
import SpinGlass.Noise

/-!
# Conditional sign calculations for mixed interactions and a field

These are exact finite-cube identities. They do not assert the integration over
an arbitrary disorder law or the uniform second-moment/lower-tail bound.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.SignPolynomial

open SpinGlass.Expansion SpinGlass.Noise Manuscript.FieldExpansion

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def polynomial (incidence : E → Finset V) (graphs : Finset (Finset E))
    (h : ℝ) (a : E → ℝ) (η : E → Bool) : ℝ :=
  ∑ Γ ∈ graphs, graphWeight incidence h (fun e => a e * spinSign (η e)) Γ

omit [Fintype E] [DecidableEq E] in
/-- The polynomial is the actual normalized exponential partition function
when signs are applied to the real interaction coefficients. -/
theorem normalizedPartition_signed (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (x : E → ℝ) (η : E → Bool) :
    normalizedPartition incidence edges h (fun e => x e * spinSign (η e)) =
      polynomial incidence edges.powerset h (fun e => Real.tanh (x e)) η := by
  rw [normalizedPartition_eq_graph_sum]
  unfold polynomial
  apply Finset.sum_congr rfl
  intro Γ hΓ
  unfold graphWeight
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  cases hη : η e <;> simp [spinSign, hη]

omit [Fintype E] [DecidableEq E] in
theorem polynomial_eq_characters (incidence : E → Finset V)
    (graphs : Finset (Finset E)) (h : ℝ) (a : E → ℝ) (η : E → Bool) :
    polynomial incidence graphs h a η =
      ∑ Γ ∈ graphs, graphWeight incidence h a Γ * spinCharacter Γ η := by
  unfold polynomial graphWeight spinCharacter
  simp_rw [Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  ring

theorem second_moment (incidence : E → Finset V) (graphs : Finset (Finset E))
    (h : ℝ) (a : E → ℝ) :
    spinMean (fun η => polynomial incidence graphs h a η ^ 2) =
      ∑ Γ ∈ graphs, Real.tanh h ^ (2 * (boundary incidence Γ).card) *
        ∏ e ∈ Γ, a e ^ 2 := by
  simp_rw [polynomial_eq_characters]
  rw [polynomial_second_moment]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  simp only [graphWeight, mul_pow, ← Finset.prod_pow, ← pow_mul, Nat.mul_comm]

theorem mean_one (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) :
    spinMean (polynomial incidence edges.powerset h a) = 1 := by
  have heq : polynomial incidence edges.powerset h a =
      fun η => ∑ Γ ∈ edges.powerset, graphWeight incidence h a Γ * spinCharacter Γ η := by
    funext η
    exact polynomial_eq_characters incidence edges.powerset h a η
  rw [heq]
  simp_rw [spinMean_sum, spinMean_mul_left, mean_spinCharacter]
  simp [mul_ite, graphWeight, boundary, degree]

omit [Fintype E] [DecidableEq E] in
theorem polynomial_pos (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (ha : ∀ e ∈ edges, |a e| < 1) (η : E → Bool) :
    0 < polynomial incidence edges.powerset h a η := by
  rw [polynomial, ← Manuscript.FieldExpansion.graphical_expansion]
  unfold fieldMean
  apply Finset.sum_pos
  · intro σ hσ
    apply mul_pos (Finset.prod_pos (fun v hv => spinWeight_pos h _))
    apply Finset.prod_pos
    intro e he
    have habs : |a e * spinSign (η e) * edgeCharacter incidence σ e| < 1 := by
      simpa only [abs_mul, abs_spinSign, abs_edgeCharacter, mul_one] using ha e he
    linarith [(abs_lt.mp habs).1]
  · exact Finset.univ_nonempty

theorem noise_inflation_identity (incidence : E → Finset V)
    (graphs : Finset (Finset E)) (h : ℝ) (a : E → ℝ)
    (θ : ℝ) (hθ : θ ≠ 0) (η : E → Bool) :
    cubeNoise θ (polynomial incidence graphs h (fun e => a e / θ)) η =
      polynomial incidence graphs h a η := by
  have heq : polynomial incidence graphs h (fun e => a e / θ) =
      fun ζ => ∑ Γ ∈ graphs,
        graphWeight incidence h (fun e => a e / θ) Γ * spinCharacter Γ ζ := by
    funext ζ
    exact polynomial_eq_characters incidence graphs h _ ζ
  rw [heq, cubeNoise_polynomial, polynomial_eq_characters]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  have hc : (∏ e ∈ Γ, a e / θ) * θ ^ Γ.card = ∏ e ∈ Γ, a e := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    exact div_mul_cancel₀ _ (pow_ne_zero _ hθ)
  unfold graphWeight
  rw [mul_assoc (Real.tanh h ^ _) (∏ e ∈ Γ, a e / θ) (θ ^ Γ.card), hc]

omit [Fintype E] [DecidableEq E] in
theorem inflated_polynomial_pos (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (a : E → ℝ) (θ : ℝ)
    (ha : ∀ e ∈ edges, |a e / θ| ≤ 1 / 2) (η : E → Bool) :
    0 < polynomial incidence edges.powerset h (fun e => a e / θ) η := by
  apply polynomial_pos
  intro e he
  linarith [ha e he]

end Manuscript.SignPolynomial
