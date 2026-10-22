import Manuscript.Model
import SpinGlass.DisorderIndependentCoefficients

/-!
# Orthogonality for the actual symmetric iid real disorder law

This file proves Lemma 2.1 with the field boundary factors, including arbitrary
square-integrable coefficients on an independent probability space. It also
proves the exact retained-family squared-error identity. The distribution is an
actual finite product measure, not a finite sign-cube proxy. No uniform graphical
mass, truncation-error bound or higher disorder moment is presumed.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.DisorderOrthogonality
open MeasureTheory
open SpinGlass.Disorder

variable {V E Ω : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [MeasurableSpace Ω]

/-- The manuscript's `W_h(Γ)` as a function of the actual disorder input. -/
def graphWeight (incidence : E → Finset V) (h : ℝ) (a : E → ℝ)
    (Γ : Finset E) (J : E → ℝ) : ℝ :=
  Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card * monomial a Γ J

omit [Fintype E] [DecidableEq E] in
theorem graphWeight_eq_fieldGraphWeight (incidence : E → Finset V) (h : ℝ)
    (a : E → ℝ) (Γ : Finset E) (J : E → ℝ) :
    graphWeight incidence h a Γ J = FieldExpansion.graphWeight incidence h
      (fun e => Real.tanh (a e * J e)) Γ := rfl

/-- Equation (16), allowing the scale to depend on the edge order. -/
theorem monomial_pair_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (a : E → ℝ) (Γ Γ' : Finset E) :
    (∫ J, monomial a Γ J * monomial a Γ' J ∂iidLaw μ) =
      if Γ = Γ' then ∏ e ∈ Γ, secondMoment μ (a e) else 0 :=
  SpinGlass.Disorder.monomial_orthogonality μ hμ a Γ Γ'

omit [DecidableEq E] in
/-- Every graph monomial product is genuinely integrable. -/
theorem integrable_graphWeight_mul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (incidence : E → Finset V) (h : ℝ) (a : E → ℝ) (Γ Γ' : Finset E) :
    Integrable (fun J => graphWeight incidence h a Γ J * graphWeight incidence h a Γ' J)
      (iidLaw μ) := by
  have hi := (integrable_monomial_mul μ a Γ Γ').const_mul
    (Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card *
      Real.tanh h ^ (FieldExpansion.boundary incidence Γ').card)
  simpa only [graphWeight, mul_mul_mul_comm] using hi

/-- Field-weighted orthogonality under the original iid law. -/
theorem graphWeight_pair_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (h : ℝ)
    (a : E → ℝ) (Γ Γ' : Finset E) :
    (∫ J, graphWeight incidence h a Γ J * graphWeight incidence h a Γ' J ∂iidLaw μ) =
      if Γ = Γ' then Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
        ∏ e ∈ Γ, secondMoment μ (a e) else 0 := by
  simp_rw [graphWeight, mul_mul_mul_comm]
  rw [integral_const_mul, SpinGlass.Disorder.monomial_orthogonality μ hμ]
  by_cases heq : Γ = Γ'
  · subst Γ'
    simp only [ite_true, ← sq, ← pow_mul]
    rw [Nat.mul_comm (FieldExpansion.boundary incidence Γ).card 2]
  · simp [heq]

/-- Equation (17) for arbitrary square-integrable independent coefficients.
The coefficients may be mutually dependent: their entire array is carried by Ω. -/
theorem independent_coefficients_second_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (incidence : E → Finset V) (h : ℝ) (a : E → ℝ)
    (A : Finset (Finset E)) (c : Ω → Finset E → ℝ)
    (hc : ∀ Γ ∈ A, Measurable (fun ω => c ω Γ))
    (hcsq : ∀ Γ ∈ A, Integrable (fun ω => c ω Γ ^ 2) P) :
    (∫ ωJ : Ω × (E → ℝ),
      (∑ Γ ∈ A, c ωJ.1 Γ * graphWeight incidence h a Γ ωJ.2) ^ 2
        ∂P.prod (iidLaw μ)) =
      ∑ Γ ∈ A, (∫ ω, c ω Γ ^ 2 ∂P) *
        Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
          ∏ e ∈ Γ, secondMoment μ (a e) := by
  have hc' (Γ : Finset E) (hΓ : Γ ∈ A) :
      Measurable (fun ω => c ω Γ * Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) :=
    (hc Γ hΓ).mul_const _
  have hcsq' (Γ : Finset E) (hΓ : Γ ∈ A) :
      Integrable (fun ω =>
        (c ω Γ * Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) ^ 2) P := by
    simpa only [mul_pow] using (hcsq Γ hΓ).mul_const
      ((Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) ^ 2)
  have hid := SpinGlass.Disorder.independent_coefficients_second_moment μ hμ P a A
    (fun ω Γ => c ω Γ * Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) hc' hcsq'
  simpa only [graphWeight, ← mul_assoc, mul_pow, integral_mul_const, ← pow_mul,
    Nat.mul_comm _ 2] using hid

/-- The same identity for the error between two independent-coefficient estimators. -/
theorem independent_coefficient_error_second_moment (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (incidence : E → Finset V) (h : ℝ) (a : E → ℝ)
    (A : Finset (Finset E)) (c d : Ω → Finset E → ℝ)
    (hcd : ∀ Γ ∈ A, Measurable (fun ω => c ω Γ - d ω Γ))
    (hcdsq : ∀ Γ ∈ A, Integrable (fun ω => (c ω Γ - d ω Γ) ^ 2) P) :
    (∫ ωJ : Ω × (E → ℝ),
      ((∑ Γ ∈ A, c ωJ.1 Γ * graphWeight incidence h a Γ ωJ.2) -
        (∑ Γ ∈ A, d ωJ.1 Γ * graphWeight incidence h a Γ ωJ.2)) ^ 2
          ∂P.prod (iidLaw μ)) =
      ∑ Γ ∈ A, (∫ ω, (c ω Γ - d ω Γ) ^ 2 ∂P) *
        Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
          ∏ e ∈ Γ, secondMoment μ (a e) := by
  have heq (ωJ : Ω × (E → ℝ)) :
      (∑ Γ ∈ A, c ωJ.1 Γ * graphWeight incidence h a Γ ωJ.2) -
        (∑ Γ ∈ A, d ωJ.1 Γ * graphWeight incidence h a Γ ωJ.2) =
      ∑ Γ ∈ A, (c ωJ.1 Γ - d ωJ.1 Γ) * graphWeight incidence h a Γ ωJ.2 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
  simp_rw [heq]
  exact independent_coefficients_second_moment μ hμ P incidence h a A
    (fun ω Γ => c ω Γ - d ω Γ) hcd hcdsq

/-- Square integrability of the expression whose expectation appears in (17). -/
theorem integrable_independent_graph_square (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (incidence : E → Finset V) (h : ℝ) (a : E → ℝ)
    (A : Finset (Finset E)) (c : Ω → Finset E → ℝ)
    (hc : ∀ Γ ∈ A, Measurable (fun ω => c ω Γ))
    (hcsq : ∀ Γ ∈ A, Integrable (fun ω => c ω Γ ^ 2) P) :
    Integrable (fun ωJ : Ω × (E → ℝ) =>
      (∑ Γ ∈ A, c ωJ.1 Γ * graphWeight incidence h a Γ ωJ.2) ^ 2)
        (P.prod (iidLaw μ)) := by
  have hc' (Γ : Finset E) (hΓ : Γ ∈ A) :
      Measurable (fun ω => c ω Γ * Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) :=
    (hc Γ hΓ).mul_const _
  have hcsq' (Γ : Finset E) (hΓ : Γ ∈ A) :
      Integrable (fun ω =>
        (c ω Γ * Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) ^ 2) P := by
    simpa only [mul_pow] using (hcsq Γ hΓ).mul_const
      ((Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) ^ 2)
  simpa only [graphWeight, ← mul_assoc] using
    SpinGlass.Disorder.integrable_independent_polynomial_square μ P a A
      (fun ω Γ => c ω Γ * Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) hc' hcsq'

/-- Deterministic field-weighted Parseval identity. -/
theorem deterministic_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (h : ℝ) (a : E → ℝ)
    (A : Finset (Finset E)) (c : Finset E → ℝ) :
    (∫ J, (∑ Γ ∈ A, c Γ * graphWeight incidence h a Γ J) ^ 2 ∂iidLaw μ) =
      ∑ Γ ∈ A, c Γ ^ 2 * Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
        ∏ e ∈ Γ, secondMoment μ (a e) := by
  have hid := SpinGlass.Disorder.polynomial_second_moment μ hμ a A
    (fun Γ => c Γ * Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card)
  simpa only [graphWeight, ← mul_assoc, mul_pow, ← pow_mul, Nat.mul_comm _ 2] using hid

/-- Equation (18), for any deterministically selected family of retained graphs. -/
theorem retained_family_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (incidence : E → Finset V) (h : ℝ) (a : E → ℝ)
    (A : Finset (Finset E)) (keep : Finset E → Prop) [DecidablePred keep] :
    (∫ J, ((∑ Γ ∈ A, graphWeight incidence h a Γ J) -
      (∑ Γ ∈ A.filter keep, graphWeight incidence h a Γ J)) ^ 2 ∂iidLaw μ) =
      ∑ Γ ∈ A.filter (fun Γ => ¬keep Γ),
        Real.tanh h ^ (2 * (FieldExpansion.boundary incidence Γ).card) *
          ∏ e ∈ Γ, secondMoment μ (a e) := by
  have hid := SpinGlass.Disorder.retained_polynomial_error μ hμ a A
    (fun Γ => Real.tanh h ^ (FieldExpansion.boundary incidence Γ).card) keep
  simpa only [graphWeight, ← pow_mul, Nat.mul_comm _ 2] using hid


/-- The scale `beta*a_p/N^((p-1)/2)` on the exact physical mixed-edge domain. -/
def physicalScale (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (e : Model.Edge N P) : ℝ :=
  beta * a e.val.card / Model.scaleDenominator N e.val.card

theorem coefficient_eq_physicalScale (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta : ℝ) (J : Model.Edge N P → ℝ) (e : Model.Edge N P) :
    Model.coefficient N P a beta J e = physicalScale N P a beta e * J e := by
  unfold Model.coefficient physicalScale
  ring

/-- The original mixed-field normalized partition is exactly the disorder polynomial. -/
theorem normalizedPartition_eq_disorder_graph_sum (N : ℕ) (P : Finset ℕ)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Model.Edge N P → ℝ) :
    Model.normalizedPartition N P a beta h J =
      ∑ Γ ∈ (Finset.univ : Finset (Model.Edge N P)).powerset,
        graphWeight Subtype.val h (physicalScale N P a beta) Γ J := by
  rw [Model.normalizedPartition_eq_graph_sum]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  rw [graphWeight_eq_fieldGraphWeight]
  simp_rw [coefficient_eq_physicalScale]

/-- The exact second moment of the manuscript's original mixed-field partition. -/
theorem normalizedPartition_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ) :
    (∫ J : Model.Edge N P → ℝ, Model.normalizedPartition N P a beta h J ^ 2 ∂iidLaw μ) =
      ∑ Γ ∈ (Finset.univ : Finset (Model.Edge N P)).powerset,
        Real.tanh h ^ (2 * (FieldExpansion.boundary Subtype.val Γ).card) *
          ∏ e ∈ Γ, secondMoment μ (physicalScale N P a beta e) := by
  simp_rw [normalizedPartition_eq_disorder_graph_sum]
  simpa only [one_mul, one_pow] using deterministic_second_moment μ hμ
    (Subtype.val : Model.Edge N P → Finset (Fin N)) h (physicalScale N P a beta)
    Finset.univ.powerset (fun _ => 1)

/-- Equation (18), directly for the manuscript's partition and physical disorder law. -/
theorem physical_retained_family_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (keep : Finset (Model.Edge N P) → Prop) [DecidablePred keep] :
    (∫ J : Model.Edge N P → ℝ,
      (Model.normalizedPartition N P a beta h J -
        ∑ Γ ∈ (Finset.univ : Finset (Model.Edge N P)).powerset.filter keep,
          graphWeight Subtype.val h (physicalScale N P a beta) Γ J) ^ 2 ∂iidLaw μ) =
      ∑ Γ ∈ (Finset.univ : Finset (Model.Edge N P)).powerset.filter (fun Γ => ¬keep Γ),
        Real.tanh h ^ (2 * (FieldExpansion.boundary Subtype.val Γ).card) *
          ∏ e ∈ Γ, secondMoment μ (physicalScale N P a beta e) := by
  simp_rw [normalizedPartition_eq_disorder_graph_sum]
  exact retained_family_error μ hμ Subtype.val h (physicalScale N P a beta)
    Finset.univ.powerset keep

end Manuscript.DisorderOrthogonality
