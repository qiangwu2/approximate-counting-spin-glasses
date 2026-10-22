import Manuscript.InputPreparation
import Manuscript.UniformLowerTail

/-! Algorithm 1's concrete budgets and logarithmic output. The lower-tail
estimate is discharged here. The graph-approximation MSE is an explicit input
to this assembly lemma, to be supplied by the two implemented branches. -/

noncomputable section
namespace Manuscript.LogApprox
open MeasureTheory SpinGlass.Disorder
open Manuscript.MixedThreshold Manuscript.UniformMixedMass
open SpinGlass.ArithmeticEvaluation Manuscript.InputPreparation

def constant (P : Finset ℕ) (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  massConstant P a (betaPlus P a B ^ 2) rho

def exponent (P : Finset ℕ) (a : ℕ → ℝ) (B : ℝ) : ℝ :=
  ConditionalLowerTail.exponent (theta P a B)

def threshold (P : Finset ℕ) (a : ℕ → ℝ) (B rho delta : ℝ) : ℝ :=
  SpinGlass.accuracyThreshold (constant P a B rho) delta (exponent P a B)

def mseBudget (P : Finset ℕ) (a : ℕ → ℝ) (B rho epsilon delta : ℝ) : ℝ :=
  SpinGlass.accuracyMSEBudget (constant P a B rho) delta epsilon (exponent P a B)

theorem exponent_pos (P : Finset ℕ) (a : ℕ → ℝ) {B : ℝ}
    (hB : 0 < B) (hBT : B < betaF P a) : 0 < exponent P a B :=
  ConditionalLowerTail.exponent_pos (theta_range P a hB hBT).1 (theta_range P a hB hBT).2

theorem constant_ge_one (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) {B rho : ℝ}
    (hB : 0 < B) (hBT : B < betaF P a) : 1 ≤ constant P a B rho :=
  massConstant_ge_one P a hP ha hp (sq_nonneg _) (betaPlus_sq_range P a hP ha hp hB hBT).2

theorem budgets_range (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) {B rho epsilon delta : ℝ}
    (hB : 0 < B) (hBT : B < betaF P a)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    0 < threshold P a B rho delta ∧ threshold P a B rho delta < 1 ∧
      0 < mseBudget P a B rho epsilon delta ∧ mseBudget P a B rho epsilon delta < 1 / 8 := by
  have hC := constant_ge_one P a hP ha hp (rho := rho) hB hBT
  have hs := exponent_pos P a hB hBT
  have hz := SpinGlass.accuracyThreshold_pos (s := exponent P a B) (by linarith : 0 < constant P a B rho) hd
  have hz1 := SpinGlass.accuracyThreshold_lt_one hC hd hd1 hs
  refine ⟨hz, hz1, SpinGlass.accuracyMSEBudget_pos (by linarith) hd he, ?_⟩
  change delta * epsilon ^ 2 * SpinGlass.accuracyThreshold (constant P a B rho) delta (exponent P a B) ^ 2 / 8 < 1 / 8
  have he2 : epsilon ^ 2 < 1 := by nlinarith
  have hz2 : SpinGlass.accuracyThreshold (constant P a B rho) delta (exponent P a B) ^ 2 < 1 := by nlinarith
  calc
    _ < (1 : ℝ) * 1 * 1 / 8 := by gcongr
    _ = _ := by norm_num

/-- This is the actual final test, optional logarithm, and addition. -/
def finish {N : ℕ} {P : Finset ℕ} (input : PreparedInput N P) (correction : Computation) : Computation :=
  let l := if 0 < correction.value then logarithm (literal correction.value) else literal 0
  let result := add (literal input.logPrefactor) l
  ⟨result.value, input.operations + correction.operations + 1 + result.operations⟩

theorem finish_value {N : ℕ} {P : Finset ℕ} (input : PreparedInput N P) (correction : Computation) :
    (finish input correction).value = SpinGlass.logOutput input.logPrefactor correction.value := by
  unfold finish SpinGlass.logOutput
  split_ifs <;> rfl

theorem finish_operations {N : ℕ} {P : Finset ℕ} (input : PreparedInput N P) (correction : Computation) :
    (finish input correction).operations ≤ input.operations + correction.operations + 3 := by
  unfold finish
  split_ifs <;> simp only [add, logarithm, literal] <;> omega

def output {Ω : Type*} (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (T : Ω → (Model.Edge N P → ℝ) → ℝ) (ω : Ω) (J : Model.Edge N P → ℝ) : ℝ :=
  SpinGlass.logOutput (InputPreparation.logBase N P a beta h J) (T ω J)

theorem disorder_event_probability {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {E : Type*} [Fintype E] (S : Set (E → ℝ)) :
    (Q.prod (iidLaw μ)).real {ωJ : Ω × (E → ℝ) | ωJ.2 ∈ S} = (iidLaw μ).real S := by
  have heq : {ωJ : Ω × (E → ℝ) | ωJ.2 ∈ S} = Set.univ ×ˢ S := by ext x; simp
  rw [heq, measureReal_prod_prod]
  simp [Measure.real]

/-- The uniform original-law lower-tail estimate is fully discharged. Supplying
the actual graph branch's proved MSE and integrability gives Algorithm 1's exact
delta-plus-tau guarantee on the joint disorder/randomness space. -/
theorem probability_of_joint_mse {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) (hpN : ∀ p ∈ P, p ≤ N)
    {B beta h rho epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaF P a)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ)))
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1)
    (T : Ω → (Model.Edge N P → ℝ) → ℝ)
    (hE : Integrable (fun ωJ : Ω × (Model.Edge N P → ℝ) =>
      (T ωJ.1 ωJ.2 - Model.normalizedPartition N P a beta h ωJ.2) ^ 2) (Q.prod (iidLaw μ)))
    (hmse : (∫ ωJ : Ω × (Model.Edge N P → ℝ),
      (T ωJ.1 ωJ.2 - Model.normalizedPartition N P a beta h ωJ.2) ^ 2 ∂Q.prod (iidLaw μ)) ≤
        mseBudget P a B rho epsilon delta) :
    (Q.prod (iidLaw μ)).real {ωJ : Ω × (Model.Edge N P → ℝ) |
      epsilon < |output N P a beta h T ωJ.1 ωJ.2 - Real.log (Model.partition N P a beta h ωJ.2)|} ≤
        delta + OriginalLawLowerTail.tau μ N P a B (theta P a B) := by
  have hC := constant_ge_one P a hP ha hp (rho := rho) hB hBT
  have hC0 : 0 < constant P a B rho := by linarith
  have hs := exponent_pos P a hB hBT
  have hz := SpinGlass.accuracyThreshold_pos (s := exponent P a B) hC0 hd
  have hlower := UniformLowerTail.physical_lower_tail_uniform μ hμ hunit N P a hP ha hp hpN
    hbeta hbetaB hB hBT hfield hz
  simp_rw [output, targetLog_decomposition]
  rw [add_comm delta]
  apply SpinGlass.logOutput_probability_with_paper_parameters (Q.prod (iidLaw μ))
    (fun ωJ : Ω × (Model.Edge N P → ℝ) => InputPreparation.logBase N P a beta h ωJ.2)
    (fun ωJ => T ωJ.1 ωJ.2) (fun ωJ => Model.normalizedPartition N P a beta h ωJ.2)
    hE hC0 hd he he1.le hs _ hmse
  have hprob := disorder_event_probability Q μ
    {J : Model.Edge N P → ℝ | Model.normalizedPartition N P a beta h J < threshold P a B rho delta}
  simp only [Set.mem_setOf_eq, threshold] at hprob
  rw [hprob]
  simpa only [constant, exponent, add_comm] using hlower

/-- Deterministic specialization used by the higher-order support evaluator. -/
theorem probability_of_mse
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (hp : ∀ p ∈ P, 2 ≤ p) (hpN : ∀ p ∈ P, p ≤ N)
    {B beta h rho epsilon delta : ℝ} (hB : 0 < B) (hBT : B < betaF P a)
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ)))
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta)
    (T : (Model.Edge N P → ℝ) → ℝ)
    (hE : Integrable (fun J => (T J - Model.normalizedPartition N P a beta h J) ^ 2) (iidLaw μ))
    (hmse : (∫ J, (T J - Model.normalizedPartition N P a beta h J) ^ 2 ∂iidLaw μ) ≤
      mseBudget P a B rho epsilon delta) :
    (iidLaw μ).real {J | epsilon <
      |SpinGlass.logOutput (InputPreparation.logBase N P a beta h J) (T J) -
        Real.log (Model.partition N P a beta h J)|} ≤
          delta + OriginalLawLowerTail.tau μ N P a B (theta P a B) := by
  have hC := constant_ge_one P a hP ha hp (rho := rho) hB hBT
  have hC0 : 0 < constant P a B rho := by linarith
  have hs := exponent_pos P a hB hBT
  have hz := SpinGlass.accuracyThreshold_pos (s := exponent P a B) hC0 hd
  have hlower := UniformLowerTail.physical_lower_tail_uniform μ hμ hunit N P a hP ha hp hpN
    hbeta hbetaB hB hBT hfield hz
  simp_rw [targetLog_decomposition]
  rw [add_comm delta]
  apply SpinGlass.logOutput_probability_with_paper_parameters (iidLaw μ)
    (InputPreparation.logBase N P a beta h) T (Model.normalizedPartition N P a beta h)
    hE hC0 hd he he1.le hs _ hmse
  simpa only [constant, exponent, add_comm] using hlower

end Manuscript.LogApprox
