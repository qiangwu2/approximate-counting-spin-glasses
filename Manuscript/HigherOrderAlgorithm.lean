import Manuscript.HigherOrderTail
import Manuscript.HigherFieldExponent
import SpinGlass.AlgorithmBudgets

/-! The deterministic higher-order branch of Algorithm 4, including its actual
finite cutoff search and unconditional mean-square guarantee. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.HigherOrderAlgorithm
open MeasureTheory SpinGlass.Disorder SpinGlass.ArithmeticEvaluation
open Manuscript.Model Manuscript.MixedThreshold Manuscript.SupportExponent
open Manuscript.HigherOrderTail Manuscript.UniformMixedMass
open Manuscript.SupportDisorder Manuscript.DisorderOrthogonality

def budget (P : Finset ℕ) (a : ℕ → ℝ) (B rho u : ℝ) : ℝ :=
  SpinGlass.AlgorithmBudgets.logBudget (errorConstant P a B rho) u

def exactBranch (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin u : ℝ) : Prop :=
  N < Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin) ∨
    Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax)*N ≤
      budget P a B rho u

def selectedSize (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin h u : ℝ) : ℕ :=
  (Cutoffs.cutoffScan (kappaMin pmin)
    (HigherFieldExponent.selectedKappa N (max 1 rho) pmin h)
    (scale P a B rho pmin) N (budget P a B rho u)).found.getD 1

def selectedCutoff (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin h u : ℝ) : ℕ := by
  classical
  exact if exactBranch N pmax P a B rho pmin u then N
    else selectedSize N P a B rho pmin h u-1

def run (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin beta h u : ℝ)
    (J : Edge N P → ℝ) : Computation :=
  evaluator N P a beta h (selectedCutoff N pmax P a B rho pmin h u) J

@[simp] theorem run_value (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h u : ℝ) (J : Edge N P → ℝ) :
    (run N pmax P a B rho pmin beta h u J).value =
      retained N P a beta h (selectedCutoff N pmax P a B rho pmin h u) J :=
  evaluator_value _ _ _ _ _ _ _

@[simp] theorem full_retained (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N P → ℝ) :
    retained N P a beta h N J = Model.normalizedPartition N P a beta h J := by
  rw [normalizedPartition_eq_disorder_graph_sum]
  unfold retained
  congr 1
  apply Finset.filter_true_of_mem
  intro Γ hΓ
  simpa only [Fintype.card_fin] using Finset.card_le_univ (SupportEvaluation.support Subtype.val Γ)

/-- Finite bounded graph polynomials have integrable squared error independently
of the tail estimates. -/
theorem integrable_retained_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ) (k : ℕ) :
    Integrable (fun J => (Model.normalizedPartition N P a beta h J -
      retained N P a beta h k J)^2) (iidLaw μ) := by
  let A := (Finset.univ : Finset (Edge N P)).powerset
  let c := fun Γ : Finset (Edge N P) =>
    if (SupportEvaluation.support Subtype.val Γ).card ≤ k then 0
    else Real.tanh h^(FieldExpansion.boundary Subtype.val Γ).card
  have heq (J : Edge N P → ℝ) :
      Model.normalizedPartition N P a beta h J-retained N P a beta h k J =
      ∑ Γ ∈ A, c Γ*monomial (physicalScale N P a beta) Γ J := by
    rw [normalizedPartition_eq_disorder_graph_sum]
    simp only [retained,Finset.sum_filter,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro Γ hΓ
    dsimp only [c]
    split_ifs <;> simp [DisorderOrthogonality.graphWeight]
  simp_rw [heq,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply integrable_finsetSum _
  intro Γ hΓ
  apply integrable_finsetSum _
  intro Δ hΔ
  have hh := (integrable_monomial_mul μ (physicalScale N P a beta) Γ Δ).const_mul (c Γ*c Δ)
  exact hh.congr (Filter.Eventually.of_forall (fun J => by ring))

/-- Every actual deterministic return has a well-defined MSE. -/
theorem integrable_run_error (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin beta h u : ℝ) :
    Integrable (fun J => (Model.normalizedPartition N P a beta h J -
      (run N pmax P a B rho pmin beta h u J).value)^2) (iidLaw μ) := by
  simp_rw [run_value]
  exact integrable_retained_error μ N P a beta h _

/-- The complete higher-order mean-square guarantee of Proposition 5.2.
The constants and cutoff are computed from the supplied model and accuracy. -/
theorem mse_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (pmin : ℝ) (hpmin : 3 ≤ pmin)
    (horders : ∀ p ∈ P, pmin ≤ (p : ℝ)) (pmax : ℕ)
    (hmax : ∀ p ∈ P, p ≤ pmax) (hpN : ∀ p ∈ P, p ≤ N)
    {beta B h rho u : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ))) (hu : 0 < u) (hu1 : u < 1) :
    (∫ J, (Model.normalizedPartition N P a beta h J -
      (run N pmax P a B rho pmin beta h u J).value)^2 ∂iidLaw μ) ≤ u := by
  classical
  have hp : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have hh := hpmin.trans (horders p hp)
    have h3 : 3 ≤ p := by exact_mod_cast hh
    omega
  have hC : 0 ≤ massConstant P a (betaPlus P a B^2) rho :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (massConstant_ge_one P a hP ha hp
      (betaPlus_sq_range P a hP ha hp hB hBT).1.le
      (betaPlus_sq_range P a hP ha hp hB hBT).2)
  have hLam : 0 < budget P a B rho u :=
    SpinGlass.AlgorithmBudgets.logBudget_pos (by unfold errorConstant; linarith) hu hu1
  by_cases hex : exactBranch N pmax P a B rho pmin u
  · simp only [run_value,selectedCutoff,if_pos hex,full_retained,sub_self,zero_pow (by decide : (2:ℕ)≠0),integral_zero]
    exact hu.le
  · have hN0 : Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin) ≤ N := by
      exact Nat.le_of_not_gt (fun hn => hex (Or.inl hn))
    have hsmall : budget P a B rho u <
      Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax)*N :=
      lt_of_not_ge (fun hl => hex (Or.inr hl))
    have hN4 : 4 ≤ N := (Cutoffs.sizeThreshold_ge_four _ _ _).trans hN0
    have hNs : 2/Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin) ≤ (N : ℝ) :=
      (Cutoffs.sizeThreshold_ge_scale _ _ _).trans (by exact_mod_cast hN0)
    have hf : |h| ≤ max 1 rho*(N : ℝ)^(-(1/4 : ℝ)) :=
      hfield.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    have halpha := HigherFieldExponent.alpha_ge_quarter N hN4 (le_max_left 1 rho) hpmin hf
    have hkap := kappa_ge_kappaMin pmin _ hpmin halpha
    obtain ⟨m,hm,hm1,hmrange,hmPhi,hmfirst⟩ := Cutoffs.cutoffScan_correct
      (kappaMin_pos pmin hpmin) hkap (scale_pos P a B rho pmin) hNs hLam hsmall
    have hselected : selectedSize N P a B rho pmin h u = m := by
      unfold selectedSize HigherFieldExponent.selectedKappa
      rw [hm]
      rfl
    have hcut : m-1 < Nat.floor (Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin)*N) := by omega
    have htail := physical_support_tail μ hμ hunit N P a hP ha pmin hpmin horders pmax hmax hpN
      hbeta hbetaB hB hBT hfield halpha
      (HigherFieldExponent.field_le N (by omega) (by positivity)) (m-1) hcut
    have he := Cutoffs.selected_error_bounds hsmall.le hmPhi
    have hcoef := mul_le_mul_of_nonneg_left he.2 hC
    have hstep : m-1+1=m := by omega
    have hstepR : ((m-1 : ℕ) : ℝ)+1 = (m : ℝ) := by exact_mod_cast hstep
    rw [hstepR] at htail
    calc
      _ = ∫ J, (Model.normalizedPartition N P a beta h J - (evaluator N P a beta h (m-1) J).value)^2 ∂iidLaw μ := by
        simp only [run,selectedCutoff,if_neg hex,hselected]
      _ ≤ _ := htail
      _ ≤ 2*Real.exp (-budget P a B rho u)+massConstant P a (betaPlus P a B^2) rho*Real.exp (-4*budget P a B rho u) := by
        have hfirst := mul_le_mul_of_nonneg_left he.1 (show (0 : ℝ) ≤ 2 by norm_num)
        exact add_le_add hfirst hcoef
      _ ≤ u := SpinGlass.AlgorithmBudgets.support_error_budget hC hu hu1

end Manuscript.HigherOrderAlgorithm
