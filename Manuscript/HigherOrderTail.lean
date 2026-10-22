import Manuscript.SupportExecution
import Manuscript.UniformPhysicalMass
import Manuscript.Cutoffs

/-! Unconditional physical higher-order support truncation, Proposition 3.2. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.HigherOrderTail
open MeasureTheory SpinGlass.Disorder Manuscript.Model Manuscript.MixedThreshold
open Manuscript.MixedCoefficient Manuscript.UniformMixedMass Manuscript.UniformGraphMass
open Manuscript.SupportMassScale Manuscript.SupportDisorder
open Manuscript.DisorderOrthogonality Manuscript.SupportExponent

def edgeIntensity (a : ℕ → ℝ) (B : ℝ) (p : ℕ) : ℝ := B^2*a p^2

def scale (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) : ℝ :=
  supportScale P (edgeIntensity a B) (max 1 rho) pmin

def c1 (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) (pmax : ℕ) : ℝ :=
  Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin)/(pmax : ℝ)*
    Real.log (1/(theta P a B)^2)

def errorConstant (P : Finset ℕ) (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  8*(2+massConstant P a (betaPlus P a B^2) rho)

theorem scale_pos (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) :
    0 < scale P a B rho pmin :=
  supportScale_pos P (edgeIntensity a B) (max 1 rho) pmin
    (fun p hp => by unfold edgeIntensity; positivity) (le_max_left _ _)

theorem c1_pos (P : Finset ℕ) (a : ℕ → ℝ) {B rho pmin : ℝ} {pmax : ℕ}
    (hB : 0 < B) (hBT : B < betaF P a) (hpmax : 0 < pmax) :
    0 < c1 P a B rho pmin pmax := by
  obtain ⟨ht,ht1⟩ := theta_range P a hB hBT
  have hs : 0 < theta P a B^2 := sq_pos_of_pos ht
  have hs1 : theta P a B^2 < 1 := by nlinarith
  apply mul_pos (div_pos (Cutoffs.gamma_pos (scale_pos P a B rho pmin)) (by exact_mod_cast hpmax))
  exact Real.log_pos ((one_lt_div hs).mpr hs1)

/-- The actual support evaluator, with the physical normalization and field. -/
def evaluator (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (k : ℕ) (J : Edge N P → ℝ) : SpinGlass.ArithmeticEvaluation.Computation :=
  SupportExecution.supportSum Subtype.val Finset.univ (FieldExpansion.spinWeight h)
    (fun e => weight (physicalScale N P a beta e) (J e)) k

@[simp] theorem evaluator_value (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (k : ℕ) (J : Edge N P → ℝ) :
    (evaluator N P a beta h k J).value = retained N P a beta h k J := by
  rw [evaluator,SupportExecution.supportSum_value]
  rfl

/-- There are no assumed mass estimates in this physical MSE theorem. -/
theorem physical_support_tail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (pmin : ℝ) (hpmin : 3 ≤ pmin)
    (horders : ∀ p ∈ P, pmin ≤ (p : ℝ)) (pmax : ℕ)
    (hmax : ∀ p ∈ P, p ≤ pmax) (hpN : ∀ p ∈ P, p ≤ N)
    {beta B h rho alpha : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)))
    (halpha : (1 : ℝ)/4 ≤ alpha)
    (hfieldAlpha : |Real.tanh h| ≤ max 1 rho*(N : ℝ)^(-alpha))
    (k : ℕ) (hcut : k < Nat.floor
      (Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin)*N)) :
    (∫ J, (Model.normalizedPartition N P a beta h J - (evaluator N P a beta h k J).value)^2
      ∂iidLaw μ) ≤
      2*Real.exp (-SpinGlass.CutoffTail.phi (kappa pmin alpha) (scale P a B rho pmin) N (k+1)) +
      massConstant P a (betaPlus P a B^2) rho * Real.exp (-c1 P a B rho pmin pmax*N) := by
  have hp : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have hh := (hpmin.trans (horders p hp))
    have h3 : 3 ≤ p := by exact_mod_cast hh
    omega
  have hpmax : 0 < pmax := by
    obtain ⟨p,hpP⟩ := hP
    have := hp p hpP
    have := hmax p hpP
    omega
  have hplus : 0 < betaPlus P a B := hB.trans (betaPlus_range P a hB hBT).2.1
  obtain ⟨ht,ht1⟩ := theta_range P a hB hBT
  have hq : 0 < theta P a B^2 := sq_pos_of_pos ht
  have hq1 : theta P a B^2 ≤ 1 := by nlinarith
  simp_rw [evaluator_value]
  rw [retained_error_eq_tail μ hμ]
  apply SupportTail.support_truncation_tail Subtype.val Finset.univ
    (fun _ _ _ _ hh => Subtype.ext hh) P (fun e he => edge_order_mem e)
    pmin hpmin horders pmax N k hpmax (Fintype.card_fin N)
    (fun e he => hmax _ (edge_order_mem e)) h (max 1 rho) alpha
    (le_max_left _ _) halpha hfieldAlpha (edgeIntensity a B)
    (fun p hp => by unfold edgeIntensity; positivity)
    (fun e => secondMoment μ (physicalScale N P a beta e))
    (comparisonWeight N P a (betaPlus P a B^2))
    (fun e => secondMoment_nonneg μ _)
    (fun e => (comparisonWeight_range N P a hP ha hp hpN
      (betaPlus_sq_range P a hP ha hp hB hBT).1.le
      (betaPlus_sq_range P a hP ha hp hB hBT).2 e).1)
    (fun e he => secondMoment_physical_le_bound μ hunit N P a hbeta hbetaB e
      (by have := hp _ (edge_order_mem e); omega)) hq hq1
    (fun e => secondMoment_physical_le_ratio μ hunit N P a hbeta hbetaB hB hplus e
      (by have := hp _ (edge_order_mem e); omega))
    (uniform_graphical_mass_midpoint N P a hP ha hp hpN hB hBT hfield)
    (Cutoffs.gamma_pos (scale_pos P a B rho pmin))
    (Cutoffs.gamma_le_one _ _)
    (Cutoffs.gamma_gap_variable (kappaMin_pos pmin hpmin)
      (kappa_ge_kappaMin pmin alpha hpmin halpha) (scale_pos P a B rho pmin)) hcut

end Manuscript.HigherOrderTail
