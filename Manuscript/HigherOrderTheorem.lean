import Manuscript.HigherOrderAlgorithm
import Manuscript.LogApprox

/-! The actual higher-order branch of Algorithm 1, under its original iid law.
All truncation and lower-tail estimates are discharged by the preceding modules. -/

noncomputable section
namespace Manuscript.HigherOrderTheorem
open MeasureTheory SpinGlass.Disorder
open Manuscript.Model Manuscript.MixedThreshold

def approximation (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h epsilon delta : ℝ) (J : Edge N P → ℝ) : ℝ :=
  SpinGlass.logOutput (InputPreparation.logBase N P a beta h J)
    (HigherOrderAlgorithm.run N pmax P a B rho pmin beta h
      (LogApprox.mseBudget P a B rho epsilon delta) J).value

/-- Theorem 1.1's complete probability conclusion for the higher-order branch.
There is no assumed error estimate, integrability, or graphical-mass bound. -/
theorem accuracy (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (hP : P.Nonempty)
    (ha : ∀ p ∈ P, 0 < a p) (pmin : ℝ) (hpmin : 3 ≤ pmin)
    (horders : ∀ p ∈ P, pmin ≤ (p : ℝ)) (pmax : ℕ)
    (hmax : ∀ p ∈ P, p ≤ pmax) (hpN : ∀ p ∈ P, p ≤ N)
    {beta B h rho epsilon delta : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)))
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    (iidLaw μ).real {J | epsilon <
      |approximation N pmax P a B rho pmin beta h epsilon delta J -
        Real.log (Model.partition N P a beta h J)|} ≤
      delta + OriginalLawLowerTail.tau μ N P a B (theta P a B) := by
  have hp : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have h3 : (3 : ℝ) ≤ p := hpmin.trans (horders p hp)
    have h3' : 3 ≤ p := by exact_mod_cast h3
    omega
  have hu := LogApprox.budgets_range P a hP ha hp (rho := rho) hB hBT he he1 hd hd1
  have hi := HigherOrderAlgorithm.integrable_run_error μ N pmax P a B rho pmin beta h
    (LogApprox.mseBudget P a B rho epsilon delta)
  have hm := HigherOrderAlgorithm.mse_bound μ hμ hunit N P a hP ha pmin hpmin horders
    pmax hmax hpN hbeta hbetaB hB hBT hfield hu.2.2.1 (by linarith [hu.2.2.2])
  have heq (x y : ℝ) : (x-y)^2 = (y-x)^2 := by ring
  simp_rw [heq (Model.normalizedPartition N P a beta h _)] at hi hm
  exact LogApprox.probability_of_mse μ hμ hunit N P a hP ha hp hpN hB hBT hbeta hbetaB
    hfield he he1 hd _ hi hm

end Manuscript.HigherOrderTheorem
