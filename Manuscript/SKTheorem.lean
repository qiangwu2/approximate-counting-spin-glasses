import Manuscript.SKAlgorithm

/-! The original-law logarithmic accuracy theorem for weak-field SK. -/

noncomputable section
namespace Manuscript.SKTheorem
open MeasureTheory SpinGlass.Disorder
open Manuscript.Model Manuscript.MixedThreshold

abbrev Colors (N : ℕ) (a : ℕ → ℝ) (B rho epsilon delta : ℝ) :=
  SKAlgorithm.Colors N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta)

def colorLaw (N : ℕ) (a : ℕ → ℝ) (B rho epsilon delta : ℝ) :
    Measure (Colors N a B rho epsilon delta) :=
  SKAlgorithm.colorLaw N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta)

def approximation (N : ℕ) (a : ℕ → ℝ) (B rho beta h epsilon delta : ℝ)
    (χ : Colors N a B rho epsilon delta) (J : Edge N {2} → ℝ) : ℝ :=
  LogApprox.output N {2} a beta h
    (SKAlgorithm.run N a B rho beta h (LogApprox.mseBudget {2} a B rho epsilon delta)) χ J

/-- The SK accuracy conclusion of Theorem 1.1, with all analytic and
probabilistic estimates discharged for the actual mixed-model specialization. -/
theorem accuracy (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℝ) (ha : a 2 = 1)
    {beta B h rho epsilon delta : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hB1 : B < 1)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)))
    (he : 0 < epsilon) (he1 : epsilon < 1) (hd : 0 < delta) (hd1 : delta < 1) :
    ((colorLaw N a B rho epsilon delta).prod (iidLaw μ)).real
      {χJ : Colors N a B rho epsilon delta × (Edge N {2} → ℝ) | epsilon <
        |approximation N a B rho beta h epsilon delta χJ.1 χJ.2-
          Real.log (Model.partition N {2} a beta h χJ.2)|} ≤
      delta + OriginalLawLowerTail.tau μ N {2} a B (theta {2} a B) := by
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  have hu := LogApprox.budgets_range {2} a (by simp) (by simpa [ha]) (by simp)
    (rho := rho) hB hBT he he1 hd hd1
  have hu1 : LogApprox.mseBudget {2} a B rho epsilon delta < 1 := by linarith [hu.2.2.2]
  have hL := SKAlgorithm.edgeLimit_pos a ha (rho := rho) hB hB1 hu.2.2.1 hu1
  letI : Nonempty (Fin (2*SKAlgorithm.edgeLimit a B rho (LogApprox.mseBudget {2} a B rho epsilon delta))) :=
    ⟨⟨0,by omega⟩⟩
  letI : IsProbabilityMeasure (SKAlgorithm.colorLaw N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta)) := by
    unfold SKAlgorithm.colorLaw
    infer_instance
  exact LogApprox.probability_of_joint_mse
    (SKAlgorithm.colorLaw N a B rho (LogApprox.mseBudget {2} a B rho epsilon delta))
    μ hμ hunit N {2} a (by simp) (by simpa [ha]) (by simp) (by simpa using hN)
    hB hBT hbeta hbetaB hfield he he1 hd hd1 _
    (SKAlgorithm.partition_error_integrable μ N a ha hB hB1 hu.2.2.1 hu1)
    (SKAlgorithm.mse_bound μ hμ hunit N hN a ha hbeta hbetaB hB hB1 hfield hu.2.2.1 hu1)

end Manuscript.SKTheorem
