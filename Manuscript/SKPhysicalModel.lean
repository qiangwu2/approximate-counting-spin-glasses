import Manuscript.SKPhysicalTruncation
import Manuscript.SKColorEstimator

/-! The SK truncation bound on exactly the physical input coordinates of (2). -/

noncomputable section
open scoped BigOperators
namespace Manuscript.SKPhysicalModel
open MeasureTheory SpinGlass.Disorder Manuscript.Model
open Manuscript.DisorderOrthogonality Manuscript.UniformSKTransport

theorem physicalScale_eq (N : ℕ) (a : ℕ → ℝ) (ha : a 2 = 1) (beta : ℝ)
    (e : Edge N {2}) :
    DisorderOrthogonality.physicalScale N {2} a beta e = SKBranching.physicalScale N beta := by
  have he : e.val.card = 2 := by simpa using edge_order_mem e
  simp only [DisorderOrthogonality.physicalScale,he,ha,mul_one,
    Model.scaleDenominator,SKBranching.physicalScale,Real.sqrt_eq_rpow]
  norm_num

def truncation (N D L : ℕ) (a : ℕ → ℝ) (beta h : ℝ) (J : Edge N {2} → ℝ) : ℝ :=
  SKColorEstimator.retainedSum Subtype.val Finset.univ D L h
    (DisorderOrthogonality.physicalScale N {2} a beta) J

theorem omitted_mass_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (N D L : ℕ) (a : ℕ → ℝ) (beta h : ℝ) :
    (∑ Γ ∈ (Finset.univ : Finset (Edge N {2})).powerset.filter
      (fun Γ => ¬SKGraph.Retained Subtype.val D L Γ),
      SKColorEstimator.graphMass μ Subtype.val h
        (DisorderOrthogonality.physicalScale N {2} a beta) Γ) =
    (∫ J : Edge N {2} → ℝ,
      (Model.normalizedPartition N {2} a beta h J-truncation N D L a beta h J)^2 ∂iidLaw μ) := by
  exact (physical_retained_family_error μ hμ N {2} a beta h
    (SKGraph.Retained Subtype.val D L)).symm

theorem massConstant_eq (a : ℕ → ℝ) (ha : a 2 = 1) (v rho : ℝ) :
    UniformMixedMass.massConstant {2} (fun _ => 1) v rho =
      UniformMixedMass.massConstant {2} a v rho := by
  simp [UniformMixedMass.massConstant,MixedThreshold.thresholdSquared_sk a ha,
    MixedThreshold.thresholdSquared_sk (fun _ => 1) rfl,MixedThreshold.delta,ha]

/-- The omitted-family identity makes transport independent of unused ambient
coordinates in the untyped representation. -/
theorem mse_eq_untyped (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : SymmetricLaw μ)
    (N D L : ℕ) (a : ℕ → ℝ) (ha : a 2 = 1) (beta h : ℝ) :
    (∫ J : Edge N {2} → ℝ,
      (Model.normalizedPartition N {2} a beta h J-truncation N D L a beta h J)^2 ∂iidLaw μ) =
    (∫ J : Finset (Fin N) → ℝ,
      (FieldExpansion.normalizedPartition id ((Finset.univ : Finset (Fin N)).powersetCard 2)
        h (fun e => SKBranching.physicalScale N beta*J e)-
        SKBranching.truncation D L h (SKBranching.physicalScale N beta) J)^2 ∂iidLaw μ) := by
  rw [SKBranching.truncation_mse_eq μ hμ]
  unfold truncation SKColorEstimator.retainedSum SKColorEstimator.retained
  rw [physical_retained_family_error μ hμ]
  have ht := graphMass_transport N {2} (fun Γ => ¬SKGraph.Retained id D L Γ) h
    (fun _ => secondMoment μ (SKBranching.physicalScale N beta))
  simp only [physicalEdges_sk,SKGraph.Retained,forget_branch,forget_card] at ht
  simp_rw [physicalScale_eq N a ha beta]
  exact ht.symm

/-- Proposition 4.2 for the actual physical SK model and actual retained graph
polynomial. The disorder and field hypotheses are the manuscript's hypotheses. -/
theorem truncation_mse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ) {N D L : ℕ} (hN : 2 ≤ N)
    (a : ℕ → ℝ) (ha : a 2 = 1) {beta B Bplus h rho C alpha : ℝ}
    (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (hB : 0 < B) (hBplus : B < Bplus)
    (hplus1 : Bplus < 1)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ)))
    (hC : 0 < C) (hBC : SKBranching.branchConstant B (rho ^ 2) ≤ C) (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (C * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * N)) :
    (∫ J : Edge N {2} → ℝ,
      (Model.normalizedPartition N {2} a beta h J-truncation N D L a beta h J)^2 ∂iidLaw μ) ≤
      UniformMixedMass.massConstant {2} (fun _ => 1) (Bplus ^ 2) rho *
        ((B / Bplus) ^ 2) ^ (L + 1) +
      2 * SKBranching.massConstant B (rho ^ 2) * Real.exp (-SpinGlass.CutoffTail.phi 1 C N (D + 1)) +
      UniformMixedMass.massConstant {2} (fun _ => 1) (Bplus ^ 2) rho *
        ((B / Bplus) ^ 2) ^ (3 * alpha * N / 2) := by
  rw [mse_eq_untyped μ hμ N D L a ha beta h]
  exact SKBranching.physical_truncation_mse μ hμ hunit hN hbeta hbetaB hB hBplus hplus1
    hfield hC hBC halpha hgap hcut

end Manuscript.SKPhysicalModel
