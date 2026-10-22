import Manuscript.RestrictedSKGraphRuntime

noncomputable section
namespace Manuscript.RestrictedSKGraphFinal
open MeasureTheory SpinGlass.Disorder RestrictedMachine Model

/-- The SK case of current Proposition5.2 with direct raw input u∈(0,1).
The actual fixed primitive program realizes the mean-square estimator on the
original disorder/color product law and satisfies one uniform polynomial
operation bound on every input and every random outcome. -/
theorem end_to_end (a : ℕ→ℝ) (ha : a 2=1) {B rho : ℝ} (hB : 0<B) (hB1 : B<1) :
    ∃ C : ℝ,0<C ∧ ∀ (μ : Measure ℝ),IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ N M : ℕ,2≤N →
      ∀ (beta h u : ℝ),0≤beta → beta≤B → |h|≤rho*(N:ℝ)^(-(1/4:ℝ)) →
      0<u → u<1 → ∀ (order : Fin M≃Edge N {2}),
      ((∫χJ : SKAlgorithm.Colors N a B rho u × (Edge N {2}→ℝ),
        (SKAlgorithm.run N a B rho beta h u χJ.1 χJ.2-Model.normalizedPartition N {2} a beta h χJ.2)^2
        ∂(SKAlgorithm.colorLaw N a B rho u).prod (iidLaw μ))≤u) ∧
      ∀ (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2}→ℝ),∃count final,
        RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
          (RestrictedParameters.sk a B rho)
          (RestrictedInputEncoding.encode order beta h u 1 J (SKRawColorTape.encode χ))
          (RestrictedSKGraphEndpoint.program a B rho) initial count final ∧
        final.realReg 572=SKAlgorithm.run N a B rho beta h u χ J ∧
        (count:ℝ)≤C*(N:ℝ)^C*u^(-C) := by
  obtain ⟨C,hC,hpoly⟩:=RestrictedSKGraphRuntime.polynomial a ha (rho:=rho) hB hB1
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N M hN beta h u hb hbB hfield hu hu1 order
  letI : IsProbabilityMeasure μ:=hprob
  refine ⟨SKAlgorithm.mse_bound μ hμ hunit N hN a ha hb hbB hB hB1 hfield hu hu1,?_⟩
  intro χ J
  exact hpoly N M hN beta h u hu hu1 order χ J

end Manuscript.RestrictedSKGraphFinal
