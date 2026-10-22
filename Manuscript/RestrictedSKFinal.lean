import Manuscript.RestrictedSKRuntime

noncomputable section
namespace Manuscript.RestrictedSKFinal
open MeasureTheory SpinGlass.Disorder RestrictedMachine Model

/-- Primitive-machine SK Theorem1.1. The program and the two finite procedure
bodies are fixed before every raw input. The original-law probability bound
applies to its proven output function; the actual restricted-instruction
trace has a uniform polynomial bound. No output or runtime contract is assumed. -/
theorem end_to_end (a : ℕ→ℝ) (ha : a 2=1) {B rho : ℝ} (hB : 0<B) (hB1 : B<1) :
    ∃ C : ℝ,0<C ∧ ∀ (μ : Measure ℝ),IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ N M : ℕ,2≤N →
      ∀ (beta h epsilon delta : ℝ),0≤beta → beta≤B →
      |h|≤rho*(N:ℝ)^(-(1/4:ℝ)) → 0<epsilon → epsilon<1 →
      ∀ (hd : 0<delta),delta<1 → ∀ (order : Fin M≃Edge N {2}),
      (((SKTheorem.colorLaw N a B rho epsilon delta).prod (iidLaw μ)).real
        {χJ : SKTheorem.Colors N a B rho epsilon delta × (Edge N {2}→ℝ) | epsilon<
          |(SKFinal.execute N a B rho beta h epsilon delta (SKFinal.constant_pos a ha hB hB1) hd χJ.1 χJ.2).value-
            Real.log (Model.partition N {2} a beta h χJ.2)|}≤
        delta+OriginalLawLowerTail.tau μ N {2} a B (MixedThreshold.theta {2} a B)) ∧
      ∀ (χ : SKTheorem.Colors N a B rho epsilon delta) (J : Edge N {2}→ℝ),∃count final,
        RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
          (RestrictedParameters.sk a B rho)
          (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
          (RestrictedSKEndpoint.program a B rho) initial count final ∧
        final.realReg 3=(SKFinal.execute N a B rho beta h epsilon delta
          (SKFinal.constant_pos a ha hB hB1) hd χ J).value ∧
        (count:ℝ)≤C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨C,hC,hpoly⟩:=RestrictedSKRuntime.polynomial a ha (rho:=rho) hB hB1
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N M hN beta h epsilon delta hb hbB hfield he he1 hd hd1 order
  letI : IsProbabilityMeasure μ:=hprob
  refine ⟨SKFinal.accuracy μ hμ hunit N hN a ha hb hbB hB hB1 hfield he he1 hd hd1,?_⟩
  intro χ J
  exact hpoly N M hN beta h epsilon delta he he1 hd hd1 order χ J

end Manuscript.RestrictedSKFinal
