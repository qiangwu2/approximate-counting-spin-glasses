import Manuscript.RestrictedHigherRuntime

noncomputable section
namespace Manuscript.RestrictedHigherFinal
open MeasureTheory SpinGlass.Disorder RestrictedMachine Model

/-- Primitive-machine higher-order Theorem 1.1. A fixed finite program and
fixed model parameters precede all raw inputs. Its proven output function
obeys the original-law probability estimate, and its actual instruction
trace has the common polynomial bound. No runtime or output specification
is assumed: those are the conclusions of the concrete execution theorem. -/
theorem end_to_end (P : Finset ℕ) (a : ℕ→ℝ) (hP : P.Nonempty)
    (ha : ∀ p∈P,0<a p) (pmin : ℝ) (hpmin : 3≤pmin)
    (horders : ∀ p∈P,pmin≤(p:ℝ)) (pmax : ℕ) (hmax : ∀ p∈P,p≤pmax)
    {B rho : ℝ} (hB : 0<B) (hBT : B<MixedThreshold.betaF P a) :
    ∃ C : ℝ,0<C ∧ ∀ (μ : Measure ℝ),IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ N M : ℕ,(∀ p∈P,p≤N) →
      ∀ (beta h epsilon delta : ℝ),0≤beta → beta≤B →
      |h|≤rho*(N:ℝ)^(-(1/4:ℝ)) → 0<epsilon → epsilon<1 → 0<delta → delta<1 →
      ∀ (order : Fin M≃Edge N P) (tape : ℕ→ℕ),
      ((iidLaw μ).real {J | epsilon<
        |(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value-
          Real.log (Model.partition N P a beta h J)|}≤
        delta+OriginalLawLowerTail.tau μ N P a B (MixedThreshold.theta P a B)) ∧
      ∀ J : Edge N P→ℝ,∃ count final,
        RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
          (RestrictedParameters.higher pmax P a B rho pmin)
          (RestrictedInputEncoding.encode order beta h epsilon delta J tape)
          (RestrictedHigherEndpoint.program pmax P a B rho pmin) initial count final ∧
        final.realReg 3=(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value ∧
        (count:ℝ)≤C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨C,hC,hpoly⟩ := RestrictedHigherRuntime.polynomial P a hP ha pmin hpmin horders pmax hmax
    (rho:=rho) hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N M hpN beta h epsilon delta hb hbB hfield he he1 hd hd1 order tape
  letI : IsProbabilityMeasure μ := hprob
  have hN : 0<N := by
    obtain ⟨p,hp⟩ := hP
    have hh := hpmin.trans (horders p hp)
    have h3 : 3≤p := by exact_mod_cast hh
    have := hpN p hp
    omega
  refine ⟨HigherOrderFinal.accuracy μ hμ hunit N P a hP ha pmin hpmin horders pmax hmax hpN
    hb hbB hB hBT hfield he he1 hd hd1,?_⟩
  intro J
  exact hpoly N M hN hpN beta h epsilon delta hfield he he1 hd hd1 order J tape

end Manuscript.RestrictedHigherFinal
