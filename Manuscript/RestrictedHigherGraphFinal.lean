import Manuscript.RestrictedHigherGraphRuntime

noncomputable section
namespace Manuscript.RestrictedHigherGraphFinal
open MeasureTheory SpinGlass.Disorder RestrictedMachine Model

/-- The higher-order case of Proposition 5.2, for the full requested range
`0 < u < 1`. The fixed primitive program reads raw couplings and raw `u`, and
its actual output has the original-law mean-square bound. Its real primitive
instruction count has one uniform polynomial bound. -/
theorem end_to_end (P : Finset ℕ) (a : ℕ→ℝ) (hP : P.Nonempty)
    (ha : ∀ p∈P,0<a p) (pmin : ℝ) (hpmin : 3≤pmin)
    (horders : ∀ p∈P,pmin≤(p:ℝ)) (pmax : ℕ) (hmax : ∀ p∈P,p≤pmax)
    {B rho : ℝ} (hB : 0<B) (hBT : B<MixedThreshold.betaF P a) :
    ∃ C : ℝ,0<C ∧ ∀ (μ : Measure ℝ),IsProbabilityMeasure μ →
      SymmetricLaw μ → UnitSecondMoment μ → ∀ N M : ℕ,(∀ p∈P,p≤N) →
      ∀ (beta h u : ℝ),0≤beta → beta≤B →
      |h|≤rho*(N:ℝ)^(-(1/4:ℝ)) → 0<u → u<1 →
      ∀ (order : Fin M≃Edge N P) (tape : ℕ→ℕ),
      ((∫ J, (Model.normalizedPartition N P a beta h J-
        (HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).value)^2
        ∂iidLaw μ)≤u) ∧
      ∀ J : Edge N P→ℝ,∃ count final,
        RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
          (RestrictedParameters.higher pmax P a B rho pmin)
          (RestrictedInputEncoding.encode order beta h u 1 J tape)
          (RestrictedHigherGraphEndpoint.program pmax P a B rho pmin) initial count final ∧
        final.realReg 330=(HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).value ∧
        (count:ℝ)≤C*(N:ℝ)^C*u^(-C) := by
  obtain ⟨C,hC,hpoly⟩ := RestrictedHigherGraphRuntime.polynomial P a hP ha pmin hpmin horders pmax hmax
    (rho:=rho) hB hBT
  refine ⟨C,hC,?_⟩
  intro μ hprob hμ hunit N M hpN beta h u hb hbB hfield hu hu1 order tape
  letI : IsProbabilityMeasure μ := hprob
  have hN : 0<N := by
    obtain ⟨p,hp⟩ := hP
    have hh := hpmin.trans (horders p hp)
    have h3 : 3≤p := by exact_mod_cast hh
    have := hpN p hp
    omega
  refine ⟨?_,?_⟩
  · simp_rw [HigherOrderExecution.execute_value hN pmax P a B rho pmin beta h u (by linarith)]
    exact HigherOrderAlgorithm.mse_bound μ hμ hunit N P a hP ha pmin hpmin horders pmax hmax hpN
      hb hbB hB hBT hfield hu hu1
  · intro J
    exact hpoly N M hN hpN beta h u hfield hu hu1 order J tape

end Manuscript.RestrictedHigherGraphFinal
