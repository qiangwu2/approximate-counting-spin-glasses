import Manuscript.RestrictedHigherEndpoint
import Manuscript.RestrictedSupportLowerBound
import Manuscript.RuntimeOverhead

set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedHigherRuntime
open RestrictedMachine RestrictedHigherEndpoint InputPreparation Model

/-- The previously established arithmetic count is used only as a numerical
majorant, after the primitive execution has independently been derived. -/
theorem old_lower (N pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ)
    (B rho pmin beta h epsilon delta : ℝ) (J : Edge N P→ℝ) :
    Fintype.card (Edge N P)≤(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).operations ∧
    (∑l∈Finset.range (cutoff N pmax P a B rho pmin h epsilon delta+1),N.choose l*2^l)≤
      ((HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).operations+1)^2 := by
  let inp := prepareInput N P a beta h J
  let budgets := prepareBudget (LogApprox.constant P a B rho) delta epsilon (LogApprox.exponent P a B)
  let ctl := HigherOrderExecution.control N pmax P a B rho pmin h budgets.u inp.field.mean
  let result := SupportExecution.supportSum Subtype.val Finset.univ (cachedFieldWeight inp) (cachedWeight inp) ctl.cutoff
  have hk : ctl.cutoff=cutoff N pmax P a B rho pmin h epsilon delta := rfl
  have part : inp.operations+result.operations≤
      (HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).operations := by
    change inp.operations+result.operations≤
      budgets.operations+(LogApprox.finish inp ⟨result.value,ctl.operations+result.operations⟩).operations
    dsimp only [LogApprox.finish]
    omega
  have prepCost := prepareInput_operations N P a beta h J
  have prepCost' : inp.operations=InputIndices.generationWork N P+23*Fintype.card (Edge N P)+15 := prepCost
  refine ⟨by omega,?_⟩
  have hh := RestrictedSupportLowerBound.weighted_le_operations_square
    (Subtype.val : Edge N P→Finset (Fin N)) Finset.univ (cachedFieldWeight inp) (cachedWeight inp)
    (k:=ctl.cutoff) (by simpa only [Fintype.card_fin,hk] using cutoff_le N pmax P a B rho pmin h epsilon delta)
  simp only [Fintype.card_fin,hk] at hh
  apply hh.trans
  apply Nat.pow_le_pow_left
  change result.operations+1≤(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).operations+1
  omega

theorem numeric_overhead (N M old W steps : ℕ) (hM : M≤old) (hW : W≤(old+1)^2)
    (hsteps : steps≤141*M+78*N+461+(59*N+26+(66*N+56)*M+300*(N+1)+400)*W) :
    steps≤3000*(N+old+1)^4 := by
  let R := N+old+1
  have hR : 1≤R := by dsimp [R]; omega
  have hN : N≤R := by dsimp [R]; omega
  have hMr : M≤R := by dsimp [R]; omega
  have hOr : old+1≤R := by dsimp [R]; omega
  have hR2 : R≤R^2 := by nlinarith
  have hW2 : W≤R^2 := hW.trans (Nat.pow_le_pow_left hOr 2)
  have hNM : N*M≤R^2 := by simpa [pow_two] using Nat.mul_le_mul hN hMr
  have hNr2 : N≤R^2 := hN.trans hR2
  have hMr2 : M≤R^2 := hMr.trans hR2
  have h1r2 : 1≤R^2 := hR.trans hR2
  have hf : 59*N+26+(66*N+56)*M+300*(N+1)+400≤2000*R^2 := by nlinarith
  have hl : 141*M+78*N+461≤1000*R^2 := by nlinarith
  have hm := Nat.mul_le_mul hf hW2
  have hR4 : R^2≤R^4 := by nlinarith [sq_nonneg (R^2-1 : ℤ)]
  change steps≤3000*R^4
  nlinarith

theorem program_overhead {N M : ℕ} (hN : 0<N) (pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ)
    (hmax : ∀ p∈P,p≤pmax) (B rho pmin beta h epsilon delta : ℝ)
    (order : Fin M≃Edge N P) (J : Edge N P→ℝ) (tape : ℕ→ℕ) :
    ∃ count final,
      RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
        (RestrictedParameters.higher pmax P a B rho pmin)
        (RestrictedInputEncoding.encode order beta h epsilon delta J tape)
        (program pmax P a B rho pmin) initial count final ∧
      final.realReg 3=(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value ∧
      count≤3000*(N+(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).operations+1)^4 := by
  obtain ⟨c,t,he,hv,hc⟩ := program_exec hN pmax P a hmax B rho pmin beta h epsilon delta order J tape
  obtain ⟨hM,hW⟩ := old_lower N pmax P a B rho pmin beta h epsilon delta J
  have hm : M=Fintype.card (Edge N P) := by simpa using Fintype.card_congr order
  rw [←hm] at hM
  exact ⟨c,t,he,hv,numeric_overhead N M _ _ c hM hW hc⟩

/-- One constant bounds actual primitive instructions uniformly in all raw
records, all disorder values, and all requested accuracies. -/
theorem polynomial (P : Finset ℕ) (a : ℕ→ℝ) (hP : P.Nonempty)
    (ha : ∀ p∈P,0<a p) (pmin : ℝ) (hpmin : 3≤pmin)
    (horders : ∀ p∈P,pmin≤(p:ℝ)) (pmax : ℕ) (hmax : ∀ p∈P,p≤pmax)
    {B rho : ℝ} (hB : 0<B) (hBT : B<MixedThreshold.betaF P a) :
    ∃ C : ℝ,0<C ∧ ∀ N M : ℕ,0<N → (∀ p∈P,p≤N) →
      ∀ (beta h epsilon delta : ℝ), |h|≤rho*(N:ℝ)^(-(1/4:ℝ)) →
      0<epsilon → epsilon<1 → 0<delta → delta<1 →
      ∀ (order : Fin M≃Edge N P) (J : Edge N P→ℝ) (tape : ℕ→ℕ),
      ∃ count final,
        RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
          (RestrictedParameters.higher pmax P a B rho pmin)
          (RestrictedInputEncoding.encode order beta h epsilon delta J tape)
          (program pmax P a B rho pmin) initial count final ∧
        final.realReg 3=(HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).value ∧
        (count:ℝ)≤C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨K,hK,hpoly⟩ := HigherOrderFinal.polynomial P a hP ha pmin hpmin horders pmax hmax (rho:=rho) hB hBT
  obtain ⟨C,hC,hbound⟩ := RuntimeOverhead.preserves_polynomial 3000 K 4 (by norm_num) hK
  refine ⟨C,hC,?_⟩
  intro N M hN hpN beta h epsilon delta hfield he he1 hd hd1 order J tape
  obtain ⟨c,t,hex,hval,hcost⟩ := program_overhead hN pmax P a hmax B rho pmin beta h epsilon delta order J tape
  refine ⟨c,t,hex,hval,?_⟩
  apply hbound N (HigherOrderFinal.execute N pmax P a B rho pmin beta h epsilon delta J).operations c epsilon delta
    (by omega) he he1.le hd hd1.le (hpoly N hN hpN beta h epsilon delta hfield he he1 hd hd1 J)
  exact_mod_cast hcost

end Manuscript.RestrictedHigherRuntime
