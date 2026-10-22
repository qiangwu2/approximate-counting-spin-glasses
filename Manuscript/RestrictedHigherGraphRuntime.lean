import Manuscript.RestrictedHigherGraphEndpoint
import Manuscript.RestrictedHigherRuntime
import Manuscript.RestrictedSupportLowerBound
import Manuscript.RuntimeOverhead

set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedHigherGraphRuntime
open RestrictedMachine RestrictedHigherGraphEndpoint InputPreparation Model

/-- The previously established arithmetic count is used only as a numerical
majorant, after the primitive execution has independently been derived. -/
theorem old_lower (N pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ)
    (B rho pmin beta h u : ℝ) (J : Edge N P→ℝ) :
    Fintype.card (Edge N P)≤(HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).operations ∧
    (∑l∈Finset.range (cutoff N pmax P a B rho pmin h u+1),N.choose l*2^l)≤
      ((HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).operations+1)^2 := by
  let inp := prepareInput N P a beta h J
  let ctl := HigherOrderExecution.control N pmax P a B rho pmin h u inp.field.mean
  let result := SupportExecution.supportSum Subtype.val Finset.univ (cachedFieldWeight inp) (cachedWeight inp) ctl.cutoff
  have hk : ctl.cutoff=cutoff N pmax P a B rho pmin h u := rfl
  have part : inp.operations+result.operations≤
      (HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).operations := by
    change inp.operations + result.operations ≤ inp.operations + ctl.operations + result.operations
    omega
  have prepCost := prepareInput_operations N P a beta h J
  have prepCost' : inp.operations=InputIndices.generationWork N P+23*Fintype.card (Edge N P)+15 := prepCost
  refine ⟨by omega,?_⟩
  have hh := RestrictedSupportLowerBound.weighted_le_operations_square
    (Subtype.val : Edge N P→Finset (Fin N)) Finset.univ (cachedFieldWeight inp) (cachedWeight inp)
    (k:=ctl.cutoff) (by simpa only [Fintype.card_fin,hk] using cutoff_le N pmax P a B rho pmin h u)
  simp only [Fintype.card_fin,hk] at hh
  apply hh.trans
  apply Nat.pow_le_pow_left
  change result.operations+1≤(HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).operations+1
  omega

theorem program_overhead {N M : ℕ} (hN : 0<N) (pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ)
    (hmax : ∀ p∈P,p≤pmax) (B rho pmin beta h u : ℝ)
    (order : Fin M≃Edge N P) (J : Edge N P→ℝ) (tape : ℕ→ℕ) :
    ∃ count final,
      RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
        (RestrictedParameters.higher pmax P a B rho pmin)
        (RestrictedInputEncoding.encode order beta h u 1 J tape)
        (program pmax P a B rho pmin) initial count final ∧
      final.realReg 330=(HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).value ∧
      count≤3000*(N+(HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).operations+1)^4 := by
  obtain ⟨c,t,he,hv,hc⟩ := program_exec hN pmax P a hmax B rho pmin beta h u order J tape
  obtain ⟨hM,hW⟩ := old_lower N pmax P a B rho pmin beta h u J
  have hm : M=Fintype.card (Edge N P) := by simpa using Fintype.card_congr order
  rw [←hm] at hM
  exact ⟨c,t,he,hv,RestrictedHigherRuntime.numeric_overhead N M _ _ c hM hW hc⟩

/-- One constant bounds actual primitive instructions uniformly in all raw
records, all disorder values, and all requested accuracies. -/
theorem polynomial (P : Finset ℕ) (a : ℕ→ℝ) (hP : P.Nonempty)
    (ha : ∀ p∈P,0<a p) (pmin : ℝ) (hpmin : 3≤pmin)
    (horders : ∀ p∈P,pmin≤(p:ℝ)) (pmax : ℕ) (hmax : ∀ p∈P,p≤pmax)
    {B rho : ℝ} (hB : 0<B) (hBT : B<MixedThreshold.betaF P a) :
    ∃ C : ℝ,0<C ∧ ∀ N M : ℕ,0<N → (∀ p∈P,p≤N) →
      ∀ (beta h u : ℝ), |h|≤rho*(N:ℝ)^(-(1/4:ℝ)) →
      0<u → u<1 →
      ∀ (order : Fin M≃Edge N P) (J : Edge N P→ℝ) (tape : ℕ→ℕ),
      ∃ count final,
        RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
          (RestrictedParameters.higher pmax P a B rho pmin)
          (RestrictedInputEncoding.encode order beta h u 1 J tape)
          (program pmax P a B rho pmin) initial count final ∧
        final.realReg 330=(HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).value ∧
        (count:ℝ)≤C*(N:ℝ)^C*u^(-C) := by
  obtain ⟨K,hK,hpoly⟩ := HigherOrderExecution.execute_polynomial P a hP ha pmin hpmin horders pmax hmax (rho:=rho) hB hBT
  obtain ⟨C,hC,hbound⟩ := RuntimeOverhead.preserves_polynomial 3000 K 4 (by norm_num) hK
  refine ⟨C,hC,?_⟩
  intro N M hN hpN beta h u hfield hu hu1 order J tape
  obtain ⟨c,t,hex,hval,hcost⟩ := program_overhead hN pmax P a hmax B rho pmin beta h u order J tape
  refine ⟨c,t,hex,hval,?_⟩
  have hold := hpoly N hN hpN beta h u hfield hu hu1 J
  have hm := hbound N (HigherOrderExecution.execute N pmax P a B rho pmin beta h u J).operations c u 1
    (by omega) hu hu1.le (by norm_num) (by norm_num)
    (by simpa only [Real.one_rpow,mul_one] using hold) (by exact_mod_cast hcost)
  simpa only [Real.one_rpow,mul_one] using hm

end Manuscript.RestrictedHigherGraphRuntime
