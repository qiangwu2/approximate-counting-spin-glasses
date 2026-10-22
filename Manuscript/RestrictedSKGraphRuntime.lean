import Manuscript.RestrictedSKGraphEndpoint
import Manuscript.RuntimeOverhead

noncomputable section
namespace Manuscript.RestrictedSKGraphRuntime
open RestrictedMachine Model

/-- Uniform primitive operation bound for the direct requested MSE budget. -/
theorem polynomial (a : ℕ→ℝ) (ha : a 2=1) {B rho : ℝ} (hB : 0<B) (hB1 : B<1) :
    ∃ C : ℝ,0<C ∧ ∀ N M : ℕ,2≤N → ∀ (beta h u : ℝ),0<u → u<1 →
      ∀ (order : Fin M≃Edge N {2}) (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2}→ℝ),
      ∃count final,RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
        (RestrictedParameters.sk a B rho)
        (RestrictedInputEncoding.encode order beta h u 1 J (SKRawColorTape.encode χ))
        (RestrictedSKGraphEndpoint.program a B rho) initial count final ∧
      final.realReg 572=SKAlgorithm.run N a B rho beta h u χ J ∧
      (count:ℝ)≤C*(N:ℝ)^C*u^(-C) := by
  obtain ⟨K,hK,hpoly⟩:=SKExecutionCost.execute_polynomial a ha (rho:=rho) hB hB1
  obtain ⟨C,hC,hbound⟩:=RuntimeOverhead.preserves_polynomial 20000 K 6 (by norm_num) hK
  refine ⟨C,hC,?_⟩
  intro N M hN beta h u hu hu1 order χ J
  obtain ⟨count,final,hex,hvalue,hcost⟩:=RestrictedSKGraphEndpoint.program_overhead hN a ha hB hB1 hu hu1 order χ J
  refine ⟨count,final,hex,hvalue.trans (SKPhysicalExecution.execute_value (by omega) a ha hB hB1 hu hu1 χ J),?_⟩
  have hh:=hbound N (SKPhysicalExecution.execute N a B rho beta h u χ J).operations count u 1
    (by omega) hu hu1.le (by norm_num) (by norm_num)
    (by simpa using hpoly N hN beta h u hu hu1 χ J) (by exact_mod_cast hcost)
  simpa using hh

end Manuscript.RestrictedSKGraphRuntime
