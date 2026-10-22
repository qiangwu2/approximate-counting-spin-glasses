import Manuscript.RestrictedSKEndpoint
import Manuscript.RuntimeOverhead

noncomputable section
namespace Manuscript.RestrictedSKRuntime
open RestrictedMachine Model

/-- A single model-dependent polynomial bounds actual primitive traces for
all raw interaction orderings, all disorder values and all color tapes. -/
theorem polynomial (a : ℕ→ℝ) (ha : a 2=1) {B rho : ℝ} (hB : 0<B) (hB1 : B<1) :
    ∃ C : ℝ,0<C ∧ ∀ N M : ℕ,2≤N →
      ∀ (beta h epsilon delta : ℝ),0<epsilon → epsilon<1 →
      ∀ (hd : 0<delta),delta<1 →
      ∀ (order : Fin M≃Edge N {2}) (χ : SKTheorem.Colors N a B rho epsilon delta)
        (J : Edge N {2}→ℝ),∃count final,
        RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table
          (RestrictedParameters.sk a B rho)
          (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
          (RestrictedSKEndpoint.program a B rho) initial count final ∧
        final.realReg 3=(SKFinal.execute N a B rho beta h epsilon delta
          (SKFinal.constant_pos a ha hB hB1) hd χ J).value ∧
        (count:ℝ)≤C*(N:ℝ)^C*epsilon^(-C)*delta^(-C) := by
  obtain ⟨K,hK,hpoly⟩:=SKFinal.polynomial a ha (rho:=rho) hB hB1
  obtain ⟨C,hC,hbound⟩:=RuntimeOverhead.preserves_polynomial 20000 K 6 (by norm_num) hK
  refine ⟨C,hC,?_⟩
  intro N M hN beta h epsilon delta he he1 hd hd1 order χ J
  obtain ⟨count,final,hex,hvalue,hcost⟩:=RestrictedSKEndpoint.program_overhead hN a ha
    hB hB1 he he1 hd hd1 order χ J
  refine ⟨count,final,hex,hvalue,?_⟩
  apply hbound N (SKFinal.execute N a B rho beta h epsilon delta
      (SKFinal.constant_pos a ha hB hB1) hd χ J).operations count epsilon delta
    (by omega) he he1.le hd hd1.le (hpoly N hN beta h epsilon delta he he1 hd hd1 χ J)
  exact_mod_cast hcost

end Manuscript.RestrictedSKRuntime
