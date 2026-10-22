import Manuscript.SKPrimitiveNormalize

/-! Return-path closure executes the saved-cache dot product and its factor
one half; the minimum-two-colors test is computed from the runtime mask. -/
noncomputable section
namespace Manuscript.SKPrimitiveReturn
open RestrictedMachine SKBasisEncoding

def program : Program := .seq SKPrimitivePath.program (SKPrimitiveNormalize.program 2 false)

theorem return_realized {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : SpinGlass.SKCountedExecution.Root (Fin N) b →
      SpinGlass.SKCountedExecution.Table (Fin N) K)
    (a : Fin b) (S : Finset (Fin K))
    (hN : s.natReg 200=N) (hK : s.natReg 201=K) (hT : s.natReg 220=2^K*N)
    (ha : s.natReg 250=a.val) (hc : s.natReg 251=a.val)
    (hS : s.natReg 252=(maskEquiv K S).val)
    (hcache : ∀ j : Fin N,
      s.realMem (s.natReg 253+a.val*(2^K*N)+(maskEquiv K S).val*N+j.val)=
        cache (Sum.inl a) S j)
    (hweight : ∀ j : Fin N, s.realMem (s.natReg 254+a.val*N+j.val)=
      SpinGlass.SKFastEvaluator.pairWeight f (outside j) (branch a)) :
    ∃ c t, Exec p i program s c t ∧ c≤27*N+29*K+67 ∧
      t.realReg 0=(SpinGlass.SKCountedExecution.cachedReturn branch outside f cache a S).value ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  obtain ⟨d,he,hv,hm,hn,_⟩ := SKPrimitivePath.path_realized p i s branch outside f cache a a S
    hN hT ha hc hS hcache hweight
  have hf (r : ℕ) (hr : 4<r) : d.natReg r=s.natReg r := by
    apply he.natReg_frame
    simp [SKPrimitivePath.program,SKPrimitivePath.setupCode,SKRestrictedKernels.dotProgram,
      SKRestrictedKernels.dotBody,code,Program.All,Instruction.natDestination]
    omega
  obtain ⟨c,t,het,bc,hval,htm,htn⟩ := SKPrimitiveNormalize.normalize_realized p i d S 2 false
    ((hf 201 (by omega)).trans hK) ((hf 252 (by omega)).trans hS)
  refine ⟨27*N+34+c,t,Exec.seq he het,by omega,?_,htm.trans hm,htn.trans hn⟩
  rw [hval,hv]
  by_cases hS2 : 2≤S.card <;>
    simp [SpinGlass.SKCountedExecution.cachedReturn,hS2,SpinGlass.ArithmeticEvaluation.mul,
      SpinGlass.ArithmeticEvaluation.literal,div_eq_mul_inv,mul_comm]
end Manuscript.SKPrimitiveReturn
