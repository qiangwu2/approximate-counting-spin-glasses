import Manuscript.SKRestrictedGrid
import Manuscript.SKPrimitiveNormalize

/-! The outside-cycle primitive is computed by one runtime root/endpoint
grid traversal of the saved cache, followed by computed cardinality correction. -/
noncomputable section
namespace Manuscript.SKPrimitiveCycle
open RestrictedMachine SKBasisEncoding SKRestrictedGrid
open scoped BigOperators

def setupCode : List Instruction :=
  [.nmul 0 256 220, .nadd 0 253 0, .nmul 1 252 200, .nadd 0 0 1,
   .ncopy 1 254, .nconst 2 1, .nconst 3 1, .ncopy 4 200, .ncopy 5 200,
   .nsub 6 220 200, .nconst 7 0, .rconst 0 0]
def sumProgram : Program := .seq (code setupCode) SKRestrictedGrid.program
def program : Program := .seq sumProgram (SKPrimitiveNormalize.program 3 true)

theorem sum_realized {V : Type*} [DecidableEq V] {N b K : ℕ}
    (params : Parameters) (input : Inputs) (s : State)
    (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : SpinGlass.SKCountedExecution.Root (Fin N) b →
      SpinGlass.SKCountedExecution.Table (Fin N) K) (S : Finset (Fin K))
    (hN : s.natReg 200=N) (hT : s.natReg 220=2^K*N)
    (hb : s.natReg 256=b) (hS : s.natReg 252=(maskEquiv K S).val)
    (hcache : ∀ r j : Fin N,
      s.realMem (s.natReg 253+(b+r.val)*(2^K*N)+(maskEquiv K S).val*N+j.val)=
        cache (Sum.inr r) S j)
    (hweight : ∀ r j : Fin N, s.realMem (s.natReg 254+r.val*N+j.val)=
      SpinGlass.SKFastEvaluator.pairWeight f (outside r) (outside j)) :
    ∃ t, Exec params input sumProgram s (N*(27*N+18)+35) t ∧
      t.realReg 0=∑ r : Fin N, ∑ j : Fin N,
        cache (Sum.inr r) S j*SpinGlass.SKFastEvaluator.pairWeight f (outside j) (outside r) ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem ∧
      (∀ r, 8≤r → t.natReg r=s.natReg r) := by
  let d := runCode params input setupCode s
  obtain ⟨t,he,hi⟩ := grid_realized params input d
  have hlen : d.natReg 4=N ∧ d.natReg 5=N := by simp [d,setupCode,runCode,step,hN]
  have hgap : N+(2^K*N-N)=2^K*N := by
    have hpow : 1≤2^K := Nat.one_le_pow K 2 (by decide)
    have hbound : N≤2^K*N := by nlinarith
    omega
  refine ⟨t,?_,?_,?_,?_,?_⟩
  · have hinit : Exec params input (code setupCode) s 30 d := by
      simpa [d,setupCode,codeCost,instrCost] using exec_code params input setupCode s
    rw [hlen.1,hlen.2] at he
    convert Exec.seq hinit he using 1 <;> first | rfl | omega
  · have hv := hi.2.2.2.2.2.2
    simp only [d,setupCode,runCode,step,writeNatReg_natReg,writeNatReg_realReg,
      writeNatReg_realMem,writeRealReg_natReg,writeRealReg_realReg,writeRealReg_realMem] at hv
    norm_num at hv
    simp only [hN,hT,hb,hS,Nat.mul_one,Nat.add_zero,hgap] at hv
    rw [← Fin.sum_univ_eq_sum_range] at hv
    simp_rw [← Fin.sum_univ_eq_sum_range] at hv
    rw [hv]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro j _
    have hleft : s.natReg 253+b*(2^K*N)+(maskEquiv K S).val*N+r.val*(2^K*N)+j.val=
        s.natReg 253+(b+r.val)*(2^K*N)+(maskEquiv K S).val*N+j.val := by ring
    rw [hleft,hcache,hweight]
    simp [SpinGlass.SKFastEvaluator.pairWeight,Finset.pair_comm]
  · simpa [d,setupCode,runCode,step] using hi.1
  · simpa [d,setupCode,runCode,step] using hi.2.1
  · intro r hr
    have hframe := hi.2.2.2.2.1 r (by omega)
    have hn : r≠0 ∧ r≠1 ∧ r≠2 ∧ r≠3 ∧ r≠4 ∧ r≠5 ∧ r≠6 ∧ r≠7 := by omega
    simpa [d,setupCode,runCode,step,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,
      hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2] using hframe

theorem cycle_realized {V : Type*} [DecidableEq V] {N b K : ℕ}
    (params : Parameters) (input : Inputs) (s : State)
    (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : SpinGlass.SKCountedExecution.Root (Fin N) b →
      SpinGlass.SKCountedExecution.Table (Fin N) K) (S : Finset (Fin K))
    (hN : s.natReg 200=N) (hK : s.natReg 201=K) (hT : s.natReg 220=2^K*N)
    (hb : s.natReg 256=b) (hS : s.natReg 252=(maskEquiv K S).val)
    (hcache : ∀ r j : Fin N,
      s.realMem (s.natReg 253+(b+r.val)*(2^K*N)+(maskEquiv K S).val*N+j.val)=
        cache (Sum.inr r) S j)
    (hweight : ∀ r j : Fin N, s.realMem (s.natReg 254+r.val*N+j.val)=
      SpinGlass.SKFastEvaluator.pairWeight f (outside r) (outside j)) :
    ∃ count t, Exec params input program s count t ∧ count≤N*(27*N+18)+29*K+68 ∧
      t.realReg 0=(SpinGlass.SKCountedExecution.cachedCycle outside f cache S).value ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  obtain ⟨m,he,hvalue,hm,hn,hf⟩ := sum_realized params input s outside f cache S hN hT hb hS hcache hweight
  obtain ⟨cn,t,het,hcn,hv,htm,htn⟩ := SKPrimitiveNormalize.normalize_realized params input m S 3 true
    (by rw [hf 201 (by omega)]; exact hK) (by rw [hf 252 (by omega)]; exact hS)
  refine ⟨N*(27*N+18)+35+cn,t,Exec.seq he het,by omega,?_,htm.trans hm,htn.trans hn⟩
  rw [hv,hvalue]
  simp only [SpinGlass.SKCountedExecution.cachedCycle]
  split_ifs <;>
    simp [SpinGlass.ArithmeticEvaluation.mul,SpinGlass.ArithmeticEvaluation.literal,
      SpinGlass.ArithmeticEvaluation.sumFinset,Fintype.sum_prod_type,div_eq_mul_inv,mul_comm]

end Manuscript.SKPrimitiveCycle
