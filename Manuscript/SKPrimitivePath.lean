import Manuscript.SKRestrictedMemoCell
import Manuscript.SKBasisEncoding
import SpinGlass.SKCountedExecutionCache

/-! Primitive endpoint closure from the once-computed root cache. The fixed
program computes both row addresses and reads every saved entry explicitly. -/
noncomputable section
namespace Manuscript.SKPrimitivePath
open RestrictedMachine SKBasisEncoding SKRestrictedKernels

/-- Runtime N200, root-table stride220, root250, endpoint251, color mask252,
root-cache base253, endpoint/vertex weight-table base254. -/
def setupCode : List Instruction :=
  [.nmul 0 250 220, .nadd 0 253 0, .nmul 1 252 200, .nadd 0 0 1,
   .nmul 1 251 200, .nadd 1 254 1, .nconst 2 1, .nconst 3 1,
   .ncopy 4 200, .rconst 0 0]

def program : Program := .seq (code setupCode) dotProgram

theorem path_realized {V : Type*} [DecidableEq V] {N b K : ℕ}
    (params : Parameters) (input : Inputs) (s : State)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : SpinGlass.SKCountedExecution.Root (Fin N) b →
      SpinGlass.SKCountedExecution.Table (Fin N) K)
    (a c : Fin b) (S : Finset (Fin K))
    (hN : s.natReg 200=N) (hT : s.natReg 220=2^K*N)
    (ha : s.natReg 250=a.val) (hc : s.natReg 251=c.val)
    (hS : s.natReg 252=(maskEquiv K S).val)
    (hcache : ∀ i : Fin N,
      s.realMem (s.natReg 253+a.val*(2^K*N)+(maskEquiv K S).val*N+i.val)=
        cache (Sum.inl a) S i)
    (hweight : ∀ i : Fin N, s.realMem (s.natReg 254+c.val*N+i.val)=
      SpinGlass.SKFastEvaluator.pairWeight f (outside i) (branch c)) :
    ∃ t, Exec params input program s (27*N+34) t ∧
      t.realReg 0=(SpinGlass.SKCountedExecution.cachedPath branch outside f cache a c S).value ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem ∧
      (∀ r, 4 ≤ r → t.realReg r=s.realReg r) := by
  let d := runCode params input setupCode s
  have hdN : d.natReg 4=N := by simp [d,setupCode,runCode,step,hN]
  have hdz : d.realReg 0=0 := by simp [d,setupCode,runCode,step]
  obtain ⟨t,he,hi,hv⟩ := SKRestrictedMemoCell.dot_finite params input d N
    (cache (Sum.inl a) S)
    (fun i => SpinGlass.SKFastEvaluator.pairWeight f (outside i) (branch c)) hdN hdz
    (by intro i; simpa [d,setupCode,runCode,step,hN,hT,ha,hS,Nat.add_assoc] using hcache i)
    (by intro i; simpa [d,setupCode,runCode,step,hN,hc,Nat.add_assoc] using hweight i)
  refine ⟨t,?_,?_,?_,?_,?_⟩
  · have hh : Exec params input (code setupCode) s 29 d := by
      simpa [setupCode,codeCost,instrCost,d] using exec_code params input setupCode s
    convert Exec.seq hh he using 1 <;> first | rfl | omega
  · simpa [SpinGlass.SKCountedExecution.cachedPath,SpinGlass.ArithmeticEvaluation.mul,
      SpinGlass.ArithmeticEvaluation.literal,SpinGlass.ArithmeticEvaluation.sumFinset] using hv
  · simpa [d,setupCode,runCode,step] using hi.1
  · simpa [d,setupCode,runCode,step] using hi.2.1
  · intro r hr
    have hr0 : r ≠ 0 := by omega
    simpa [d,setupCode,runCode,step,hr0] using hi.2.2.2.2.2.1 r hr

end Manuscript.SKPrimitivePath
