import Manuscript.RestrictedSKOuterBridge
import Manuscript.SKCandidateContract

/-! The full truncated SK estimator is a fixed restricted stack-RAM program.
All candidate correctness and cost premises of the modular loop theorem are
discharged here by the physical raw-input candidate implementation. -/
noncomputable section
namespace Manuscript.RestrictedSKTruncated
open RestrictedMachine SpinGlass

def program : RestrictedRecursiveMachine.Program 2 :=
  RestrictedSKOuterBridge.program SKRawCandidate.program

theorem program_exec {N M D L R : ℕ} (hL : 0<L) (params : Parameters)
    (order : Fin M≃Model.Edge N {2}) (a : ℕ→ℝ) (beta h epsilon delta : ℝ)
    (J : Model.Edge N {2}→ℝ) (χ : SKColorEstimator.Colors (Fin N) L R)
    (s : State) (hs : SKCandidateContract.Core order a beta h J D L R s)
    (hbase : s.natReg 501≤s.natReg 576) :
    ∃count t,RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table params
        (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
        program s count t ∧
      t.realReg 572=(SKGeneratedExecution.estimator D L R χ (Real.tanh h)
        (SKGhostCoefficient.inputWeight N a beta J)).value ∧
      count≤RestrictedSKOuter.cost
        (SKCandidateContract.bound χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J))
        N R (D+1) 0+12 ∧
      SKCandidateContract.Core order a beta h J D L R t ∧
      (∀r,580<r ∨ r=500 ∨ r=501 ∨ r=510 ∨ r=512 ∨ r=513 ∨ r=570 ∨ r=576 → t.natReg r=s.natReg r) ∧
      (∀r,573≤r → t.realReg r=s.realReg r) ∧
      (∀j,j<s.natReg 576 → t.natMem j=s.natMem j) := by
  obtain ⟨c,t,he,hp,hc,hv,hn,hr,hm⟩ := RestrictedSKOuter.program_exec params
    (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
    SKRawCandidate.program (SKCandidateContract.Core order a beta h J D L R)
    (SKCandidateContract.core_stable order a beta h J D L R)
    (SKCandidateContract.value χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J))
    (SKCandidateContract.bound χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J))
    (SKCandidateContract.realized hL params order a beta h epsilon delta J χ) s hs hbase
  refine ⟨c,t,RestrictedSKOuterBridge.embed he,?_,?_,hp,hn,hr,hm⟩
  · rw [hv,hs.physical.size,hs.repeats,hs.cutoff]
    apply RestrictedSKOuterBridge.value_eq_estimator
    intro A r
    simp [SKCandidateContract.value,SKCandidateContract.decodeMask_encode,r.isLt]
  · simpa [hs.physical.size,hs.repeats,hs.cutoff] using hc

end Manuscript.RestrictedSKTruncated
