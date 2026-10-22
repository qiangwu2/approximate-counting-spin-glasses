import Manuscript.SKRawCandidate
import Manuscript.SKCandidateSourceFacts
import Manuscript.SKCandidateCost

/-! The actual raw-candidate trace is a fixed polynomial overhead over the
preexisting generated-trial cost, with its lower bound proved from actual
charged trial operations. -/
noncomputable section
namespace Manuscript.SKRawCandidateCost
open RestrictedMachine SpinGlass

theorem operationBound_le {N M : ℕ} (order : Fin M≃Model.Edge N {2})
    (s : State) (hM : s.natReg 501=M) (A : Finset (Fin N))
    (χ : Fin N→Fin (2*s.natReg 512)) (mean : ℝ) (w : Finset (Fin N)→ℝ) :
    SKRawCandidate.operationBound s A≤
      7000*(N+(SKGeneratedExecution.trial (s.natReg 512) A χ mean w).operations+1)^5 := by
  let work := (SKGeneratedExecution.trial (s.natReg 512) A χ mean w).operations
  let Q := N+work+1
  let d := SKCandidateSource.layout s A
  have hQ : 1≤Q := by dsimp [Q];omega
  have hdim : SKOperationCount.registers (A.card+1) (2*s.natReg 512)≤work :=
    SKExecutionLowerBound.generated_registers _ A χ mean w
  have hsize := SKExecutionLowerBound.size_le_registers (A.card+1) (2*s.natReg 512)
  have hB : d.root.B=A.card+1 := by simp [d,SKCandidateSource.layout]
  have hK : d.root.K=2*s.natReg 512 := rfl
  have hN : d.root.N≤N := by simp [d,SKCandidateSource.layout]
  have hdim' : d.M=SKOperationCount.registers (A.card+1) (2*s.natReg 512) := by
    simp [SKCandidateLayout.Layout.M,hB,hK,SKOperationCount.registers]
  have hfull : SKRestrictedCandidateExecution.operationBound d≤6000*Q^5 :=
    SKCandidateCost.full_bound d Q hQ (by dsimp [Q];omega)
      (by rw [hB];dsimp [Q];omega) (by rw [hK];dsimp [Q];omega)
      (by rw [hK];dsimp [Q];omega) (by rw [hdim'];dsimp [Q];omega)
  have hsource := SKCandidateSource.source_operationBound_physical order s hM A
  have hpower : (N+1)^4≤Q^5 :=
    (Nat.pow_le_pow_left (show N+1≤Q by dsimp [Q];omega) 4).trans
      (Nat.pow_le_pow_right hQ (by omega : 4≤5))
  change SKCandidateSource.operationBound s A+SKRestrictedCandidateExecution.operationBound d≤7000*Q^5
  omega
end Manuscript.SKRawCandidateCost
