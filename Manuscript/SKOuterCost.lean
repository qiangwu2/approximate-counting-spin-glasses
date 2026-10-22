import Manuscript.RestrictedSKOuterBridge
import Manuscript.SKCandidateContract
import Manuscript.SKRuntimeNumeric

noncomputable section
open scoped BigOperators
namespace Manuscript.SKOuterCost
open RestrictedMachine SKCandidateExecution

theorem cost_bound {N D L R : ℕ} (hD : D≤N) (hR : 0<R)
    (χ : SKColorEstimator.Colors (Fin N) L R) (mean : ℝ) (w : Finset (Fin N)→ℝ) :
    RestrictedSKOuter.cost (SKCandidateContract.bound χ mean w) N R (D+1) 0+12≤
      10000*(N+(SKGeneratedExecution.estimator D L R χ mean w).operations+1)^6 := by
  let W:=(SKGeneratedExecution.estimator D L R χ mean w).operations
  let C:=(candidates (Fin N) D).card
  have hRC : R*C≤W:=SKGlobalLowerBound.trials_candidates D L R χ mean w
  have hC : C≤W := (Nat.le_mul_of_pos_left C hR).trans hRC
  have hcandidates : (∑b∈Finset.range (D+1),N.choose b)=C := by
    simpa [C] using (SKGlobalLowerBound.candidates_card (V:=Fin N) D).symm
  have hgen : (∑b∈Finset.range (D+1),RestrictedSubsets.work N b)≤63*(2*N+1)*C := by
    calc
      _ ≤ ∑b∈Finset.range (D+1),63*(2*N+1)*N.choose b := by
        apply Finset.sum_le_sum
        intro b hb
        exact RestrictedSubsets.work_bound (by have:=Finset.mem_range.mp hb;omega)
      _ = _ := by rw [←Finset.mul_sum,hcandidates]
  have hlocal (A : Finset (Fin N)) (hA : A∈candidates (Fin N) D) :
      SKCandidateContract.bound χ mean w (RestrictedMaskBridge.encode A)≤7000*(N+W+1)^5 := by
    have havg : (SKGeneratedExecution.average L R A (χ A) mean w).operations≤W :=
      (Finset.single_le_sum (f:=fun A : Finset (Fin N)=>
        (SKGeneratedExecution.average L R A (χ A) mean w).operations)
        (fun _ _=>Nat.zero_le _) hA).trans (SKGlobalLowerBound.estimator_lower D L R χ mean w)
    simp only [SKCandidateContract.bound,SKCandidateContract.decodeMask_encode]
    gcongr
  have hsum : (∑b∈Finset.range (D+1),∑A∈(Finset.univ : Finset (Fin N)).powersetCard b,
      (R*(SKCandidateContract.bound χ mean w (RestrictedMaskBridge.encode A)+29)+35))≤
      (R*(7000*(N+W+1)^5+29)+35)*C := by
    rw [←sum_candidates]
    calc
      _ ≤ ∑_A∈candidates (Fin N) D,(R*(7000*(N+W+1)^5+29)+35) := by
        apply Finset.sum_le_sum
        intro A hA
        exact Nat.add_le_add_right (Nat.mul_le_mul_left R (Nat.add_le_add_right (hlocal A hA) 29)) 35
      _ = _ := by simp [C,Nat.mul_comm]
  apply SKRuntimeNumeric.truncated N W R C D _ hC hRC hD
  rw [RestrictedSKOuterBridge.cost_range]
  simp only [Nat.zero_add]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
  omega

end Manuscript.SKOuterCost
