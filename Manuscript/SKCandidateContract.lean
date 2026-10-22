import Manuscript.SKRawCandidateCost
import Manuscript.RestrictedSKLayer
import Manuscript.SKGlobalLowerBound

/-! Concrete physical invariant and candidate callback for the uniform
trial/candidate loops. The realization theorem invokes the fixed raw-candidate
program; it is not an assumed correctness or running-time contract. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Manuscript.SKCandidateContract
open RestrictedMachine SpinGlass

structure Core {N M : ℕ} (order : Fin M≃Model.Edge N {2})
    (a : ℕ→ℝ) (beta h : ℝ) (J : Model.Edge N {2}→ℝ) (D L R : ℕ) (s : State) : Prop where
  physical : SKCandidateSource.PhysicalData order a beta h J s
  cutoff : s.natReg 510=D
  retained : s.natReg 512=L
  repeats : s.natReg 513=R
  tape : s.natReg 570=2*M+2

def Ready {N M : ℕ} (order : Fin M≃Model.Edge N {2})
    (a : ℕ→ℝ) (beta h : ℝ) (J : Model.Edge N {2}→ℝ) (D L R : ℕ) (s : State) : Prop :=
  Core order a beta h J D L R s ∧ RestrictedSKLayer.SafeLayout s

theorem Core.transport {N M : ℕ} {order : Fin M≃Model.Edge N {2}}
    {a : ℕ→ℝ} {beta h : ℝ} {J : Model.Edge N {2}→ℝ} {D L R : ℕ} {s t : State}
    (hs : Core order a beta h J D L R s)
    (hn : ∀r,r=500 ∨ r=501 ∨ r=510 ∨ r=512 ∨ r=513 ∨ r=570 → t.natReg r=s.natReg r)
    (hr : t.realReg 504=s.realReg 504)
    (hm : ∀j,j<M → t.natMem j=s.natMem j)
    (hw : ∀j,j<2*M → t.realMem j=s.realMem j) : Core order a beta h J D L R t := by
  refine ⟨SKCandidateSource.PhysicalData.transport order a beta h J hs.physical
    (fun r hlo hhi => hn r (by omega)) hr hm hw,
    (hn 510 (by omega)).trans hs.cutoff,(hn 512 (by omega)).trans hs.retained,
    (hn 513 (by omega)).trans hs.repeats,(hn 570 (by omega)).trans hs.tape⟩

theorem core_stable {N M : ℕ} (order : Fin M≃Model.Edge N {2})
    (a : ℕ→ℝ) (beta h : ℝ) (J : Model.Edge N {2}→ℝ) (D L R : ℕ) :
    RestrictedSKLayer.Stable (Core order a beta h J D L R) := by
  constructor
  · intro s hs r v hr
    apply hs.transport
    · intro j hj
      simp [show j≠r by omega]
    · rfl
    · intro j hj;rfl
    · intro j hj;rfl
  · intro s hs r v hr
    apply hs.transport
    · intro j hj;rfl
    · simp [show 504≠r by omega]
    · intro j hj;rfl
    · intro j hj;rfl
  · intro s hs j v hj
    apply hs.transport
    · intro r hr;rfl
    · rfl
    · intro k hk
      have hj' : M≤j := by rwa [hs.physical.count] at hj
      simp [writeNatMem,Function.update_apply,show k≠j by omega]
    · intro k hk;rfl

theorem ready_stable {N M : ℕ} (order : Fin M≃Model.Edge N {2})
    (a : ℕ→ℝ) (beta h : ℝ) (J : Model.Edge N {2}→ℝ) (D L R : ℕ) :
    RestrictedSKTrials.Stable (Ready order a beta h J D L R) :=
  (RestrictedSKLayer.fold_stable (core_stable order a beta h J D L R)).trials

def decodeMask (N mask : ℕ) : Finset (Fin N) :=
  if h : mask<2^N then (SKBasisEncoding.maskEquiv N).symm ⟨mask,h⟩ else ∅

def value {N L R : ℕ} (χ : SKColorEstimator.Colors (Fin N) L R)
    (mean : ℝ) (w : Finset (Fin N)→ℝ) (mask trial : ℕ) : ℝ :=
  if hr : trial<R then
    (SKGeneratedExecution.trial L (decodeMask N mask) (χ (decodeMask N mask) ⟨trial,hr⟩) mean w).value else 0

def bound {N L R : ℕ} (χ : SKColorEstimator.Colors (Fin N) L R)
    (mean : ℝ) (w : Finset (Fin N)→ℝ) (mask : ℕ) : ℕ :=
  7000*(N+(SKGeneratedExecution.average L R (decodeMask N mask) (χ (decodeMask N mask)) mean w).operations+1)^5

theorem decodeMask_encode {N : ℕ} (A : Finset (Fin N)) :
    decodeMask N (RestrictedMaskBridge.encode A)=A := by
  simp [decodeMask,RestrictedMaskBridge.encode,(SKBasisEncoding.maskEquiv N A).isLt]

theorem encode_decodeMask {N mask : ℕ} (h : mask<2^N) :
    RestrictedMaskBridge.encode (decodeMask N mask)=mask := by
  simp [decodeMask,h,RestrictedMaskBridge.encode]

theorem realized {N M D L R : ℕ} (hL : 0<L) (params : Parameters)
    (order : Fin M≃Model.Edge N {2}) (a : ℕ→ℝ) (beta h epsilon delta : ℝ)
    (J : Model.Edge N {2}→ℝ) (χ : SKColorEstimator.Colors (Fin N) L R)
    (s : State) (hs : Ready order a beta h J D L R s)
    (hp : RestrictedSKTrials.Prepared s) :
    ∃count t,Exec params (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
      SKRawCandidate.program s count t ∧
      RestrictedSKTrials.CandidateResult (Ready order a beta h J D L R)
        (value χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J))
        (bound χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)) s t count := by
  have hfit : M≤s.natReg 530 := by rw [←hs.1.physical.count];exact hs.2.2
  let A := decodeMask N (s.natReg 520)
  have hmask : s.natReg 520<2^N := by simpa [hs.1.physical.size] using hp.1
  have htrial : s.natReg 521<R := by simpa [hs.1.repeats] using hp.2.1
  let r : Fin R := ⟨s.natReg 521,htrial⟩
  have hA : s.natReg 520=RestrictedMaskBridge.encode A := (encode_decodeMask hmask).symm
  have hptr : s.natReg 522=2*M+2+(RestrictedMaskBridge.encode A*R+r.val)*N := by
    simpa [hs.1.tape,hs.1.repeats,hs.1.physical.size,r,←hA] using hp.2.2
  obtain ⟨c,t,he,bc,hv,hn,hm,hrn,hrr⟩ := SKRawCandidate.encoded_program_exec params order a beta h epsilon delta
    J χ s A r hL hs.1.retained hA hptr hs.1.physical hfit hs.2.1
  refine ⟨c,t,he,?_,?_,?_,?_,?_,hn⟩
  · constructor
    · apply hs.1.transport
      · intro j hj;exact hrn j (by omega) (by omega)
      · exact hrr 504 (by omega)
      · intro j hj;exact hn j (by omega)
      · intro j hj;exact hm j (by rw [hs.1.physical.count];exact hj)
    · constructor
      · have h500 := hrn 500 (by omega) (by omega)
        have h530 := hrn 530 (by omega) (by omega)
        have h531 := hrn 531 (by omega) (by omega)
        have h532 := hrn 532 (by omega) (by omega)
        have h533 := hrn 533 (by omega) (by omega)
        constructor
        · simpa [h500,h530,h531] using hs.2.1.branch_before
        · simpa [h500,h531,h532] using hs.2.1.outside_before
        · simpa [h500,h532,h533] using hs.2.1.charge_before
      · rw [hrn 501 (by omega) (by omega),hrn 530 (by omega) (by omega)]
        exact hs.2.2
  · simpa [value,htrial,A,r] using hv
  · have hcost : SKRawCandidate.operationBound s A≤
        7000*(N+(SKGeneratedExecution.trial L A (χ A r) (Real.tanh h)
          (SKGhostCoefficient.inputWeight N a beta J)).operations+1)^5 := by
      have hret := hs.1.retained
      subst L
      exact SKRawCandidateCost.operationBound_le order s hs.1.physical.count A
        (χ A r) (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)
    have hsum : (SKGeneratedExecution.trial L A (χ A r) (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)).operations≤
        (SKGeneratedExecution.average L R A (χ A) (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)).operations :=
      (Finset.single_le_sum (f:=fun r:Fin R =>
        (SKGeneratedExecution.trial L A (χ A r) (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)).operations)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ r)).trans
        (SKGlobalLowerBound.average_lower L R A (χ A) (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J)).2
    exact bc.trans (hcost.trans (by unfold bound;dsimp [A] at *;gcongr))
  · intro j hj;exact hrn j (by omega) (by omega)
  · intro j hj;exact hrr j (by omega)
end Manuscript.SKCandidateContract
