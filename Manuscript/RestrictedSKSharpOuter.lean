import Manuscript.SKOuterCost
import Manuscript.RestrictedSKTruncated
import Manuscript.SKRestrictedCandidateSharpCost

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSKSharpOuter
open RestrictedMachine SKCandidateContract

def factor (N L : ℕ) : ℕ := (N+2*L+1)^6*16^L

def bound (C N L mask : ℕ) : ℕ :=
  C*factor N L*36^(decodeMask N mask).card

theorem factor_lower (N L : ℕ) : N+1≤factor N L := by
  have h1 : N+1≤N+2*L+1 := by omega
  have h2 : N+2*L+1≤(N+2*L+1)^6 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤N+2*L+1) (by decide : 1≤6)
  have h3 : 1≤16^L := Nat.one_le_pow _ _ (by decide)
  exact (h1.trans h2).trans (Nat.le_mul_of_pos_right _ h3)

theorem layer_bound (C N L R b : ℕ) (hR : 0<R) (hb : b≤N) :
    RestrictedSubsets.work N b+
      (∑A∈(Finset.univ : Finset (Fin N)).powersetCard b,
        (R*(bound C N L (RestrictedMaskBridge.encode A)+29)+35))+66≤
      (C+256)*R*factor N L*(N.choose b*36^b) := by
  let G:=factor N L*36^b
  let q:=N.choose b
  have hq : 1≤q := Nat.choose_pos hb
  have hG : N+1≤G := (factor_lower N L).trans
    (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by decide : 1≤36)))
  have hRG : G≤R*G := Nat.le_mul_of_pos_left G hR
  have hG1 : 1≤G := by omega
  have hRle : R≤R*G := Nat.le_mul_of_pos_right _ hG1
  have hsum : (∑A∈(Finset.univ : Finset (Fin N)).powersetCard b,
      (R*(bound C N L (RestrictedMaskBridge.encode A)+29)+35))=
      q*(R*(C*G+29)+35) := by
    calc
      _ = ∑_A∈(Finset.univ : Finset (Fin N)).powersetCard b,
          (R*(C*G+29)+35) := by
        apply Finset.sum_congr rfl
        intro A hA
        have hcard := (Finset.mem_powersetCard.mp hA).2
        simp [bound,decodeMask_encode,hcard,G,Nat.mul_assoc]
      _ = _ := by simp [q]
  rw [hsum]
  have hgen := RestrictedSubsets.work_bound hb
  have hgen' : RestrictedSubsets.work N b≤126*R*G*q := by
    have hg : 63*(2*N+1)≤126*R*G := by nlinarith
    exact hgen.trans (Nat.mul_le_mul_right q hg)
  have hlocal : R*(C*G+29)+35≤(C+64)*R*G := by nlinarith
  have hsum' := Nat.mul_le_mul_left q hlocal
  have h66 : 66≤66*R*G*q := by
    have hh : 1≤R*G*q := Nat.mul_le_mul (by omega : 1≤R*G) hq
    nlinarith
  dsimp [G,q] at *
  nlinarith

/-- Sharp cardinality/trial aggregation, including actual subset generation
and all loop overhead. The local bound is instantiated by a concrete raw
candidate execution theorem in the operational result below. -/
theorem cost_bound (C N D L R : ℕ) (hD : D≤N) (hR : 0<R) :
    RestrictedSKOuter.cost (bound C N L) N R (D+1) 0+12≤
      (C+1000)*R*factor N L*(∑b∈Finset.range (D+1),N.choose b*36^b) := by
  rw [RestrictedSKOuterBridge.cost_range]
  simp only [Nat.zero_add]
  have hsum : (∑b∈Finset.range (D+1),
      (RestrictedSubsets.work N b+
        (∑A∈(Finset.univ : Finset (Fin N)).powersetCard b,
          (R*(bound C N L (RestrictedMaskBridge.encode A)+29)+35))+66))≤
      (C+256)*R*factor N L*(∑b∈Finset.range (D+1),N.choose b*36^b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    exact layer_bound C N L R b hR (by have:=Finset.mem_range.mp hb;omega)
  have hS : 1≤∑b∈Finset.range (D+1),N.choose b*36^b := by
    have hh:=Finset.single_le_sum (fun b (_ : b∈Finset.range (D+1))=>Nat.zero_le (N.choose b*36^b))
      (show 0∈Finset.range (D+1) by simp)
    simpa using hh
  have hF : 1≤factor N L := by have:=factor_lower N L;omega
  have hprod : 1≤R*factor N L*(∑b∈Finset.range (D+1),N.choose b*36^b) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by omega : 1≤R) hF) hS
  nlinarith

theorem realized {N M D L R : ℕ} (hL : 0<L) (params : Parameters)
    (order : Fin M≃Model.Edge N {2}) (a : ℕ→ℝ) (beta h epsilon delta : ℝ)
    (J : Model.Edge N {2}→ℝ) (χ : SKColorEstimator.Colors (Fin N) L R)
    (s : State) (hs : Ready order a beta h J D L R s)
    (hp : RestrictedSKTrials.Prepared s) :
    ∃count t,Exec params (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
      SKRawCandidate.program s count t ∧
      RestrictedSKTrials.CandidateResult (Ready order a beta h J D L R)
        (value χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J))
        (bound 361000 N L) s t count := by
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
  · have hcost := SKRestrictedCandidateSharpCost.raw_candidate_bound order s hs.1.physical.count A
    rw [hs.1.retained] at hcost
    exact bc.trans (by simpa [bound,factor,A,Nat.mul_assoc] using hcost)
  · intro j hj;exact hrn j (by omega) (by omega)
  · intro j hj;exact hrr j (by omega)
/-- Proposition 4.5's displayed operation formula for the actual fixed
primitive estimator, including generated candidates, raw trial reads,
source matrices, every candidate evaluation and trial averaging. All modular
callback hypotheses are discharged by the raw candidate implementation. -/
theorem program_exec {N M D L R : ℕ} (hL : 0<L) (hR : 0<R) (hD : D≤N) (params : Parameters)
    (order : Fin M≃Model.Edge N {2}) (a : ℕ→ℝ) (beta h epsilon delta : ℝ)
    (J : Model.Edge N {2}→ℝ) (χ : SKColorEstimator.Colors (Fin N) L R)
    (s : State) (hs : SKCandidateContract.Core order a beta h J D L R s)
    (hbase : s.natReg 501≤s.natReg 576) :
    ∃count t,RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table params
        (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
        RestrictedSKTruncated.program s count t ∧
      t.realReg 572=(SKGeneratedExecution.estimator D L R χ (Real.tanh h)
        (SKGhostCoefficient.inputWeight N a beta J)).value ∧
      count≤362000*R*(N+2*L+1)^6*16^L*
        (∑b∈Finset.range (D+1),N.choose b*36^b) ∧
      SKCandidateContract.Core order a beta h J D L R t ∧
      (∀r,580<r ∨ r=500 ∨ r=501 ∨ r=510 ∨ r=512 ∨ r=513 ∨ r=570 ∨ r=576 → t.natReg r=s.natReg r) ∧
      (∀r,573≤r → t.realReg r=s.realReg r) ∧
      (∀j,j<s.natReg 576 → t.natMem j=s.natMem j) := by
  obtain ⟨c,t,he,hp,hc,hv,hn,hr,hm⟩ := RestrictedSKOuter.program_exec params
    (RestrictedInputEncoding.encode order beta h epsilon delta J (SKRawColorTape.encode χ))
    SKRawCandidate.program (SKCandidateContract.Core order a beta h J D L R)
    (SKCandidateContract.core_stable order a beta h J D L R)
    (SKCandidateContract.value χ (Real.tanh h) (SKGhostCoefficient.inputWeight N a beta J))
    (bound 361000 N L)
    (realized hL params order a beta h epsilon delta J χ) s hs hbase
  refine ⟨c,t,RestrictedSKOuterBridge.embed he,?_,?_,hp,hn,hr,hm⟩
  · rw [hv,hs.physical.size,hs.repeats,hs.cutoff]
    apply RestrictedSKOuterBridge.value_eq_estimator
    intro A r
    simp [SKCandidateContract.value,SKCandidateContract.decodeMask_encode,r.isLt]
  · have hc' : c≤RestrictedSKOuter.cost (bound 361000 N L) N R (D+1) 0+12 := by
      simpa [hs.physical.size,hs.repeats,hs.cutoff] using hc
    exact hc'.trans (by simpa [factor,Nat.mul_assoc] using cost_bound 361000 N D L R hD hR)

end Manuscript.RestrictedSKSharpOuter
