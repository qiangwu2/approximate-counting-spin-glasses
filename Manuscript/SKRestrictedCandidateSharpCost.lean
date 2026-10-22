import Manuscript.SKRestrictedCandidateCost
import Manuscript.SKRawCandidateCost

/-! The manuscript's local SK operation bound for the actual restricted
instruction trace, retaining its two exponential factors rather than absorbing
its state dimension into an unspecified polynomial overhead. -/
set_option maxHeartbeats 1800000
noncomputable section
namespace Manuscript.SKRestrictedCandidateSharpCost
open RestrictedMachine SpinGlass

theorem expanded_sharp {N B K P M Q : ℕ} (hQ : 1≤Q) (hM : 1≤M)
    (hN : N≤Q) (hB : B≤Q) (hK : K≤Q) (hP : P≤M) :
    SKRestrictedCandidateCost.expanded N B K P M≤10000*Q^4*M^2 := by
  have hmono : SKRestrictedCandidateCost.expanded N B K P M≤
      SKRestrictedCandidateCost.expanded Q Q Q M M := by
    unfold SKRestrictedCandidateCost.expanded
    gcongr
  have hm (i j : ℕ) (hi : i≤4) (hj : j≤2) : Q^i*M^j≤Q^4*M^2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hQ hi) (Nat.pow_le_pow_right hM hj)
  have hdiag : SKRestrictedCandidateCost.expanded Q Q Q M M≤10000*Q^4*M^2 := by
    unfold SKRestrictedCandidateCost.expanded
    nlinarith only [hm 0 0 (by omega) (by omega),hm 0 1 (by omega) (by omega),
      hm 0 2 (by omega) (by omega),hm 1 0 (by omega) (by omega),
      hm 1 1 (by omega) (by omega),hm 1 2 (by omega) (by omega),
      hm 2 0 (by omega) (by omega),hm 2 1 (by omega) (by omega),
      hm 2 2 (by omega) (by omega),hm 3 0 (by omega) (by omega),
      hm 3 1 (by omega) (by omega),hm 3 2 (by omega) (by omega),
      hm 4 0 (by omega) (by omega),hm 4 1 (by omega) (by omega),
      hm 4 2 (by omega) (by omega)]
  exact hmono.trans hdiag

theorem dimension_square (L b : ℕ) :
    ((2*L+1)*2^(2*L)*6^(b+1))^2=(2*L+1)^2*16^L*36^b*36 := by
  have hp : (2^(2*L))^2=16^L := by
    calc
      (2^(2*L))^2=((2^2)^2)^L := by
        simp only [←pow_mul]
        congr 1
        omega
      _=16^L := by norm_num
  have hq : (6^(b+1))^2=36^b*36 := by
    rw [show 6^(b+1)=6^b*6 from pow_succ _ _,mul_pow,←pow_mul,Nat.mul_comm b 2,pow_mul]
    norm_num
  rw [mul_pow,mul_pow,hp,hq]
  ring

theorem candidate_bound (d : SKCandidateLayout.Layout) (N L b : ℕ)
    (hn : d.root.N≤N) (hb : d.root.B=b+1) (hbn : b≤N)
    (hK : d.root.K=2*L) :
    SKRestrictedCandidateExecution.operationBound d≤
      360000*(N+2*L+1)^6*16^L*36^b := by
  let Q := N+2*L+1
  have hQ : 1≤Q := by dsimp [Q];omega
  have hM : 1≤d.M := by
    have hp : 0<d.M := by unfold SKCandidateLayout.Layout.M;positivity
    omega
  have hP : 2^d.root.K≤d.M := by
    unfold SKCandidateLayout.Layout.M
    have hp : 1≤6^d.root.B := one_le_pow₀ (by omega)
    calc
      2^d.root.K≤(d.root.K+1)*2^d.root.K := by nlinarith [Nat.zero_le (d.root.K*2^d.root.K)]
      _≤(d.root.K+1)*2^d.root.K*6^d.root.B := Nat.le_mul_of_pos_right _ (by omega)
  have hbound := expanded_sharp hQ hM (show d.root.N≤Q by dsimp [Q];omega)
    (show d.root.B≤Q by dsimp [Q];omega) (show d.root.K≤Q by dsimp [Q];omega) hP
  rw [←SKRestrictedCandidateCost.operationBound_eq] at hbound
  have hs : d.M^2≤Q^2*16^L*36^b*36 := by
    rw [SKCandidateLayout.Layout.M,hK,hb,dimension_square]
    gcongr
    dsimp [Q];omega
  calc
    SKRestrictedCandidateExecution.operationBound d≤10000*Q^4*d.M^2 := hbound
    _≤10000*Q^4*(Q^2*16^L*36^b*36) := Nat.mul_le_mul_left _ hs
    _=360000*(N+2*L+1)^6*16^L*36^b := by dsimp [Q];ring

theorem raw_candidate_bound {N M : ℕ} (order : Fin M≃Model.Edge N {2})
    (s : State) (hM : s.natReg 501=M) (A : Finset (Fin N)) :
    SKRawCandidate.operationBound s A≤
      361000*(N+2*s.natReg 512+1)^6*16^(s.natReg 512)*36^A.card := by
  let d := SKCandidateSource.layout s A
  have hcandidate : SKRestrictedCandidateExecution.operationBound d≤
      360000*(N+2*s.natReg 512+1)^6*16^(s.natReg 512)*36^A.card :=
    candidate_bound d N (s.natReg 512) A.card
      (by simp [d,SKCandidateSource.layout]) (by simp [d,SKCandidateSource.layout])
      (by simpa using Finset.card_le_univ A) rfl
  have hsource := SKCandidateSource.source_operationBound_physical order s hM A
  have hp : (N+1)^4≤(N+2*s.natReg 512+1)^6 :=
    (Nat.pow_le_pow_left (by omega : N+1≤N+2*s.natReg 512+1) 4).trans
      (Nat.pow_le_pow_right (by omega) (by omega : 4≤6))
  have he : 1≤16^(s.natReg 512)*36^A.card := by
    have h16 : 1≤16^(s.natReg 512) := one_le_pow₀ (by omega)
    have h36 : 1≤36^A.card := one_le_pow₀ (by omega)
    nlinarith
  have hs : (N+1)^4≤(N+2*s.natReg 512+1)^6*16^(s.natReg 512)*36^A.card := by
    calc
      _≤(N+2*s.natReg 512+1)^6 := hp
      _≤(N+2*s.natReg 512+1)^6*(16^(s.natReg 512)*36^A.card) :=
        Nat.le_mul_of_pos_right _ (by omega)
      _=_ := by ring
  change SKCandidateSource.operationBound s A+SKRestrictedCandidateExecution.operationBound d≤_
  nlinarith
end Manuscript.SKRestrictedCandidateSharpCost
