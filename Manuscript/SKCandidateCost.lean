import Manuscript.SKCandidatePrimitives
import Manuscript.SKExecutionLowerBound
import Manuscript.SKRestrictedCandidateExecution

set_option maxHeartbeats 1200000
noncomputable section
namespace Manuscript.SKCandidateCost

theorem primitive_bound (n b K Q : ℕ) (hQ : 1≤Q) (hn : n≤Q) (hb : b≤Q) (hK : K≤Q)
    (hmask : 2^K≤Q) (hreg : (K+1)*2^K*6^b≤Q) :
    SKPrimitiveAssembly.operationBound n b K≤1000*Q^4 := by
  have h1 : 27*n+58*K+18*b+229≤332*Q := by omega
  have h2 : 27*n+18≤45*Q := by omega
  have h3 : n*(27*n+18)+58*K+147≤250*Q^2 := by
    have hh := Nat.mul_le_mul hn h2
    have hpow : Q≤Q^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hQ (by decide : 1≤2)
    nlinarith
  have hterm1 : b*b*2^K*(27*n+58*K+18*b+229)≤332*Q^4 := by
    calc
      _≤Q*Q*Q*(332*Q) := by gcongr
      _=_ := by ring
  have hterm2 : 2^K*(n*(27*n+18)+58*K+147)≤250*Q^3 := by
    calc
      _≤Q*(250*Q^2) := Nat.mul_le_mul hmask h3
      _=_ := by ring
  have hpow1 : Q≤Q^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hQ (by decide : 1≤4)
  have hpow3 : Q^3≤Q^4 := Nat.pow_le_pow_right hQ (by decide : 3≤4)
  unfold SKPrimitiveAssembly.operationBound
  nlinarith

theorem root_body_bound (d : SKRootCache.Layout) (Q : ℕ) (hQ : 1≤Q)
    (hn : d.N≤Q) (hK : d.K≤Q) (hmask : 2^d.K≤Q) :
    SKRootCache.bodyCost d+5≤500*Q^4 := by
  have hT : d.T≤Q^2 := by
    change 2^d.K*d.N≤Q^2
    simpa [pow_two] using Nat.mul_le_mul hmask hn
  have hlin : 38*d.K+27*d.N+137≤202*Q := by omega
  have hprod : d.T*(38*d.K+27*d.N+137)+21≤223*Q^3 := by
    have hp := Nat.mul_le_mul hT hlin
    have hpow : 1≤Q^3 := Nat.one_le_pow _ _ hQ
    nlinarith
  have hnested : d.K*(d.T*(38*d.K+27*d.N+137)+21)≤223*Q^4 := by
    calc
      _≤Q*(223*Q^3) := Nat.mul_le_mul hK hprod
      _=_ := by ring
  have hpow1 : Q≤Q^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hQ (by decide : 1≤4)
  have hpow2 : Q^2≤Q^4 := Nat.pow_le_pow_right hQ (by decide : 2≤4)
  unfold SKRootCache.bodyCost SKRootCache.memoCost
  nlinarith

theorem frontend_bound (d : SKCandidateLayout.Layout) (Q : ℕ) (hQ : 1≤Q)
    (hn : d.root.N≤Q) (hb : d.root.B≤Q) (hK : d.root.K≤Q)
    (hmask : 2^d.root.K≤Q) (hreg : d.M≤Q) :
    SKCandidatePrimitives.operationBound d≤3000*Q^5 := by
  have hp := primitive_bound d.root.N d.root.B d.root.K Q hQ hn hb hK hmask hreg
  have hr := root_body_bound d.root Q hQ hn hK hmask
  have hprod : (d.root.B+d.root.N)*(SKRootCache.bodyCost d.root+5)≤1000*Q^5 := by
    calc
      _≤(2*Q)*(500*Q^4) := Nat.mul_le_mul (by omega) hr
      _=_ := by ring
  have hpow1 : Q≤Q^5 := by simpa only [pow_one] using Nat.pow_le_pow_right hQ (by decide : 1≤5)
  have hpow4 : Q^4≤Q^5 := Nat.pow_le_pow_right hQ (by decide : 4≤5)
  unfold SKCandidatePrimitives.operationBound
  nlinarith

theorem backend_bound (d : SKCandidateLayout.Layout) (Q : ℕ) (hQ : 1≤Q)
    (hb : d.root.B≤Q) (hK : d.root.K≤Q) (hreg : d.M≤Q) :
    SKCandidateBackend.operationBound d≤3000*Q^4 := by
  have hmono : SKCandidateBackend.operationBound d≤
      Q*Q*(30*Q+18*Q+141)+10+Q^2*(52*Q+29*Q+157)+11+
        (Q+Q*Q)*(56*Q^2+90*Q+111)+90*Q+104+Q*(40*Q+53*Q+110)+8+100 := by
    unfold SKCandidateBackend.operationBound
    gcongr
  have h0 : 1≤Q^4 := Nat.one_le_pow _ _ hQ
  have h1 : Q≤Q^4 := by simpa using Nat.pow_le_pow_right hQ (show 1≤4 by omega)
  have h2 : Q^2≤Q^4 := Nat.pow_le_pow_right hQ (by omega)
  have h3 : Q^3≤Q^4 := Nat.pow_le_pow_right hQ (by omega)
  nlinarith

theorem full_bound (d : SKCandidateLayout.Layout) (Q : ℕ) (hQ : 1≤Q)
    (hn : d.root.N≤Q) (hb : d.root.B≤Q) (hK : d.root.K≤Q)
    (hmask : 2^d.root.K≤Q) (hreg : d.M≤Q) :
    SKRestrictedCandidateExecution.operationBound d≤6000*Q^5 := by
  have hfront := frontend_bound d Q hQ hn hb hK hmask hreg
  have hback := backend_bound d Q hQ hb hK hreg
  have hpow : Q^4≤Q^5 := Nat.pow_le_pow_right hQ (by omega)
  unfold SKRestrictedCandidateExecution.operationBound
  omega

end Manuscript.SKCandidateCost
