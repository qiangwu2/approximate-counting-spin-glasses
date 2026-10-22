import Manuscript.SKRestrictedMultiply
import Manuscript.SKRestrictedScaleAdd

noncomputable section
namespace Manuscript.SKRestrictedExponential
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays SKRestrictedAlgebra

def body : Program := .seq SKRestrictedMultiply.program SKRestrictedScaleAdd.program
def program : Program := .repeat 34 body

def Ready {b K : ℕ} (base offset n : ℕ) (f : Coefficients b K) (s : State) : Prop :=
  s.natReg 30=base ∧ s.natReg 31=(K+1)*2^K*6^b ∧
  s.natReg 32=offset ∧ s.natReg 33=((K+1)*2^K*6^b)^2 ∧
  s.natReg 35=n ∧ s.natReg 36=1 ∧
  ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K) ∧
  SKRestrictedArrays.Represents base (SKExponential.expLoop f n).1 s.realMem ∧
  SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) f s.realMem ∧
  SKRestrictedArrays.Represents (base+3*((K+1)*2^K*6^b)) (SKExponential.expLoop f n).2 s.realMem

theorem body_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset n : ℕ) (f : Coefficients b K)
    (hs : Ready base offset n f s) :
    ∃ count t, Exec params input body s count t ∧
      count ≤ 56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+97 ∧
      Ready base offset (n+1) f t ∧
      (∀ address, base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  rcases hs with ⟨hbase,hM,hoff,hpairs,hn,hone,hrecords,hpower,hf,hacc⟩
  obtain ⟨c₁,u,hu,bc₁,uv,um⟩ := SKRestrictedMultiply.program_exec params input s base offset
    (SKExponential.expLoop f n).1 f hbase hM hoff hpairs hone hpower hf hrecords
  have un := (SKRestrictedMultiply.program_frame params input hu).1
  have unm := (SKRestrictedMultiply.program_frame params input hu).2
  have uacc : SKRestrictedArrays.Represents (base+3*((K+1)*2^K*6^b))
      (SKExponential.expLoop f n).2 u.realMem := by
    intro x
    rw [um _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact hacc x
  obtain ⟨c₂,t,ht,bc₂,tp,ta,tn,tm⟩ := SKRestrictedScaleAdd.program_exec params input u base n
    (SKCoefficient.mul (SKExponential.expLoop f n).1 f) (SKExponential.expLoop f n).2
    ((un 30 (by omega)).trans hbase) ((un 31 (by omega)).trans hM)
    ((un 35 (by omega)).trans hn) ((un 36 (by omega)).trans hone) uv.2.2 uacc
  have tframe := (SKRestrictedScaleAdd.program_frame params input ht).1
  have tnm := (SKRestrictedScaleAdd.program_frame params input ht).2
  have tf : SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) f t.realMem := by
    intro x
    rw [tm _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact uv.2.1 x
  refine ⟨c₁+c₂,t,Exec.seq hu ht,by omega,?_,?_⟩
  swap
  · intro address ha
    rw [tm _ (by intro i hi; omega),um _ (by intro i hi; omega)]
  refine ⟨(tframe 30 (by omega) (by omega)).trans ((un 30 (by omega)).trans hbase),
    (tframe 31 (by omega) (by omega)).trans ((un 31 (by omega)).trans hM),
    (tframe 32 (by omega) (by omega)).trans ((un 32 (by omega)).trans hoff),
    (tframe 33 (by omega) (by omega)).trans ((un 33 (by omega)).trans hpairs),
    tn,(tframe 36 (by omega) (by omega)).trans ((un 36 (by omega)).trans hone),?_,tp,tf,ta⟩
  rw [tnm,unm]; exact hrecords

theorem repeats_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (base offset : ℕ) (f : Coefficients b K) (steps n : ℕ)
    (s : State) (hs : Ready base offset n f s) :
    ∃ count t, Repeats params input body steps s count t ∧
      count ≤ steps*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+3 ∧
      Ready base offset (n+steps) f t ∧
      (∀ address, base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  induction steps generalizing n s with
  | zero => exact ⟨3,s,Repeats.zero _ _,by simp,by simpa using hs,by intros; rfl⟩
  | succ steps ih =>
    obtain ⟨c,u,hu,bc,hready,um⟩ := body_exec params input s base offset n f hs
    obtain ⟨d,t,ht,bd,hend,tm⟩ := ih (n+1) u hready
    refine ⟨c+d+5,t,Repeats.succ hu ht,?_,?_,?_⟩
    · calc
        c+d+5 ≤ (56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+97)+
          (steps*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+3)+5 := by omega
        _ = (steps+1)*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+3 := by ring
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hend
    · intro address ha; exact (tm address ha).trans (um address ha)

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset iterations : ℕ) (f : Coefficients b K)
    (hs : Ready base offset 0 f s) (hit : s.natReg 34=iterations) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ iterations*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+5 ∧
      Ready base offset iterations f t ∧
      (∀ address, base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  obtain ⟨c,t,he,hc,ht,hm⟩ := repeats_exec params input base offset f iterations 0 s hs
  refine ⟨c+2,t,?_,by omega,by simpa using ht,hm⟩
  rw [← hit] at he
  exact Exec.repeat he

theorem body_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset n : ℕ) (f : Coefficients b K)
    (hs : Ready base offset n f s) :
    ∃ count t, Exec params input body s count t ∧
      count ≤ 56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+97 ∧
      Ready base offset (n+1) f t ∧
      (∀ address, address<base ∨ base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  rcases hs with ⟨hbase,hM,hoff,hpairs,hn,hone,hrecords,hpower,hf,hacc⟩
  obtain ⟨c₁,u,hu,bc₁,uv,um⟩ := SKRestrictedMultiply.program_exec params input s base offset
    (SKExponential.expLoop f n).1 f hbase hM hoff hpairs hone hpower hf hrecords
  have un := (SKRestrictedMultiply.program_frame params input hu).1
  have unm := (SKRestrictedMultiply.program_frame params input hu).2
  have uacc : SKRestrictedArrays.Represents (base+3*((K+1)*2^K*6^b))
      (SKExponential.expLoop f n).2 u.realMem := by
    intro x
    rw [um _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact hacc x
  obtain ⟨c₂,t,ht,bc₂,tp,ta,tn,tm⟩ := SKRestrictedScaleAdd.program_exec params input u base n
    (SKCoefficient.mul (SKExponential.expLoop f n).1 f) (SKExponential.expLoop f n).2
    ((un 30 (by omega)).trans hbase) ((un 31 (by omega)).trans hM)
    ((un 35 (by omega)).trans hn) ((un 36 (by omega)).trans hone) uv.2.2 uacc
  have tframe := (SKRestrictedScaleAdd.program_frame params input ht).1
  have tnm := (SKRestrictedScaleAdd.program_frame params input ht).2
  have tf : SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) f t.realMem := by
    intro x
    rw [tm _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact uv.2.1 x
  refine ⟨c₁+c₂,t,Exec.seq hu ht,by omega,?_,?_⟩
  swap
  · intro address ha
    rw [tm _ (by intro i hi; omega),um _ (by intro i hi; omega)]
  refine ⟨(tframe 30 (by omega) (by omega)).trans ((un 30 (by omega)).trans hbase),
    (tframe 31 (by omega) (by omega)).trans ((un 31 (by omega)).trans hM),
    (tframe 32 (by omega) (by omega)).trans ((un 32 (by omega)).trans hoff),
    (tframe 33 (by omega) (by omega)).trans ((un 33 (by omega)).trans hpairs),
    tn,(tframe 36 (by omega) (by omega)).trans ((un 36 (by omega)).trans hone),?_,tp,tf,ta⟩
  rw [tnm,unm]; exact hrecords

theorem repeats_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (base offset : ℕ) (f : Coefficients b K) (steps n : ℕ)
    (s : State) (hs : Ready base offset n f s) :
    ∃ count t, Repeats params input body steps s count t ∧
      count ≤ steps*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+3 ∧
      Ready base offset (n+steps) f t ∧
      (∀ address, address<base ∨ base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  induction steps generalizing n s with
  | zero => exact ⟨3,s,Repeats.zero _ _,by simp,by simpa using hs,by intros; rfl⟩
  | succ steps ih =>
    obtain ⟨c,u,hu,bc,hready,um⟩ := body_exec_framed params input s base offset n f hs
    obtain ⟨d,t,ht,bd,hend,tm⟩ := ih (n+1) u hready
    refine ⟨c+d+5,t,Repeats.succ hu ht,?_,?_,?_⟩
    · calc
        c+d+5 ≤ (56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+97)+
          (steps*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+3)+5 := by omega
        _ = (steps+1)*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+3 := by ring
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hend
    · intro address ha; exact (tm address ha).trans (um address ha)

theorem program_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset iterations : ℕ) (f : Coefficients b K)
    (hs : Ready base offset 0 f s) (hit : s.natReg 34=iterations) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ iterations*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102)+5 ∧
      Ready base offset iterations f t ∧
      (∀ address, address<base ∨ base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  obtain ⟨c,t,he,hc,ht,hm⟩ := repeats_exec_framed params input base offset f iterations 0 s hs
  refine ⟨c+2,t,?_,by omega,by simpa using ht,hm⟩
  rw [← hit] at he
  exact Exec.repeat he

end Manuscript.SKRestrictedExponential
