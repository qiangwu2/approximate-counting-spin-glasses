import Manuscript.SKRestrictedDirectStep
import SpinGlass.SKExponential

noncomputable section
namespace Manuscript.SKRestrictedDirect
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays SKRestrictedAlgebra

def Bank {b K : ℕ} : ℕ → List (Coefficients b K) → (ℕ → ℝ) → Prop
  | _, [], _ => True
  | base, f::fs, memory => SKRestrictedArrays.Represents base f memory ∧
      Bank (base+(K+1)*2^K*6^b) fs memory

theorem bank_frame {b K : ℕ} (bank : ℕ) (es : List (Coefficients b K))
    (old new : ℕ → ℝ) (h : ∀ address, bank ≤ address → new address=old address)
    (hold : Bank bank es old) : Bank bank es new := by
  induction es generalizing bank with
  | nil => trivial
  | cons e es ih =>
    refine ⟨?_,ih _ (fun address ha => h address (by omega)) hold.2⟩
    intro x; rw [h _ (by omega)]; exact hold.1 x

def program : Program := .repeat 39 SKRestrictedDirectStep.program

theorem repeats_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (base offset : ℕ) (es : List (Coefficients b K)) (s : State) (bank : ℕ)
    (acc : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1) (hbank : s.natReg 37=bank)
    (hseparate : base+3*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hacc : SKRestrictedArrays.Represents base acc s.realMem)
    (hdata : Bank bank es s.realMem) :
    ∃ count t, Repeats params input SKRestrictedDirectStep.program es.length s count t ∧
      count ≤ es.length*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+3 ∧
      SKRestrictedArrays.Represents base (SKExponential.directLoop es acc) t.realMem := by
  induction es generalizing s bank acc with
  | nil => exact ⟨3,s,Repeats.zero _ _,by simp,hacc⟩
  | cons e es ih =>
    obtain ⟨c,u,hu,hc,ua,ub,un,unm,um⟩ := SKRestrictedDirectStep.program_exec params input s base offset
      bank acc e hbase hM hoff hpairs hone hbank hseparate hrecords hacc hdata.1
    have tail : Bank (bank+(K+1)*2^K*6^b) es u.realMem :=
      bank_frame _ es s.realMem u.realMem (fun address ha => um address (by omega)) hdata.2
    obtain ⟨d,t,ht,hd,hout⟩ := ih u (bank+(K+1)*2^K*6^b) (SKCoefficient.mul acc (one b K+e))
      ((un 30 (by omega) (by omega) (by omega) (by omega)).trans hbase)
      ((un 31 (by omega) (by omega) (by omega) (by omega)).trans hM)
      ((un 32 (by omega) (by omega) (by omega) (by omega)).trans hoff)
      ((un 33 (by omega) (by omega) (by omega) (by omega)).trans hpairs)
      ((un 36 (by omega) (by omega) (by omega) (by omega)).trans hone)
      ub (by omega) (by rwa [unm]) ua tail
    refine ⟨c+d+5,t,Repeats.succ hu ht,?_,hout⟩
    simp only [List.length_cons]
    calc
      c+d+5 ≤ (56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+106)+
        (es.length*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+3)+5 := by omega
      _ = (es.length+1)*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+3 := by ring

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (base offset : ℕ) (es : List (Coefficients b K)) (s : State) (bank : ℕ)
    (acc : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1) (hbank : s.natReg 37=bank) (hcount : s.natReg 39=es.length)
    (hseparate : base+3*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hacc : SKRestrictedArrays.Represents base acc s.realMem)
    (hdata : Bank bank es s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ es.length*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+5 ∧
      SKRestrictedArrays.Represents base (SKExponential.directLoop es acc) t.realMem := by
  obtain ⟨c,t,he,hc,hout⟩ := repeats_exec params input base offset es s bank acc
    hbase hM hoff hpairs hone hbank hseparate hrecords hacc hdata
  refine ⟨c+2,t,?_,by omega,hout⟩
  rw [← hcount] at he
  exact Exec.repeat he

theorem repeats_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (base offset : ℕ) (es : List (Coefficients b K)) (s : State) (bank : ℕ)
    (acc : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1) (hbank : s.natReg 37=bank)
    (hseparate : base+3*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hacc : SKRestrictedArrays.Represents base acc s.realMem)
    (hdata : Bank bank es s.realMem) :
    ∃ count t, Repeats params input SKRestrictedDirectStep.program es.length s count t ∧
      count ≤ es.length*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+3 ∧
      SKRestrictedArrays.Represents base (SKExponential.directLoop es acc) t.realMem ∧
      (∀ address, address<base → t.realMem address=s.realMem address) := by
  induction es generalizing s bank acc with
  | nil => exact ⟨3,s,Repeats.zero _ _,by simp,hacc,by intros; rfl⟩
  | cons e es ih =>
    obtain ⟨c,u,hu,hc,ua,ub,un,unm,um⟩ := SKRestrictedDirectStep.program_exec_framed params input s base offset
      bank acc e hbase hM hoff hpairs hone hbank hseparate hrecords hacc hdata.1
    have tail : Bank (bank+(K+1)*2^K*6^b) es u.realMem :=
      bank_frame _ es s.realMem u.realMem (fun address ha => um address (Or.inr (by omega))) hdata.2
    obtain ⟨d,t,ht,hd,hout,tm⟩ := ih u (bank+(K+1)*2^K*6^b) (SKCoefficient.mul acc (one b K+e))
      ((un 30 (by omega) (by omega) (by omega) (by omega)).trans hbase)
      ((un 31 (by omega) (by omega) (by omega) (by omega)).trans hM)
      ((un 32 (by omega) (by omega) (by omega) (by omega)).trans hoff)
      ((un 33 (by omega) (by omega) (by omega) (by omega)).trans hpairs)
      ((un 36 (by omega) (by omega) (by omega) (by omega)).trans hone)
      ub (by omega) (by rwa [unm]) ua tail
    refine ⟨c+d+5,t,Repeats.succ hu ht,?_,hout,fun address ha => (tm address ha).trans (um address (Or.inl ha))⟩
    simp only [List.length_cons]
    calc
      c+d+5 ≤ (56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+106)+
        (es.length*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+3)+5 := by omega
      _ = (es.length+1)*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+3 := by ring

theorem program_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (base offset : ℕ) (es : List (Coefficients b K)) (s : State) (bank : ℕ)
    (acc : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1) (hbank : s.natReg 37=bank) (hcount : s.natReg 39=es.length)
    (hseparate : base+3*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hacc : SKRestrictedArrays.Represents base acc s.realMem)
    (hdata : Bank bank es s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ es.length*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+5 ∧
      SKRestrictedArrays.Represents base (SKExponential.directLoop es acc) t.realMem ∧
      (∀ address, address<base → t.realMem address=s.realMem address) := by
  obtain ⟨c,t,he,hc,hout,hm⟩ := repeats_exec_framed params input base offset es s bank acc
    hbase hM hoff hpairs hone hbank hseparate hrecords hacc hdata
  refine ⟨c+2,t,?_,by omega,hout,hm⟩
  rw [← hcount] at he
  exact Exec.repeat he

end Manuscript.SKRestrictedDirect
