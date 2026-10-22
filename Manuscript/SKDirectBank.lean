import Manuscript.SKDirectFactor
import Manuscript.SKRestrictedDirect

noncomputable section
set_option maxHeartbeats 1200000
namespace Manuscript.SKDirectBank
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays

def setup : List Instruction :=
  [.ndiv 442 459 440,.nmod 443 459 440,.nmul 37 459 31,.nadd 37 460 37]
def advance : List Instruction := [.nadd 459 459 36]
def body : Program := .seq (code setup) (.seq SKDirectFactor.program (code advance))
def initCode : List Instruction := [.nconst 459 0,.nmul 461 440 440]
def program : Program := .seq (code initCode) (.repeat 461 body)

def pairs {b : ℕ} (i : Fin (b*b)) : Fin b × Fin b :=
  have hb : 0<b := by
    cases b with
    | zero => exact Fin.elim0 i
    | succ b => omega
  (⟨i.val/b,Nat.div_lt_of_lt_mul i.isLt⟩,⟨i.val%b,Nat.mod_lt _ hb⟩)

def entry {V : Type*} [DecidableEq V] {b K : ℕ}
    (charge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ) (i : ℕ) : Coefficients b K :=
  if hi : i<b*b then SKDirectFactor.factor charge branch f (pairs ⟨i,hi⟩).1 (pairs ⟨i,hi⟩).2 else 0

def segment {b K : ℕ} (f : ℕ → Coefficients b K) : ℕ → ℕ → List (Coefficients b K)
  | _,0 => []
  | i,n+1 => f i::segment f (i+1) n

structure Ready {V : Type*} [DecidableEq V] {b K : ℕ}
    (bank chargeBase weightBase : ℕ) (charge : Fin b → ℕ)
    (branch : Fin b → V) (f : Finset V → ℝ) (s : State) : Prop where
  dimension : s.natReg 31=(K+1)*2^K*6^b
  one : s.natReg 36=1
  branches : s.natReg 440=b
  charges : s.natReg 444=chargeBase
  weights : s.natReg 445=weightBase
  colors : s.natReg 447=2^K
  degrees : s.natReg 448=6^b
  bankPointer : s.natReg 460=bank
  separation : weightBase+b*b≤bank
  chargeData : ∀ a : Fin b, s.natMem (chargeBase+a.val)=charge a
  weightData : ∀ a c : Fin b, s.realMem (weightBase+a.val*b+c.val)=
    SKFastEvaluator.pairWeight f (branch a) (branch c)

theorem body_nat_frame (params : Parameters) (input : Inputs) {s t : State} {count : ℕ}
    (he : Exec params input body s count t) (r : ℕ)
    (hr : r=31 ∨ r=36 ∨ r=440 ∨ r=444 ∨ r=445 ∨ r=447 ∨ r=448 ∨ r=460 ∨ 461≤r) :
    t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [body,setup,advance,SKDirectFactor.program,SKDirectFactor.test,SKDirectFactor.zero,
    SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,SKDirectIndex.finish,
    IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
    SKRestrictedSingle.program,SKRestrictedSingle.setup,SKRestrictedSingle.finish,
    RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
    code,Program.All,Instruction.natDestination]; omega

theorem body_exec {V : Type*} [DecidableEq V] {b K : ℕ} (hK : 1≤K)
    (params : Parameters) (input : Inputs) (s : State) (bank chargeBase weightBase : ℕ)
    (charge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ) (i : ℕ)
    (hs : Ready (K:=K) bank chargeBase weightBase charge branch f s)
    (hi : i<b*b) (hindex : s.natReg 459=i) :
    ∃ count t, Exec params input body s count t ∧
      count≤30*((K+1)*2^K*6^b)+18*b+136 ∧
      Ready (K:=K) bank chargeBase weightBase charge branch f t ∧ t.natReg 459=i+1 ∧
      Represents (bank+i*((K+1)*2^K*6^b)) (entry (K:=K) charge branch f i) t.realMem ∧
      (∀ address, (∀ j, j<(K+1)*2^K*6^b → address≠bank+i*((K+1)*2^K*6^b)+j) →
        t.realMem address=s.realMem address) := by
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 16 u := exec_code _ _ _ _
  let a := (pairs (⟨i,hi⟩ : Fin (b*b))).1
  let c := (pairs (⟨i,hi⟩ : Fin (b*b))).2
  obtain ⟨d,v,hv,hd,hout,hframe⟩ := SKDirectFactor.program_exec hK params input u
    (bank+i*((K+1)*2^K*6^b)) chargeBase weightBase charge branch f a c
    (by simp [u,setup,runCode,step,hs.branches])
    (by simp [u,setup,runCode,step,hs.branches,hindex,a,pairs])
    (by simp [u,setup,runCode,step,hs.branches,hindex,c,pairs])
    (by simp [u,setup,runCode,step,hs.charges])
    (by simp [u,setup,runCode,step,hs.weights])
    (by simp [u,setup,runCode,step,hs.colors])
    (by simp [u,setup,runCode,step,hs.degrees])
    (by simp [u,setup,runCode,step,hs.dimension,hs.bankPointer,hindex])
    (by simp [u,setup,runCode,step,hs.dimension])
    (by simp [u,setup,runCode,step,hs.one]) hs.chargeData hs.weightData
  have vn := (SKDirectFactor.program_frame params input hv).1
  have vi : v.natReg 459=i := by
    simpa [u,setup,runCode,step,hindex] using vn 459 (by omega) (by omega) (by omega) (by omega)
  have vone : v.natReg 36=1 := by
    simpa [u,setup,runCode,step,hs.one] using vn 36 (by omega) (by omega) (by omega) (by omega)
  let t := runCode params input advance v
  have ht : Exec params input (code advance) v 4 t := exec_code _ _ _ _
  have he : Exec params input body s (16+(d+4)) t := Exec.seq hu (Exec.seq hv ht)
  have tn (r : ℕ) (hr : r=31 ∨ r=36 ∨ r=440 ∨ r=444 ∨ r=445 ∨ r=447 ∨ r=448 ∨ r=460 ∨ 461≤r) :=
    body_nat_frame params input he r hr
  refine ⟨16+(d+4),t,he,by omega,?_,?_,?_,hframe⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hs.separation,?_,?_⟩
    · exact (tn 31 (by omega)).trans hs.dimension
    · exact (tn 36 (by omega)).trans hs.one
    · exact (tn 440 (by omega)).trans hs.branches
    · exact (tn 444 (by omega)).trans hs.charges
    · exact (tn 445 (by omega)).trans hs.weights
    · exact (tn 447 (by omega)).trans hs.colors
    · exact (tn 448 (by omega)).trans hs.degrees
    · exact (tn 460 (by omega)).trans hs.bankPointer
    · intro a
      change v.natMem (chargeBase+a.val)=charge a
      rw [(SKDirectFactor.program_frame params input hv).2.2]
      exact hs.chargeData a
    · intro a c
      change v.realMem (weightBase+a.val*b+c.val)=_
      rw [hframe _ (by
        intro j hj
        have ha := a.isLt; have hc := c.isLt
        have hsep := hs.separation
        have hb : 0<b := by omega
        have hv : a.val*b+c.val<b*b := by nlinarith
        omega)]
      exact hs.weightData a c
  · simp [t,advance,runCode,step,vi,vone]
  · simpa [t,advance,runCode,step,entry,hi,a,c] using hout

theorem repeats_exec {V : Type*} [DecidableEq V] {b K : ℕ} (hK : 1≤K)
    (params : Parameters) (input : Inputs) (bank chargeBase weightBase : ℕ)
    (charge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ)
    (n i : ℕ) (s : State) (hs : Ready (K:=K) bank chargeBase weightBase charge branch f s)
    (hi : i+n≤b*b) (hindex : s.natReg 459=i) :
    ∃ count t, Repeats params input body n s count t ∧
      count≤n*(30*((K+1)*2^K*6^b)+18*b+141)+3 ∧
      Ready (K:=K) bank chargeBase weightBase charge branch f t ∧ t.natReg 459=i+n ∧
      SKRestrictedDirect.Bank (bank+i*((K+1)*2^K*6^b))
        (segment (entry (K:=K) charge branch f) i n) t.realMem ∧
      (∀ address, address<bank+i*((K+1)*2^K*6^b) ∨
        bank+(i+n)*((K+1)*2^K*6^b)≤address → t.realMem address=s.realMem address) := by
  induction n generalizing i s with
  | zero => exact ⟨3,s,Repeats.zero _ _,by simp,hs,by simpa using hindex,True.intro,fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨c,u,hu,hc,us,ui,uhead,um⟩ := body_exec hK params input s bank chargeBase weightBase
      charge branch f i hs (by omega) hindex
    obtain ⟨d,t,ht,hd,ts,ti,ttail,tm⟩ := ih (i+1) u us (by omega) ui
    refine ⟨c+d+5,t,Repeats.succ hu ht,?_,ts,by omega,?_,?_⟩
    · calc
        c+d+5≤(30*((K+1)*2^K*6^b)+18*b+136)+
          (n*(30*((K+1)*2^K*6^b)+18*b+141)+3)+5 := by omega
        _ = (n+1)*(30*((K+1)*2^K*6^b)+18*b+141)+3 := by ring
    · change Represents (bank+i*((K+1)*2^K*6^b)) (entry (K:=K) charge branch f i) t.realMem ∧ _
      constructor
      · intro x
        rw [tm _ (Or.inl (by have hx := encode_lt x; nlinarith))]
        exact uhead x
      · simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using ttail
    · intro address haddress
      have ha : address<bank+(i+1)*((K+1)*2^K*6^b) ∨
          bank+(i+1+n)*((K+1)*2^K*6^b)≤address := by
        rcases haddress with h | h
        · left; rw [Nat.add_mul,Nat.one_mul]; omega
        · right; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      rw [tm address ha]
      apply um address
      intro j hj
      rcases haddress with h | h
      · omega
      · have hend : bank+i*((K+1)*2^K*6^b)+((K+1)*2^K*6^b)≤
            bank+(i+(n+1))*((K+1)*2^K*6^b) := by
          have hii : i+1 ≤ i+(n+1) := by omega
          have hh := Nat.mul_le_mul_right ((K+1)*2^K*6^b) hii
          have heq : (i+1)*((K+1)*2^K*6^b)=i*((K+1)*2^K*6^b)+((K+1)*2^K*6^b) := by ring
          rw [heq] at hh
          omega
        omega

theorem program_exec {V : Type*} [DecidableEq V] {b K : ℕ} (hK : 1≤K)
    (params : Parameters) (input : Inputs) (s : State) (bank chargeBase weightBase : ℕ)
    (charge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ)
    (hs : Ready (K:=K) bank chargeBase weightBase charge branch f s) :
    ∃ count t, Exec params input program s count t ∧
      count≤b*b*(30*((K+1)*2^K*6^b)+18*b+141)+10 ∧
      Ready (K:=K) bank chargeBase weightBase charge branch f t ∧
      SKRestrictedDirect.Bank bank (segment (entry (K:=K) charge branch f) 0 (b*b)) t.realMem ∧
      (∀ address, address<bank ∨ bank+b*b*((K+1)*2^K*6^b)≤address →
        t.realMem address=s.realMem address) := by
  let u := runCode params input initCode s
  have hu : Exec params input (code initCode) s 5 u := exec_code _ _ _ _
  have us : Ready (K:=K) bank chargeBase weightBase charge branch f u := by
    rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
    exact ⟨by simpa [u,initCode,runCode,step] using h1,
      by simpa [u,initCode,runCode,step] using h2,
      by simpa [u,initCode,runCode,step] using h3,
      by simpa [u,initCode,runCode,step] using h4,
      by simpa [u,initCode,runCode,step] using h5,
      by simpa [u,initCode,runCode,step] using h6,
      by simpa [u,initCode,runCode,step] using h7,
      by simpa [u,initCode,runCode,step] using h8,h9,h10,h11⟩
  obtain ⟨c,t,ht,hc,ts,_,tb,tm⟩ := repeats_exec hK params input bank chargeBase weightBase
    charge branch f (b*b) 0 u us (by omega) (by simp [u,initCode,runCode,step])
  have ul : u.natReg 461=b*b := by simp [u,initCode,runCode,step,hs.branches]
  refine ⟨5+(c+2),t,Exec.seq hu (Exec.repeat (by rwa [ul])),by omega,ts,?_,?_⟩
  · simpa using tb
  · simpa [u,initCode,runCode,step] using tm

end Manuscript.SKDirectBank
