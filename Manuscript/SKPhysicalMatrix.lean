import Manuscript.SKPhysicalPair

noncomputable section
namespace Manuscript.SKPhysicalMatrix
open RestrictedMachine

/-- Registers420/421 are row/column label bases,422/423 their lengths,
424 is the result base. All are runtime values. -/
def initCode : List Instruction := [.nmul 425 422 423,.nconst 426 0,.nconst 427 1]
def preludeCode : List Instruction :=
  [.ndiv 428 426 423,.nadd 428 428 420,.loadNat 390 428,
   .nmod 429 426 423,.nadd 429 429 421,.loadNat 391 429]
def tailCode : List Instruction := [.nadd 430 424 426,.storeReal 430 390,.nadd 426 426 427]
def body : Program := .seq (code preludeCode) (.seq SKPhysicalPair.program (code tailCode))
def program : Program := .seq (code initCode) (.repeat 425 body)

def pairValue (s : State) (u v : ℕ) : ℝ :=
  SKPhysicalPair.value (writeNatReg (writeNatReg s 390 u) 391 v)
def entry (s : State) (n : ℕ) : ℝ :=
  pairValue s (s.natMem (s.natReg 420+n/s.natReg 423))
    (s.natMem (s.natReg 421+n%s.natReg 423))
def cost (s : State) := 18*s.natReg 500+34*s.natReg 501+91

def Fixed (s t : State) : Prop :=
  ∀r,((420≤r ∧ r≤424) ∨ 500≤r) → t.natReg r=s.natReg r
structure Invariant (s : State) (n : ℕ) (t : State) : Prop where
  fixed : Fixed s t
  counter : t.natReg 426=n
  one : t.natReg 427=1
  bound : t.natReg 425=s.natReg 422*s.natReg 423
  natMem : t.natMem=s.natMem
  mean : t.realReg 504=s.realReg 504
  computed : ∀i,i<n → t.realMem (s.natReg 424+i)=entry s i
  frame : ∀a,(a<s.natReg 424 ∨ s.natReg 424+n≤a) → t.realMem a=s.realMem a

theorem value_congr (a s : State) (u v : ℕ)
    (hu : a.natReg 390=u) (hv : a.natReg 391=v)
    (hn : a.natReg 500=s.natReg 500) (hm : a.natReg 501=s.natReg 501)
    (hmem : a.natMem=s.natMem) (hmean : a.realReg 504=s.realReg 504)
    (hw : ∀i,i<s.natReg 501 → a.realMem (2*i)=s.realMem (2*i)) :
    SKPhysicalPair.value a=pairValue s u v := by
  simp only [SKPhysicalPair.value,hu,hv,hn,hm,hmem,hmean]
  simp [pairValue,SKPhysicalPair.value,writeNatReg]
  split_ifs <;> first | rfl | skip
  apply Finset.sum_congr rfl
  intro i hi
  rw [hw i (Finset.mem_range.mp hi)]

theorem body_execution (params : Parameters) (input : Inputs) (s t : State) (n : ℕ)
    (hi : Invariant s n t) (hn : n<s.natReg 422*s.natReg 423)
    (hfit : 2*s.natReg 501≤s.natReg 424)
    (hrow : ∀i,i<s.natReg 422 → s.natMem (s.natReg 420+i)≤s.natReg 500)
    (hcol : ∀i,i<s.natReg 423 → s.natMem (s.natReg 421+i)≤s.natReg 500) :
    ∃c u,Exec params input body t c u ∧ c≤cost s ∧ Invariant s (n+1) u := by
  have hpos : 0<s.natReg 423 := by nlinarith
  have hnrow : n/s.natReg 423<s.natReg 422 := by
    exact (Nat.div_lt_iff_lt_mul hpos).mpr (by simpa [Nat.mul_comm] using hn)
  have hncol : n%s.natReg 423<s.natReg 423 := Nat.mod_lt n hpos
  let a := runCode params input preludeCode t
  have af (r : ℕ) (hr : r≠428 ∧ r≠429 ∧ r≠390 ∧ r≠391) : a.natReg r=t.natReg r := by
    simp [a,preludeCode,runCode,step,hr.1,hr.2.1,hr.2.2.1,hr.2.2.2]
  have au : a.natReg 390=s.natMem (s.natReg 420+n/s.natReg 423) := by
    simp [a,preludeCode,runCode,step,hi.natMem,hi.counter,hi.fixed 420 (by omega),hi.fixed 423 (by omega),Nat.add_comm]
  have av : a.natReg 391=s.natMem (s.natReg 421+n%s.natReg 423) := by
    simp [a,preludeCode,runCode,step,hi.natMem,hi.counter,hi.fixed 421 (by omega),hi.fixed 423 (by omega),Nat.add_comm]
  have an : a.natReg 500=s.natReg 500 := (af 500 (by omega)).trans (hi.fixed 500 (by omega))
  have am : a.natReg 501=s.natReg 501 := (af 501 (by omega)).trans (hi.fixed 501 (by omega))
  obtain ⟨cp,p,hp,bp,hpv,hpm,hpn⟩ := SKPhysicalPair.execution params input a
    (by rw [au,an]; exact hrow _ hnrow) (by rw [av,an]; exact hcol _ hncol)
  have pv : p.realReg 390=entry s n := by
    rw [hpv]
    apply value_congr a s _ _ au av an am
    · simpa [a,preludeCode,runCode,step] using hi.natMem
    · simpa [a,preludeCode,runCode,step] using hi.mean
    · intro i hilen
      have haway : 2*i<s.natReg 424 := by omega
      simpa [a,preludeCode,runCode,step] using hi.frame (2*i) (Or.inl haway)
  have pf (r : ℕ) (hr : 396≤r) : p.natReg r=a.natReg r :=
    SKPhysicalPair.natReg_frame params input a p cp r hp hr
  have p426 : p.natReg 426=n := by rw [pf 426 (by omega),af 426 (by omega),hi.counter]
  have p427 : p.natReg 427=1 := by rw [pf 427 (by omega),af 427 (by omega),hi.one]
  have p424 : p.natReg 424=s.natReg 424 := by rw [pf 424 (by omega),af 424 (by omega),hi.fixed 424 (by omega)]
  let u := runCode params input tailCode p
  have um : u.realMem=Function.update t.realMem (s.natReg 424+n) (entry s n) := by
    simp [u,tailCode,runCode,step,writeRealMem,p426,p424,pv,hpm,a,preludeCode,writeRealMem]
  refine ⟨22+(cp+11),u,?_,?_,?_⟩
  · exact Exec.seq (exec_code params input preludeCode t)
      (Exec.seq hp (exec_code params input tailCode p))
  · rw [an,am] at bp
    simp only [cost]; omega
  · constructor
    · intro r hr
      have hn426 : r≠426 := by omega
      have hn430 : r≠430 := by omega
      simp [u,tailCode,runCode,step,writeRealMem,hn426,hn430,pf r (by omega),af r (by omega),hi.fixed r hr]
    · simp [u,tailCode,runCode,step,writeRealMem,p426,p427]
    · simp [u,tailCode,runCode,step,writeRealMem,p427]
    · simp [u,tailCode,runCode,step,writeRealMem,pf 425 (by omega),af 425 (by omega),hi.bound]
    · simpa [u,tailCode,runCode,step,writeRealMem,hpn,a,preludeCode] using hi.natMem
    · have hm := SKPhysicalPair.realReg_frame params input a p cp 504 hp (by omega)
      simpa [u,tailCode,runCode,step,writeRealMem,hm,a,preludeCode] using hi.mean
    · intro i hil
      rw [um]
      by_cases hi' : i=n
      · subst i; simp
      · rw [Function.update_of_ne (by omega : s.natReg 424+i≠s.natReg 424+n)]
        exact hi.computed i (by omega)
    · intro address haway
      rw [um,Function.update_of_ne (by omega : address≠s.natReg 424+n)]
      apply hi.frame address
      omega

theorem loop_execution (params : Parameters) (input : Inputs) (s t : State) (n m : ℕ)
    (hi : Invariant s n t) (hn : n+m≤s.natReg 422*s.natReg 423)
    (hfit : 2*s.natReg 501≤s.natReg 424)
    (hrow : ∀i,i<s.natReg 422 → s.natMem (s.natReg 420+i)≤s.natReg 500)
    (hcol : ∀i,i<s.natReg 423 → s.natMem (s.natReg 421+i)≤s.natReg 500) :
    ∃c u,Repeats params input body m t c u ∧ c≤m*(cost s+5)+3 ∧ Invariant s (n+m) u := by
  induction m generalizing n t with
  | zero => exact ⟨3,t,Repeats.zero body t,by simp,by simpa using hi⟩
  | succ m ih =>
    obtain ⟨cb,b,hb,bb,hib⟩ := body_execution params input s t n hi (by omega) hfit hrow hcol
    obtain ⟨cu,u,hu,bu,hiu⟩ := ih b (n+1) hib (by omega)
    refine ⟨cb+cu+5,u,Repeats.succ hb hu,?_,?_⟩
    · calc
        cb+cu+5≤cost s+(m*(cost s+5)+3)+5 := by omega
        _=(m+1)*(cost s+5)+3 := by ring
    · convert hiu using 1; omega

theorem execution (params : Parameters) (input : Inputs) (s : State)
    (hfit : 2*s.natReg 501≤s.natReg 424)
    (hrow : ∀i,i<s.natReg 422 → s.natMem (s.natReg 420+i)≤s.natReg 500)
    (hcol : ∀i,i<s.natReg 423 → s.natMem (s.natReg 421+i)≤s.natReg 500) :
    ∃c u,Exec params input program s c u ∧
      c≤s.natReg 422*s.natReg 423*(cost s+5)+11 ∧
      Invariant s (s.natReg 422*s.natReg 423) u := by
  let a := runCode params input initCode s
  have ha : Invariant s 0 a := by
    constructor
    · intro r hr
      have h425 : r≠425 := by omega
      have h426 : r≠426 := by omega
      have h427 : r≠427 := by omega
      simp [a,initCode,runCode,step,h425,h426,h427]
    · simp [a,initCode,runCode,step]
    · simp [a,initCode,runCode,step]
    · simp [a,initCode,runCode,step]
    · simp [a,initCode,runCode,step]
    · simp [a,initCode,runCode,step]
    · intro i hi; omega
    · intro address _; simp [a,initCode,runCode,step]
  obtain ⟨cl,u,hl,bl,hi⟩ := loop_execution params input s a 0
    (s.natReg 422*s.natReg 423) ha (by omega) hfit hrow hcol
  refine ⟨6+(cl+2),u,?_,by omega,by simpa using hi⟩
  exact Exec.seq (exec_code params input initCode s) (Exec.repeat (by simpa [a,initCode,runCode,step] using hl))

end Manuscript.SKPhysicalMatrix
