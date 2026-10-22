import Manuscript.RestrictedSKLayer

noncomputable section
namespace Manuscript.RestrictedSKOuter
open RestrictedMachine

def initCode : List Instruction := [.rconst 572 0,.nconst 579 1,.nadd 573 510 579,.nconst 574 0]
def suffixCode : List Instruction := [.nconst 579 1,.nadd 574 574 579]
def body (candidate : Program) : RestrictedRecursiveMachine.Program 1 :=
  .seq (RestrictedSKLayer.program candidate) (.base (code suffixCode))
def program (candidate : Program) : RestrictedRecursiveMachine.Program 1 :=
  .seq (.base (code initCode)) (.repeat 573 (body candidate))

def value (f : ℕ→ℕ→ℝ) (N R : ℕ) : ℕ→ℕ→ℝ
  | 0,_ => 0
  | n+1,b => RestrictedSKMaskFold.value f R (fun j=>(RestrictedSubsets.masks N b 0 1)[j]!)
      (N.choose b) 0+value f N R n (b+1)
def cost (bound : ℕ→ℕ) (N R : ℕ) : ℕ→ℕ→ℕ
  | 0,_ => 0
  | n+1,b => RestrictedSubsets.work N b+
      RestrictedSKMaskFold.cost bound R (fun j=>(RestrictedSubsets.masks N b 0 1)[j]!)
        (N.choose b) 0+66+cost bound N R n (b+1)

theorem body_exec (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : RestrictedSKLayer.Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s ∧ RestrictedSKLayer.SafeLayout s →
      RestrictedSKTrials.Prepared s → ∃ count t,Exec params input candidate s count t ∧
        RestrictedSKTrials.CandidateResult (fun s=>P s ∧ RestrictedSKLayer.SafeLayout s) f bound s t count)
    (s : State) (hs : P s) (hbase : s.natReg 501≤s.natReg 576) :
    ∃ count t,RestrictedRecursiveMachine.Exec RestrictedSubsets.table params input (body candidate) s count t ∧ P t ∧
      count≤RestrictedSubsets.work (s.natReg 500) (s.natReg 574)+
        RestrictedSKMaskFold.cost bound (s.natReg 513)
          (fun j=>(RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1)[j]!)
          ((s.natReg 500).choose (s.natReg 574)) 0+61 ∧
      t.realReg 572=s.realReg 572+RestrictedSKMaskFold.value f (s.natReg 513)
          (fun j=>(RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1)[j]!)
          ((s.natReg 500).choose (s.natReg 574)) 0 ∧
      t.natReg 574=s.natReg 574+1 ∧
      (∀ r,580<r ∨ r=500 ∨ r=501 ∨ r=510 ∨ r=512 ∨ r=513 ∨ r=570 ∨ r=573 ∨ r=576 →
        t.natReg r=s.natReg r) ∧
      (∀ r,573≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 576 → t.natMem j=s.natMem j) := by
  obtain ⟨c,a,ha,hpa,hc,hv,hn,hr,hm⟩ := RestrictedSKLayer.program_exec params input candidate P stable f bound realized s hs hbase
  let t:=runCode params input suffixCode a
  refine ⟨c+5,t,?_,?_,by omega,?_,?_,?_,?_,?_⟩
  · simpa [body,suffixCode,codeCost,instrCost,t] using
      RestrictedRecursiveMachine.Exec.seq ha (RestrictedRecursiveMachine.Exec.base (exec_code params input suffixCode a))
  · exact stable.nat _ (stable.nat _ hpa _ _ (by omega)) _ _ (by omega)
  · simpa [t,suffixCode,runCode,step] using hv
  · simp [t,suffixCode,runCode,step,hn]
  · intro r h
    simp [t,suffixCode,runCode,step,show r≠574 by omega,show r≠579 by omega,hn r (by omega)]
  · intro r h
    simpa [t,suffixCode,runCode,step] using hr r h
  · intro j hj
    simpa [t,suffixCode,runCode,step] using hm j hj

theorem repeats (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : RestrictedSKLayer.Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s ∧ RestrictedSKLayer.SafeLayout s →
      RestrictedSKTrials.Prepared s → ∃ count t,Exec params input candidate s count t ∧
        RestrictedSKTrials.CandidateResult (fun s=>P s ∧ RestrictedSKLayer.SafeLayout s) f bound s t count)
    (n : ℕ) : ∀ s : State,P s → s.natReg 501≤s.natReg 576 →
    ∃ count t,RestrictedRecursiveMachine.Repeats RestrictedSubsets.table params input (body candidate) n s count t ∧ P t ∧
      count≤cost bound (s.natReg 500) (s.natReg 513) n (s.natReg 574)+3 ∧
      t.realReg 572=s.realReg 572+value f (s.natReg 500) (s.natReg 513) n (s.natReg 574) ∧
      (∀ r,580<r ∨ r=500 ∨ r=501 ∨ r=510 ∨ r=512 ∨ r=513 ∨ r=570 ∨ r=573 ∨ r=576 →
        t.natReg r=s.natReg r) ∧
      (∀ r,573≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 576 → t.natMem j=s.natMem j) := by
  induction n with
  | zero =>
      intro s hs hbase
      refine ⟨3,s,RestrictedRecursiveMachine.Repeats.zero _ _,hs,?_,?_,by intros;rfl,by intros;rfl,by intros;rfl⟩
      · simp [cost]
      · simp [value]
  | succ n ih =>
      intro s hs hbase
      obtain ⟨c,a,ha,hpa,hc,hv,hi,hn,hr,hm⟩ := body_exec params input candidate P stable f bound realized s hs hbase
      obtain ⟨d,t,ht,hpt,hd,hvt,hnt,hrt,hmt⟩ := ih a hpa (by rw [hn 501 (by simp),hn 576 (by simp)];exact hbase)
      refine ⟨c+d+5,t,RestrictedRecursiveMachine.Repeats.succ ha ht,hpt,?_,?_,?_,?_,?_⟩
      · rw [hn 500 (by simp),hn 513 (by simp),hi] at hd
        simp only [cost]
        omega
      · rw [hvt,hv,hn 500 (by simp),hn 513 (by simp),hi,value]
        ring
      · intro r h
        exact (hnt r h).trans (hn r h)
      · intro r h
        exact (hrt r h).trans (hr r h)
      · intro j hj
        exact (hmt j (by rw [hn 576 (by simp)];exact hj)).trans (hm j hj)

/-- Output-sensitive, uniform truncated estimator execution. The only modular
premise is a proved realization of the concrete candidate program; no evaluator
or cost function occurs as an instruction in the program. -/
theorem program_exec (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : RestrictedSKLayer.Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s ∧ RestrictedSKLayer.SafeLayout s →
      RestrictedSKTrials.Prepared s → ∃ count t,Exec params input candidate s count t ∧
        RestrictedSKTrials.CandidateResult (fun s=>P s ∧ RestrictedSKLayer.SafeLayout s) f bound s t count)
    (s : State) (hs : P s) (hbase : s.natReg 501≤s.natReg 576) :
    ∃ count t,RestrictedRecursiveMachine.Exec RestrictedSubsets.table params input (program candidate) s count t ∧ P t ∧
      count≤cost bound (s.natReg 500) (s.natReg 513) (s.natReg 510+1) 0+12 ∧
      t.realReg 572=value f (s.natReg 500) (s.natReg 513) (s.natReg 510+1) 0 ∧
      (∀ r,580<r ∨ r=500 ∨ r=501 ∨ r=510 ∨ r=512 ∨ r=513 ∨ r=570 ∨ r=576 →
        t.natReg r=s.natReg r) ∧
      (∀ r,573≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 576 → t.natMem j=s.natMem j) := by
  let ready:=runCode params input initCode s
  have hready : P ready := stable.nat _ (stable.nat _ (stable.nat _ (stable.real _ hs _ _ (by omega)) _ _ (by omega)) _ _ (by omega)) _ _ (by omega)
  obtain ⟨c,t,he,hp,hc,hv,hn,hr,hm⟩ := repeats params input candidate P stable f bound realized
    (ready.natReg 573) ready hready (by simpa [ready,initCode,runCode,step] using hbase)
  refine ⟨7+(c+2),t,?_,hp,?_,?_,?_,?_,?_⟩
  · simpa [program,initCode,codeCost,instrCost,ready] using
      RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base (exec_code params input initCode s))
        (RestrictedRecursiveMachine.Exec.repeat he)
  · have hh : c≤cost bound (s.natReg 500) (s.natReg 513) (s.natReg 510+1) 0+3 := by
      simpa [ready,initCode,runCode,step] using hc
    omega
  · simpa [ready,initCode,runCode,step] using hv
  · intro r h
    have hh:=hn r (by omega)
    simpa [ready,initCode,runCode,step,show r≠573 by omega,show r≠574 by omega,show r≠579 by omega] using hh
  · intro r h
    have hh:=hr r h
    simpa [ready,initCode,runCode,step,show r≠572 by omega] using hh
  · intro j hj
    have hh:=hm j (by simpa [ready,initCode,runCode,step] using hj)
    simpa [ready,initCode,runCode,step] using hh

end Manuscript.RestrictedSKOuter
