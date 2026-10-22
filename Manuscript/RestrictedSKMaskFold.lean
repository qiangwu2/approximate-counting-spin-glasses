import Manuscript.RestrictedSKTrials

noncomputable section
namespace Manuscript.RestrictedSKMaskFold
open RestrictedMachine

def prefixCode : List Instruction := [.nadd 580 576 575,.loadNat 520 580]
def suffixCode : List Instruction := [.radd 572 572 570,.nadd 575 575 579]
def body (candidate : Program) : Program := .seq (code prefixCode)
  (.seq (RestrictedSKTrials.program candidate) (code suffixCode))
def program (candidate : Program) : Program := .repeat 577 (body candidate)

structure Stable (P : State→Prop) : Prop where
  trials : RestrictedSKTrials.Stable P
  nat : ∀ s,P s → ∀ r v,r=520 ∨ r=575 ∨ r=580 → P (writeNatReg s r v)
  real : ∀ s,P s → ∀ v,P (writeRealReg s 572 v)

def value (f : ℕ→ℕ→ℝ) (R : ℕ) (masks : ℕ→ℕ) : ℕ→ℕ→ℝ
  | 0,_ => 0
  | n+1,i => RestrictedSKTrials.sum f (masks i) R 0/(R:ℝ)+value f R masks n (i+1)
def cost (bound : ℕ→ℕ) (R : ℕ) (masks : ℕ→ℕ) : ℕ→ℕ→ℕ
  | 0,_ => 0
  | n+1,i => R*(bound (masks i)+29)+35+cost bound R masks n (i+1)

theorem body_exec (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s → RestrictedSKTrials.Prepared s → ∃ count t,Exec params input candidate s count t ∧
      RestrictedSKTrials.CandidateResult P f bound s t count)
    (s : State) (hs : P s) (h1 : s.natReg 579=1)
    (hmask : s.natMem (s.natReg 576+s.natReg 575)<2^s.natReg 500) :
    ∃ count t,Exec params input (body candidate) s count t ∧ P t ∧
      count≤s.natReg 513*(bound (s.natMem (s.natReg 576+s.natReg 575))+29)+30 ∧
      t.realReg 572=s.realReg 572+RestrictedSKTrials.sum f
        (s.natMem (s.natReg 576+s.natReg 575)) (s.natReg 513) 0/(s.natReg 513:ℝ) ∧
      t.natReg 575=s.natReg 575+1 ∧
      (∀ r,((500≤r ∧ r<540 ∧ r≠520 ∧ r≠521 ∧ r≠522) ∨
        (570≤r ∧ r≠571 ∧ r≠575 ∧ r≠580)) → t.natReg r=s.natReg r) ∧
      (∀ r,573≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 530 → t.natMem j=s.natMem j) := by
  let ready := runCode params input prefixCode s
  have hready : P ready := stable.nat _ (stable.nat _ hs _ _ (by simp)) _ _ (by simp)
  obtain ⟨c,a,ha,hpa,hc,hv,hn,hr,hm⟩ := RestrictedSKTrials.program_exec params input candidate
    P stable.trials f bound realized ready hready
    (by simpa [ready,prefixCode,runCode,step] using hmask)
  let t := runCode params input suffixCode a
  refine ⟨7+(c+8),t,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh:=Exec.seq (exec_code params input prefixCode s) (Exec.seq ha (exec_code params input suffixCode a))
    simpa [body,prefixCode,suffixCode,codeCost,instrCost,t,ready] using hh
  · exact stable.nat _ (stable.real _ hpa _) _ _ (by simp)
  · have hc' : c≤s.natReg 513*(bound (s.natMem (s.natReg 576+s.natReg 575))+29)+15 := by
      simpa [ready,prefixCode,runCode,step] using hc
    omega
  · simp [t,suffixCode,runCode,step,hv,hr,ready,prefixCode]
  · simp [t,suffixCode,runCode,step,hn,ready,prefixCode,h1]
  · intro r h
    simp [t,suffixCode,runCode,step,show r≠575 by omega,hn r (by omega),
      ready,prefixCode,show r≠520 by omega,show r≠580 by omega]
  · intro r h
    simp [t,suffixCode,runCode,step,show r≠572 by omega,hr r (by omega),ready,prefixCode]
  · intro j hj
    have hh:=hm j (by simpa [ready,prefixCode,runCode,step] using hj)
    simpa [t,suffixCode,runCode,step,ready,prefixCode] using hh

theorem repeats (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s → RestrictedSKTrials.Prepared s → ∃ count t,Exec params input candidate s count t ∧
      RestrictedSKTrials.CandidateResult P f bound s t count)
    (masks : ℕ→ℕ) (limit n : ℕ) :
    ∀ s : State,P s → s.natReg 579=1 → s.natReg 575+n≤limit →
      s.natReg 576+limit≤s.natReg 530 →
      (∀ j,j<limit → s.natMem (s.natReg 576+j)=masks j) →
      (∀ j,j<limit → masks j<2^s.natReg 500) →
    ∃ count t,Repeats params input (body candidate) n s count t ∧ P t ∧
      count≤cost bound (s.natReg 513) masks n (s.natReg 575)+3 ∧
      t.realReg 572=s.realReg 572+value f (s.natReg 513) masks n (s.natReg 575) ∧
      (∀ r,((500≤r ∧ r<540 ∧ r≠520 ∧ r≠521 ∧ r≠522) ∨
        (570≤r ∧ r≠571 ∧ r≠575 ∧ r≠580)) → t.natReg r=s.natReg r) ∧
      (∀ r,573≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 530 → t.natMem j=s.natMem j) := by
  induction n with
  | zero =>
      intro s hs h1 hlim hsep hread hvalid
      refine ⟨3,s,Repeats.zero _ _,hs,?_,?_,by intros;rfl,by intros;rfl,by intros;rfl⟩
      · simp [cost]
      · simp [value]
  | succ n ih =>
      intro s hs h1 hlim hsep hread hvalid
      obtain ⟨c,a,ha,hpa,hc,hv,hi,hn,hr,hm⟩ := body_exec params input candidate P stable f bound realized s hs h1
        (by rw [hread _ (by omega)];exact hvalid _ (by omega))
      have hr' : ∀ j,j<limit → a.natMem (a.natReg 576+j)=masks j := by
        intro j hj
        rw [hn 576 (by omega),hm _ (by omega)]
        exact hread j hj
      obtain ⟨d,t,ht,hpt,hd,hvt,hnt,hrt,hmt⟩ := ih a hpa
        (by rw [hn 579 (by omega)];exact h1) (by rw [hi];omega)
        (by rw [hn 576 (by omega),hn 530 (by omega)];exact hsep) hr'
        (by intro j hj;rw [hn 500 (by omega)];exact hvalid j hj)
      have hreadi:=hread (s.natReg 575) (by omega)
      refine ⟨c+d+5,t,Repeats.succ ha ht,hpt,?_,?_,?_,?_,?_⟩
      · rw [hn 513 (by omega),hi] at hd
        rw [hreadi] at hc
        simp only [cost]
        omega
      · rw [hvt,hv,hn 513 (by omega),hi,hreadi,value]
        ring
      · intro r h
        exact (hnt r h).trans (hn r h)
      · intro r h
        exact (hrt r h).trans (hr r h)
      · intro j hj
        exact (hmt j (by rw [hn 530 (by omega)];exact hj)).trans (hm j hj)

theorem program_exec (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s → RestrictedSKTrials.Prepared s → ∃ count t,Exec params input candidate s count t ∧
      RestrictedSKTrials.CandidateResult P f bound s t count)
    (masks : ℕ→ℕ) (s : State) (hs : P s) (h1 : s.natReg 579=1) (hi : s.natReg 575=0)
    (hsep : s.natReg 576+s.natReg 577≤s.natReg 530)
    (hread : ∀ j,j<s.natReg 577 → s.natMem (s.natReg 576+j)=masks j)
    (hvalid : ∀ j,j<s.natReg 577 → masks j<2^s.natReg 500) :
    ∃ count t,Exec params input (program candidate) s count t ∧ P t ∧
      count≤cost bound (s.natReg 513) masks (s.natReg 577) 0+5 ∧
      t.realReg 572=s.realReg 572+value f (s.natReg 513) masks (s.natReg 577) 0 ∧
      (∀ r,((500≤r ∧ r<540 ∧ r≠520 ∧ r≠521 ∧ r≠522) ∨
        (570≤r ∧ r≠571 ∧ r≠575 ∧ r≠580)) → t.natReg r=s.natReg r) ∧
      (∀ r,573≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 530 → t.natMem j=s.natMem j) := by
  obtain ⟨c,t,he,hp,hc,hv,hn,hr,hm⟩ := repeats params input candidate P stable f bound realized masks
    (s.natReg 577) (s.natReg 577) s hs h1 (by omega) hsep hread hvalid
  refine ⟨c+2,t,Exec.repeat he,hp,?_,?_,hn,hr,hm⟩
  · rw [hi] at hc
    omega
  · simpa [hi] using hv

end Manuscript.RestrictedSKMaskFold
