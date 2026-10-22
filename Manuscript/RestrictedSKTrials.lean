import Manuscript.RestrictedCandidateLabelPreparation

noncomputable section
namespace Manuscript.RestrictedSKTrials
open RestrictedMachine

/-- The random tape contains a block of N colors per (mask,trial) pair. -/
def prefixCode : List Instruction :=
  [.nmul 522 520 513,.nadd 522 522 521,.nmul 522 522 500,.nadd 522 522 570]
def suffixCode : List Instruction := [.radd 570 570 310,.nadd 521 521 571]
def initCode : List Instruction := [.rconst 570 0,.nconst 521 0,.nconst 571 1]
def finishCode : List Instruction := [.natToReal 571 513,.rdiv 570 570 571]
def body (candidate : Program) : Program := .seq (code prefixCode) (.seq candidate (code suffixCode))
def program (candidate : Program) : Program := .seq (code initCode)
  (.seq (.repeat 513 (body candidate)) (code finishCode))

/-- Stable physical-cache assertions may mention raw model data, saved globals,
and array addresses. These are the only register updates made by this wrapper. -/
structure Stable (P : State→Prop) : Prop where
  nat : ∀ s,P s → ∀ r v,r=521 ∨ r=522 ∨ r=571 → P (writeNatReg s r v)
  real : ∀ s,P s → ∀ r v,r=570 ∨ r=571 → P (writeRealReg s r v)

def sum (f : ℕ→ℕ→ℝ) (mask : ℕ) : ℕ→ℕ→ℝ
  | 0,_ => 0
  | n+1,j => f mask j+sum f mask n (j+1)

/-- Only actually reached trial calls require candidate correctness. -/
def Prepared (s : State) : Prop :=
  s.natReg 520<2^s.natReg 500 ∧ s.natReg 521<s.natReg 513 ∧
  s.natReg 522=s.natReg 570+(s.natReg 520*s.natReg 513+s.natReg 521)*s.natReg 500

structure CandidateResult (P : State→Prop) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (s t : State) (count : ℕ) : Prop where
  invariant : P t
  value : t.realReg 310=f (s.natReg 520) (s.natReg 521)
  cost : count≤bound (s.natReg 520)
  nat : ∀ r,(500≤r ∧ r<540) ∨ 570≤r → t.natReg r=s.natReg r
  real : ∀ r,570≤r → t.realReg r=s.realReg r
  memory : ∀ j,j<s.natReg 530 → t.natMem j=s.natMem j

theorem prefix_stable {P : State→Prop} (stable : Stable P) (params : Parameters) (input : Inputs)
    (s : State) (hs : P s) : P (runCode params input prefixCode s) := by
  apply stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _ hs _ _ (by simp)) _ _ (by simp)) _ _ (by simp)) _ _ (by simp)

theorem suffix_stable {P : State→Prop} (stable : Stable P) (params : Parameters) (input : Inputs)
    (s : State) (hs : P s) : P (runCode params input suffixCode s) := by
  exact stable.nat _ (stable.real _ hs _ _ (by simp)) _ _ (by simp)

theorem body_exec (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s → Prepared s → ∃ count t,Exec params input candidate s count t ∧ CandidateResult P f bound s t count)
    (s : State) (hs : P s) (h1 : s.natReg 571=1)
    (hmask : s.natReg 520<2^s.natReg 500) (htrial : s.natReg 521<s.natReg 513) :
    ∃ count t,Exec params input (body candidate) s count t ∧ P t ∧
      count≤bound (s.natReg 520)+24 ∧ t.realReg 570=s.realReg 570+f (s.natReg 520) (s.natReg 521) ∧
      t.natReg 521=s.natReg 521+1 ∧
      (∀ r,((500≤r ∧ r<540 ∧ r≠521 ∧ r≠522) ∨ 570≤r) → t.natReg r=s.natReg r) ∧
      (∀ r,571≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 530 → t.natMem j=s.natMem j) := by
  let ready := runCode params input prefixCode s
  obtain ⟨c,a,ha,ar⟩ := realized ready (prefix_stable stable params input s hs)
    (by simp [Prepared,ready,prefixCode,runCode,step,hmask,htrial,Nat.add_comm])
  let t := runCode params input suffixCode a
  have an (r : ℕ) (hr : (500≤r ∧ r<540) ∨ 570≤r) : a.natReg r=ready.natReg r := ar.nat r hr
  have av (r : ℕ) (hr : 570≤r) : a.realReg r=s.realReg r := by
    simpa [ready,prefixCode,runCode,step] using ar.real r hr
  refine ⟨16+(c+8),t,?_,suffix_stable stable params input a ar.invariant,?_,?_,?_,?_,?_,?_⟩
  · have hh := Exec.seq (exec_code params input prefixCode s) (Exec.seq ha (exec_code params input suffixCode a))
    simpa [body,prefixCode,suffixCode,codeCost,instrCost,t,ready] using hh
  · have hc:=ar.cost
    simpa [ready,prefixCode,runCode,step] using (show 16+(c+8)≤bound (ready.natReg 520)+24 by omega)
  · simp [t,suffixCode,runCode,step,ar.value,av,ready,prefixCode]
  · simp [t,suffixCode,runCode,step,an,ready,prefixCode,h1]
  · intro r hr
    simp [t,suffixCode,runCode,step,show r≠521 by omega,an r (by omega),
      ready,prefixCode,show r≠522 by omega]
  · intro r hr
    simp [t,suffixCode,runCode,step,show r≠570 by omega,av r (by omega)]
  · intro j hj
    have hh:=ar.memory j (by simpa [ready,prefixCode,runCode,step] using hj)
    simpa [t,suffixCode,runCode,step,ready,prefixCode] using hh

theorem repeats (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s → Prepared s → ∃ count t,Exec params input candidate s count t ∧ CandidateResult P f bound s t count)
    (n : ℕ) : ∀ s : State,P s → s.natReg 571=1 →
    s.natReg 520<2^s.natReg 500 → s.natReg 521+n≤s.natReg 513 →
    ∃ count t,Repeats params input (body candidate) n s count t ∧ P t ∧
      count≤n*(bound (s.natReg 520)+29)+3 ∧
      t.realReg 570=s.realReg 570+sum f (s.natReg 520) n (s.natReg 521) ∧
      (∀ r,((500≤r ∧ r<540 ∧ r≠521 ∧ r≠522) ∨ 570≤r) → t.natReg r=s.natReg r) ∧
      (∀ r,571≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 530 → t.natMem j=s.natMem j) := by
  induction n with
  | zero =>
      intro s hs h1 hmask hlim
      refine ⟨3,s,Repeats.zero _ _,hs,?_,?_,by intros;rfl,by intros;rfl,by intros;rfl⟩
      · simp
      · simp [sum]
  | succ n ih =>
      intro s hs h1 hmask hlim
      obtain ⟨c,a,ha,hpa,hc,hv,hi,hn,hr,hm⟩ := body_exec params input candidate P stable f bound realized s hs h1 hmask (by omega)
      obtain ⟨d,t,ht,hpt,hd,hvt,hnt,hrt,hmt⟩ := ih a hpa (by rw [hn 571 (by omega)];exact h1)
        (by rw [hn 520 (by omega),hn 500 (by omega)];exact hmask)
        (by rw [hi,hn 513 (by omega)];omega)
      refine ⟨c+d+5,t,Repeats.succ ha ht,hpt,?_,?_,?_,?_,?_⟩
      · rw [hn 520 (by omega)] at hd
        nlinarith
      · rw [hvt,hv,hi,hn 520 (by omega),sum]
        ring
      · intro r h
        exact (hnt r h).trans (hn r h)
      · intro r h
        exact (hrt r h).trans (hr r h)
      · intro j hj
        exact (hmt j (by rw [hn 530 (by omega)];exact hj)).trans (hm j hj)

theorem program_exec (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s → Prepared s → ∃ count t,Exec params input candidate s count t ∧ CandidateResult P f bound s t count)
    (s : State) (hs : P s) (hmask : s.natReg 520<2^s.natReg 500) :
    ∃ count t,Exec params input (program candidate) s count t ∧ P t ∧
      count≤s.natReg 513*(bound (s.natReg 520)+29)+15 ∧
      t.realReg 570=sum f (s.natReg 520) (s.natReg 513) 0/(s.natReg 513:ℝ) ∧
      (∀ r,((500≤r ∧ r<540 ∧ r≠521 ∧ r≠522) ∨ (570≤r ∧ r≠571)) → t.natReg r=s.natReg r) ∧
      (∀ r,572≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 530 → t.natMem j=s.natMem j) := by
  let ready := runCode params input initCode s
  have hready : P ready :=
    stable.nat _ (stable.nat _ (stable.real _ hs _ _ (by simp)) _ _ (by simp)) _ _ (by simp)
  obtain ⟨c,a,ha,hpa,hc,hv,hn,hr,hm⟩ := repeats params input candidate P stable f bound realized
    (ready.natReg 513) ready hready (by simp [ready,initCode,runCode,step])
    (by simpa [ready,initCode,runCode,step] using hmask) (by simp [ready,initCode,runCode,step])
  let t := runCode params input finishCode a
  refine ⟨3+(c+2+7),t,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := Exec.seq (exec_code params input initCode s) (Exec.seq (Exec.repeat ha) (exec_code params input finishCode a))
    simpa [program,initCode,finishCode,codeCost,instrCost,t,ready] using hh
  · exact stable.real _ (stable.real _ hpa _ _ (by simp)) _ _ (by simp)
  · have hc' : c≤s.natReg 513*(bound (s.natReg 520)+29)+3 := by simpa [ready,initCode,runCode,step] using hc
    omega
  · simp [t,finishCode,runCode,step,hv,hn,ready,initCode]
  · intro r h
    have hh:=hn r (by omega)
    simpa [t,finishCode,runCode,step,ready,initCode,show r≠521 by omega,show r≠571 by omega] using hh
  · intro r h
    have hh:=hr r (by omega)
    simpa [t,finishCode,runCode,step,ready,initCode,show r≠570 by omega,show r≠571 by omega] using hh
  · intro j hj
    have hh:=hm j (by simpa [ready,initCode,runCode,step] using hj)
    simpa [t,finishCode,runCode,step,ready,initCode] using hh

end Manuscript.RestrictedSKTrials
