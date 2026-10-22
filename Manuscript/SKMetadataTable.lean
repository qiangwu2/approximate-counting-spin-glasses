import Manuscript.SKMetadataGeneration

noncomputable section
namespace Manuscript.RestrictedMachine.IndexGeneration

def recordField (r : PairRecord) (j : ℕ) : ℕ :=
  match j with | 0 => r.accepted | 1 => r.left | 2 => r.right | 3 => r.target | _ => 0

def metadataPrefix (memory : ℕ→ℕ) (base : ℕ) (records : ℕ→PairRecord) : ℕ→(ℕ→ℕ)
  | 0 => memory
  | n+1 => writeRecord (metadataPrefix memory base records n) (base+4*n) (records n)

theorem writeRecord_inside (memory : ℕ→ℕ) (base j : ℕ) (r : PairRecord) (hj : j<4) :
    writeRecord memory base r (base+j)=recordField r j := by
  have h : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases h with h | h | h | h <;> subst j <;> simp [writeRecord,recordField,Function.update_apply]

theorem writeRecord_outside (memory : ℕ→ℕ) (base address : ℕ) (r : PairRecord)
    (h : address<base ∨ base+4≤address) : writeRecord memory base r address=memory address := by
  simp [writeRecord,Function.update_apply,show address≠base by omega,
    show address≠base+1 by omega,show address≠base+2 by omega,show address≠base+3 by omega]

theorem metadataPrefix_inside (memory : ℕ→ℕ) (base : ℕ) (records : ℕ→PairRecord)
    (n j offset : ℕ) (hj : j<n) (ho : offset<4) :
    metadataPrefix memory base records n (base+4*j+offset)=recordField (records j) offset := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [metadataPrefix]
    by_cases h : j=n
    · subst j
      exact writeRecord_inside _ _ _ _ ho
    · rw [writeRecord_outside _ _ _ _ (Or.inl (by omega))]
      exact ih (by omega)

def indexedRecord (s : State) (j : ℕ) : PairRecord :=
  pairRecord (writeNatReg (writeNatReg s 140 (j/s.natReg 166)) 141 (j%s.natReg 166))

def metadataInit : List Instruction := [.nconst 168 0, .nconst 167 1, .nmul 169 166 166]
def metadataDecode : List Instruction := [.ndiv 140 168 166, .nmod 141 168 166]
def metadataBody : Program :=
  .seq (code metadataDecode) (.seq pairProgram (.atom (.nadd 168 168 167)))
/-- Runtime nat166=M; the program calculates M*M and traverses all pairs in
numerical lexicographic order. It uses no supplied enumeration or metadata. -/
def metadataProgram : Program := .seq (code metadataInit) (.repeat 169 metadataBody)

def MetadataInvariant (seed : State) (n : ℕ) (s : State) : Prop :=
  s.natReg 168=n ∧ s.natReg 167=1 ∧ s.natReg 166=seed.natReg 166 ∧
  s.natReg 147=seed.natReg 147+4*n ∧
  (∀ r, 142≤r → r≤150 → r≠147 → s.natReg r=seed.natReg r) ∧
  s.realMem=seed.realMem ∧
  s.natMem=metadataPrefix seed.natMem (seed.natReg 147) (indexedRecord seed) n

theorem metadata_step (p : Parameters) (i : Inputs) (seed : State) (n : ℕ) (s : State)
    (hs : MetadataInvariant seed n s) :
    ∃ c t, Exec p i metadataBody s c t ∧ c≤52*seed.natReg 145+29*seed.natReg 146+152 ∧
      MetadataInvariant seed (n+1) t := by
  rcases hs with ⟨hn,hone,hM,hptr,hfixed,hm,hnm⟩
  let ready := runCode p i metadataDecode s
  have hd : Exec p i (code metadataDecode) s 8 ready := exec_code _ _ _ _
  obtain ⟨cp,v,hp,bp,vp,vm⟩ := pair_execution p i ready
  let t := step p i (.nadd 168 168 167) v
  have hf (r : ℕ) (hr : r < 100 ∨ 165 < r ∨ (140≤r ∧ r≤150 ∧ r≠147)) :
      v.natReg r=ready.natReg r := pair_natReg_frame p i ready v cp r hp hr
  have vr : pairRecord ready=indexedRecord seed n := by
    simp [pairRecord,indexedRecord,ready,metadataDecode,runCode,step,hn,hM,
      hfixed 142 (by omega) (by omega) (by omega),
      hfixed 143 (by omega) (by omega) (by omega),
      hfixed 144 (by omega) (by omega) (by omega),
      hfixed 145 (by omega) (by omega) (by omega),
      hfixed 146 (by omega) (by omega) (by omega),
      hfixed 148 (by omega) (by omega) (by omega),
      hfixed 149 (by omega) (by omega) (by omega),
      hfixed 150 (by omega) (by omega) (by omega)]
  have vp' : v.natReg 147=seed.natReg 147+4*n+4 := by
    simpa [ready,metadataDecode,runCode,step,hptr] using vp
  have vm' : v.natMem=metadataPrefix seed.natMem (seed.natReg 147) (indexedRecord seed) (n+1) := by
    rw [vr] at vm
    simpa [metadataPrefix,ready,metadataDecode,runCode,step,hptr,hnm] using vm
  refine ⟨8+(cp+4),t,Exec.seq hd (Exec.seq hp (Exec.atom _ _)),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have b := bp
    simp only [ready,metadataDecode,runCode,step,writeNatReg_natReg] at b
    simp only [show (145:ℕ)≠141 by omega,show (145:ℕ)≠140 by omega,
      show (146:ℕ)≠141 by omega,show (146:ℕ)≠140 by omega,if_false] at b
    rw [hfixed 145 (by omega) (by omega) (by omega),hfixed 146 (by omega) (by omega) (by omega)] at b
    omega
  · simp [t,step,hf 168 (by omega),hf 167 (by omega),ready,metadataDecode,runCode,hn,hone]
  · simp [t,step,hf 167 (by omega),ready,metadataDecode,runCode,hone]
  · simp [t,step,hf 166 (by omega),ready,metadataDecode,runCode,hM]
  · simp [t,step,vp',Nat.mul_add,Nat.add_assoc]
  · intro r hr hr' hne
    have hr140 : r≠140 := by omega
    have hr141 : r≠141 := by omega
    have hr168 : r≠168 := by omega
    simp [t,step,hr168,hf r (Or.inr (Or.inr ⟨by omega,hr',hne⟩)),ready,metadataDecode,
      runCode,hr140,hr141,hfixed r hr hr' hne]
  · exact (pair_realMem_frame p i ready v cp hp).trans hm
  · exact vm'

theorem metadata_repeats (p : Parameters) (i : Inputs) (seed : State) (count n : ℕ) (s : State)
    (hs : MetadataInvariant seed n s) :
    ∃ c t, Repeats p i metadataBody count s c t ∧
      c≤count*(52*seed.natReg 145+29*seed.natReg 146+157)+3 ∧
      MetadataInvariant seed (n+count) t := by
  induction count generalizing n s with
  | zero => exact ⟨3,s,Repeats.zero _ _,by simp,by simpa using hs⟩
  | succ count ih =>
    obtain ⟨c,m,hc,bc,hm⟩ := metadata_step p i seed n s hs
    obtain ⟨d,t,hd,bd,ht⟩ := ih (n+1) m hm
    refine ⟨c+d+5,t,Repeats.succ hc hd,?_,?_⟩
    · rw [Nat.add_mul]
      omega
    · convert ht using 1 <;> omega

theorem metadata_execution (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i metadataProgram s c t ∧
      c≤s.natReg 166*s.natReg 166*(52*s.natReg 145+29*s.natReg 146+157)+11 ∧
      t.natMem=metadataPrefix s.natMem (s.natReg 147) (indexedRecord s) (s.natReg 166*s.natReg 166) ∧
      t.natReg 147=s.natReg 147+4*(s.natReg 166*s.natReg 166) ∧ t.realMem=s.realMem := by
  let ready := runCode p i metadataInit s
  have hi : MetadataInvariant s 0 ready := by
    refine ⟨?_,?_,?_,?_,?_,rfl,rfl⟩
    all_goals try { simp [ready,metadataInit,runCode,step] }
    intro r hr hr' hne
    simp [ready,metadataInit,runCode,step,show r≠169 by omega,show r≠168 by omega,show r≠167 by omega]
  obtain ⟨c,t,hc,bc,ht⟩ := metadata_repeats p i s (s.natReg 166*s.natReg 166) 0 ready hi
  have hn : ready.natReg 169=s.natReg 166*s.natReg 166 := by simp [ready,metadataInit,runCode,step]
  have hc' : Repeats p i metadataBody (ready.natReg 169) ready c t := by simpa [hn] using hc
  refine ⟨6+(c+2),t,Exec.seq (exec_code p i metadataInit s) (Exec.repeat hc'),by omega,?_,?_,ht.2.2.2.2.2.1⟩
  · simpa using ht.2.2.2.2.2.2
  · simpa using ht.2.2.2.1

end Manuscript.RestrictedMachine.IndexGeneration
