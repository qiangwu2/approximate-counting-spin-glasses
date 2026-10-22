import Manuscript.SKRootCacheLayout

noncomputable section
namespace Manuscript.SKRootCache
open RestrictedMachine SKMemoUpdate SKMemoPass SKMemoLayers

def memoCode : List Instruction := [.ncopy 208 232,.ncopy 205 238,.ncopy 206 239]
def copyCode : List Instruction :=
  [.ncopy 10 205,.ncopy 11 205,.nmul 241 234 236,.nadd 241 241 240,
   .ncopy 12 241,.nconst 13 1,.ncopy 14 236]
def tailCode : List Instruction := [.nadd 234 234 235]
def body : Program := .seq SKRootStart.program (.seq (code memoCode)
  (.seq SKMemoInitialization.fullProgram (.seq (code copyCode)
    (.seq (RestrictedArrays.program .copy) (code tailCode)))))

def memoCost (d : Layout) :=
  9*d.K+30*d.T+d.K*(d.T*(38*d.K+27*d.N+137)+21)+35
def bodyCost (d : Layout) := 30*d.N+memoCost d+30*d.T+100

def Protected (r : ℕ) : Prop :=
  r=200 ∨ r=201 ∨ r=204 ∨ r=207 ∨ (230≤r ∧ r≤240 ∧ r≠234)

theorem Registers.transfer {d : Layout} {r r' : ℕ} {s t : State}
    (hs : Registers d r s) (hf : ∀i,Protected i → t.natReg i=s.natReg i)
    (hc : t.natReg 234=r') : Registers d r' t := by
  constructor
  · rw [hf 200 (by simp [Protected])]; exact hs.size
  · rw [hf 201 (by simp [Protected])]; exact hs.colors
  · rw [hf 204 (by simp [Protected])]; exact hs.colorBase
  · rw [hf 207 (by simp [Protected])]; exact hs.weightBase
  · rw [hf 230 (by simp [Protected])]; exact hs.branches
  · rw [hf 231 (by simp [Protected])]; exact hs.branchBase
  · rw [hf 232 (by simp [Protected])]; exact hs.arena
  · rw [hf 233 (by simp [Protected])]; exact hs.roots
  · exact hc
  · rw [hf 235 (by simp [Protected])]; exact hs.one
  · rw [hf 236 (by simp [Protected])]; exact hs.tableSize
  · rw [hf 238 (by simp [Protected])]; exact hs.left
  · rw [hf 239 (by simp [Protected])]; exact hs.right
  · rw [hf 240 (by simp [Protected])]; exact hs.cache

def Away (d : Layout) (r address : ℕ) : Prop :=
  address<d.arena ∨ (d.cache≤address ∧
    (address<d.cache+r*d.T ∨ d.cache+(r+1)*d.T≤address))

theorem body_execution (params : Parameters) (input : Inputs) (d : Layout)
    (χ : Fin d.N→Fin d.K) (w : Fin d.N→Fin d.N→ℝ)
    (branch : Fin d.B→Fin d.N→ℝ) (r : ℕ) (s : State)
    (hs : Registers d r s)
    (hc : ∀j,s.natMem (d.colorBase+j.val)=(χ j).val)
    (hw : ∀i j,s.realMem (d.weightBase+i.val*d.N+j.val)=w i j)
    (hb : ∀i j,s.realMem (d.branchBase+i.val*d.N+j.val)=branch i j) :
    ∃c t,Exec params input body s c t ∧ c≤bodyCost d ∧
      Registers d (r+1) t ∧ t.natMem=s.natMem ∧
      (∀S j,t.realMem (rowAddress d.N (d.cache+r*d.T) S j.val)=
        SpinGlass.ColorPath.pathTable χ (start branch r) w S j) ∧
      (∀address,Away d r address → t.realMem address=s.realMem address) := by
  obtain ⟨cs,a,ha,bsa,hav,haf⟩ := SKRootStart.execution params input s (by
    intro hr
    rw [hs.counter,hs.branches] at hr
    rw [hs.branchBase,hs.counter,hs.size,hs.arena]
    have hf := d.branchFit
    nlinarith)
  have af (i : ℕ) (hi : (200 ≤ i ∧ i ≤ 241) ∨ 244 < i) : a.natReg i=s.natReg i := haf.2.2 i hi
  let b := runCode params input memoCode a
  have bf (i : ℕ) (hi : i ≠ 208 ∧ i ≠ 205 ∧ i ≠ 206) : b.natReg i=a.natReg i := by
    simp [b,memoCode,runCode,step,hi.1,hi.2.1,hi.2.2]
  have bm : b.realMem=a.realMem := by simp [b,memoCode,runCode,step]
  have bn : b.natMem=a.natMem := by simp [b,memoCode,runCode,step]
  have bl : b.natReg 205=d.left := by simp [b,memoCode,runCode,step,af 238 (by omega),hs.left]
  have br : b.natReg 206=d.right := by simp [b,memoCode,runCode,step,af 239 (by omega),hs.right]
  have bready : SKMemoInitialization.InputsReady d.colorBase d.weightBase d.arena χ (start branch r) w b := by
    constructor
    · rw [bf 200 (by omega),af 200 (by omega)]; exact hs.size
    · rw [bf 201 (by omega),af 201 (by omega)]; exact hs.colors
    · rw [bf 204 (by omega),af 204 (by omega)]; exact hs.colorBase
    · rw [bf 207 (by omega),af 207 (by omega)]; exact hs.weightBase
    · simp [b,memoCode,runCode,step,af 232 (by omega),hs.arena]
    · rw [bl,br]; exact d.separation
    · intro j; rw [bn,haf.1]; exact hc j
    · intro i j
      rw [bm,haf.2.1 _ (Or.inl (by rw [hs.arena]; exact d.weight_lt i j))]
      exact hw i j
    · intro j
      rw [bm]
      have hv := hav j.val (by rw [hs.size]; exact j.isLt)
      rw [hs.arena] at hv
      rw [hv,SKRootStart.startValue,hs.branches,hs.counter,hs.branchBase,hs.size]
      by_cases hr : r<d.B
      · simp [start,hr,show ¬d.B≤r by omega,hb ⟨r,hr⟩ j]
      · simp [start,hr,show d.B≤r by omega]
  obtain ⟨cm,m,hm,bsm,hmv,hmn,hbanks,hmframe⟩ :=
    SKMemoInitialization.full_memo_realized params input d.colorBase d.weightBase d.arena χ (start branch r) w b bready
  have mf (i : ℕ) (hi : i = 200 ∨ i = 201 ∨ i = 204 ∨ i = 207 ∨ ((223 < i ∧ i ≤ 241) ∨ 244 < i)) : m.natReg i=s.natReg i := by
    rw [SKMemoInitialization.full_natReg_frame params input b m cm i hm (by rcases hi with h|h|h|h|h <;> omega)]
    rw [bf i (by rcases hi with h|h|h|h|h <;> omega),af i (by rcases hi with h|h|h|h|h <;> omega)]
  have bankend : m.natReg 205+d.T≤d.cache := by
    rcases hbanks with h|h
    · rw [h.1,bl]; simp only [Layout.left,Layout.cache]; omega
    · rw [h.1,br]; simp only [Layout.right,Layout.cache]; omega
  let q := runCode params input copyCode m
  have qm : q.realMem=m.realMem := by simp [q,copyCode,runCode,step]
  have qn : q.natMem=m.natMem := by simp [q,copyCode,runCode,step]
  have q10 : q.natReg 10=m.natReg 205 := by simp [q,copyCode,runCode,step]
  have q11 : q.natReg 11=m.natReg 205 := by simp [q,copyCode,runCode,step]
  have q12 : q.natReg 12=d.cache+r*d.T := by
    simp [q,copyCode,runCode,step,mf 234 (by omega),mf 236 (by omega),mf 240 (by omega),hs.counter,hs.tableSize,hs.cache,Nat.add_comm]
  have q14 : q.natReg 14=d.T := by simp [q,copyCode,runCode,step,mf 236 (by omega),hs.tableSize]
  have q13 : q.natReg 13=1 := by simp [q,copyCode,runCode,step]
  have qf (i : ℕ) (hi : 200 ≤ i ∧ i ≠ 241) : q.natReg i=m.natReg i := by
    have h10 : i ≠ 10 := by omega
    have h11 : i ≠ 11 := by omega
    have h12 : i ≠ 12 := by omega
    have h13 : i ≠ 13 := by omega
    have h14 : i ≠ 14 := by omega
    simp [q,copyCode,runCode,step,hi.2,h10,h11,h12,h13,h14]
  obtain ⟨cx,x,hx,bsx,hxi,hxv⟩ := RestrictedArrays.pointwise_realized .copy params input q q13 (by
    intro i j hi hj
    rw [q10,q11,q12]
    rw [q14] at hi
    constructor <;> omega)
  have xf (i : ℕ) (hi : 200 ≤ i) : x.natReg i=q.natReg i := hxi.2.2.2.2.2.1 i (by omega) (by omega) (by omega)
  let t := runCode params input tailCode x
  have tm : t.realMem=x.realMem := by simp [t,tailCode,runCode,step]
  have tn : t.natMem=x.natMem := by simp [t,tailCode,runCode,step]
  have tf (i : ℕ) (hi : i ≠ 234) : t.natReg i=x.natReg i := by simp [t,tailCode,runCode,step,hi]
  have he : Exec params input body s (cs+(6+(cm+(17+(cx+4))))) t := by
    exact Exec.seq ha (Exec.seq (exec_code params input memoCode a)
      (Exec.seq hm (Exec.seq (exec_code params input copyCode m)
        (Exec.seq hx (exec_code params input tailCode x)))))
  refine ⟨_,t,he,?_,?_,?_,?_,?_⟩
  · rw [hs.size] at bsa
    rw [q14] at bsx
    change cm≤memoCost d at bsm
    simp only [bodyCost]
    omega
  · apply hs.transfer
    · intro i hi
      rw [tf i (by simp only [Protected] at hi; omega),xf i (by simp only [Protected] at hi; omega),
        qf i (by simp only [Protected] at hi; omega),mf i (by simp only [Protected] at hi; omega)]
    · simp [t,tailCode,runCode,step,xf 234 (by omega),xf 235 (by omega),qf 234 (by omega),qf 235 (by omega),
        mf 234 (by omega),mf 235 (by omega),hs.counter,hs.one]
  · exact tn.trans (hxi.2.1.trans (qn.trans (hmn.trans (bn.trans haf.1))))
  · intro S j
    have hj : cellIndex S j<d.T := by rw [cellIndex_eq]; exact (cellEquiv d.N d.K (S,j)).isLt
    have hv := hxv (cellIndex S j) (by rw [q14]; exact hj)
    rw [q12,q10,qm,RestrictedArrays.Operation.eval] at hv
    have hmval : m.realMem (m.natReg 205+cellIndex S j)=
        SpinGlass.ColorPath.pathTable χ (start branch r) w S j := by
      simpa only [rowAddress,cellIndex,Nat.add_assoc] using hmv S j
    simpa only [tm,rowAddress,cellIndex,Nat.add_assoc] using hv.trans hmval
  · intro address haway
    rw [tm,hxi.1,RestrictedArrays.loop_frame]
    · rw [qm,hmframe address (d.outside b bl br address (by
        rcases haway with h|h; exact Or.inl h; exact Or.inr h.1)),bm]
      apply haf.2.1
      rw [hs.arena,hs.size]
      rcases haway with h|h
      · exact Or.inl h
      · apply Or.inr; simp only [Layout.cache] at h; omega
    · intro j hj
      rw [q12]
      rw [q14] at hj
      simp only [Away,Layout.cache,Nat.add_mul,Nat.one_mul] at *
      rcases haway with h|h
      · omega
      · rcases h.2 with h|h <;> omega

end Manuscript.SKRootCache
