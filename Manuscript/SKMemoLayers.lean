import Manuscript.SKMemoPass

/-! Full colorful-path memo computation by a fixed runtime loop over layers,
using two alternating cache banks. Every source table is saved in RAM. -/
noncomputable section
namespace Manuscript.SKMemoLayers
open RestrictedMachine SKBasisEncoding SKMemoUpdate

structure Separation (N K A B weightBase startBase : ℕ) : Prop where
  banks : ∀ (S T : Finset (Fin K)) (i j : Fin N),
    rowAddress N A S i.val ≠ rowAddress N B T j.val
  leftWeight : ∀ (S : Finset (Fin K)) (j i k : Fin N),
    rowAddress N A S j.val ≠ weightBase+i.val*N+k.val
  rightWeight : ∀ (S : Finset (Fin K)) (j i k : Fin N),
    rowAddress N B S j.val ≠ weightBase+i.val*N+k.val
  leftStart : ∀ (S : Finset (Fin K)) (j i : Fin N),
    rowAddress N A S j.val ≠ startBase+i.val
  rightStart : ∀ (S : Finset (Fin K)) (j i : Fin N),
    rowAddress N B S j.val ≠ startBase+i.val

theorem Separation.symm {N K A B W S : ℕ} (h : Separation N K A B W S) :
    Separation N K B A W S :=
  ⟨fun T U i j => (h.banks U T j i).symm,h.rightWeight,h.leftWeight,h.rightStart,h.leftStart⟩

def preludeCode : List Instruction := [.nadd 209 209 222, .nconst 221 0]
def tailCode : List Instruction := [.ncopy 223 205, .ncopy 205 206, .ncopy 206 223]
def body : Program := .seq (code preludeCode) (.seq SKMemoPass.program (code tailCode))
def program : Program := .repeat 201 body

structure Invariant {N K : ℕ} (colorBase weightBase startBase : ℕ)
    (χ : Fin N → Fin K) (start : Fin N → ℝ) (w : Fin N → Fin N → ℝ)
    (n : ℕ) (s : State) : Prop where
  size : s.natReg 200=N
  colors : s.natReg 201=K
  colorBaseReg : s.natReg 204=colorBase
  weightBaseReg : s.natReg 207=weightBase
  startBaseReg : s.natReg 208=startBase
  layer : s.natReg 209=n
  bound : s.natReg 220=2^K*N
  one : s.natReg 222=1
  separation : Separation N K (s.natReg 205) (s.natReg 206) weightBase startBase
  colorRead : ∀ j, s.natMem (colorBase+j.val)=(χ j).val
  oldRead : ∀ S j, s.realMem (rowAddress N (s.natReg 205) S j.val)=
    SpinGlass.ColorMemoExecution.memo χ start w n S j
  weightRead : ∀ i j, s.realMem (weightBase+i.val*N+j.val)=w i j
  startRead : ∀ j, s.realMem (startBase+j.val)=start j

def layerCost (N K : ℕ) : ℕ := (2^K*N)*(38*K+27*N+137)+16

def Banks (s t : State) : Prop :=
  (t.natReg 205=s.natReg 205 ∧ t.natReg 206=s.natReg 206) ∨
  (t.natReg 205=s.natReg 206 ∧ t.natReg 206=s.natReg 205)

def Outside (N K : ℕ) (s : State) (address : ℕ) : Prop :=
  ∀ (S : Finset (Fin K)) (j : Fin N),
    address ≠ rowAddress N (s.natReg 205) S j.val ∧
    address ≠ rowAddress N (s.natReg 206) S j.val

def Frame (N K : ℕ) (s t : State) : Prop :=
  ∀ address, Outside N K s address → t.realMem address=s.realMem address

theorem Banks.trans {s u t : State} (hsu : Banks s u) (hut : Banks u t) : Banks s t := by
  rcases hsu with hsu|hsu <;> rcases hut with hut|hut <;> simp_all [Banks]

theorem Banks.outside {N K : ℕ} {s t : State} (h : Banks s t)
    {address : ℕ} (ha : Outside N K s address) : Outside N K t address := by
  rcases h with h|h
  · simpa only [Outside,h.1,h.2] using ha
  · intro S j
    simpa only [h.1,h.2] using (ha S j).symm

theorem Frame.trans {N K : ℕ} {s u t : State} (hbank : Banks s u)
    (hsu : Frame N K s u) (hut : Frame N K u t) : Frame N K s t := by
  intro address haway
  exact (hut address (hbank.outside haway)).trans (hsu address haway)

theorem body_realized {N K : ℕ} (params : Parameters) (input : Inputs)
    (colorBase weightBase startBase : ℕ) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (n : ℕ) (s : State)
    (hs : Invariant colorBase weightBase startBase χ start w n s) :
    ∃ count t, Exec params input body s count t ∧ count ≤ layerCost N K ∧
      Invariant colorBase weightBase startBase χ start w (n+1) t ∧ t.natMem=s.natMem ∧
      Banks s t ∧ Frame N K s t := by
  let layout : SKMemoPass.Layout N K :=
    ⟨colorBase,s.natReg 205,s.natReg 206,weightBase,startBase,n+1,
      (fun S T i j => (hs.separation.banks T S j i).symm),
      hs.separation.rightWeight,hs.separation.rightStart⟩
  let a := runCode params input preludeCode s
  have ha : SKMemoPass.Invariant layout χ start w
      (SpinGlass.ColorMemoExecution.memo χ start w n) 0 a := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals simp [a,preludeCode,runCode,step,layout,hs.size,hs.colors,hs.colorBaseReg,
      hs.weightBaseReg,hs.startBaseReg,hs.layer,hs.bound,hs.one]
    all_goals first | exact hs.colorRead | exact hs.oldRead | exact hs.weightRead | exact hs.startRead
  obtain ⟨cp,u,hu,bc,hvalues,hui,hun,hframe⟩ := SKMemoPass.pass_realized params input layout χ start w
    (SpinGlass.ColorMemoExecution.memo χ start w n) a ha
  let t := runCode params input tailCode u
  have htmem : t.realMem=u.realMem := by simp [t,tailCode,runCode,step]
  have htnmem : t.natMem=s.natMem := by simpa [t,tailCode,runCode,step,a,preludeCode] using hun
  have htu : t.natReg 205=s.natReg 206 ∧ t.natReg 206=s.natReg 205 := by
    simp [t,tailCode,runCode,step,hui.oldBase,hui.newBase,layout]
  have htf (r : ℕ) (h205 : r ≠ 205) (h206 : r ≠ 206) (h223 : r ≠ 223) :
      t.natReg r=u.natReg r := by simp [t,tailCode,runCode,step,h205,h206,h223]
  refine ⟨5+(cp+6),t,Exec.seq (exec_code params input preludeCode s)
    (Exec.seq hu (exec_code params input tailCode u)),by dsimp [layerCost]; omega,?_,htnmem,Or.inr htu,?_⟩
  rotate_left
  · intro address haway
    rw [htmem]
    have hh := hframe address (fun S j => (haway S j).2)
    simpa [a,preludeCode,runCode,step] using hh
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [htf 200 (by decide) (by decide) (by decide)]; exact hui.size
  · rw [htf 201 (by decide) (by decide) (by decide)]; exact hui.colors
  · rw [htf 204 (by decide) (by decide) (by decide)]; exact hui.colorBase
  · rw [htf 207 (by decide) (by decide) (by decide)]; exact hui.weightBase
  · rw [htf 208 (by decide) (by decide) (by decide)]; exact hui.startBase
  · rw [htf 209 (by decide) (by decide) (by decide)]; exact hui.layer
  · rw [htf 220 (by decide) (by decide) (by decide)]; exact hui.bound
  · rw [htf 222 (by decide) (by decide) (by decide)]; exact hui.one
  · rw [htu.1,htu.2]; exact hs.separation.symm
  · intro j; rw [htnmem]; exact hs.colorRead j
  · intro S j
    rw [htmem,htu.1]
    have hh := hvalues S j
    simpa only [layout,SKMemoPass.layerValue,SpinGlass.ColorMemoExecution.memo] using hh
  · intro i j; rw [htmem]; exact hui.weightRead i j
  · intro j; rw [htmem]; exact hui.startRead j

theorem layers_repeats {N K : ℕ} (params : Parameters) (input : Inputs)
    (colorBase weightBase startBase : ℕ) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (remaining : ℕ) :
    ∀ n s, Invariant colorBase weightBase startBase χ start w n s →
    ∃ count t, Repeats params input body remaining s count t ∧
      count ≤ remaining*(layerCost N K+5)+3 ∧
      Invariant colorBase weightBase startBase χ start w (n+remaining) t ∧ t.natMem=s.natMem ∧
      Banks s t ∧ Frame N K s t := by
  induction remaining with
  | zero =>
    intro n s hs
    exact ⟨3,s,Repeats.zero body s,by simp,by simpa using hs,rfl,Or.inl ⟨rfl,rfl⟩,fun _ _ => rfl⟩
  | succ k ih =>
    intro n s hs
    obtain ⟨c,u,hu,hc,hui,hun,hub,huf⟩ := body_realized params input colorBase weightBase startBase χ start w n s hs
    obtain ⟨d,t,ht,hd,hti,htn,htb,htf⟩ := ih (n+1) u hui
    refine ⟨c+d+5,t,Repeats.succ hu ht,?_,?_,htn.trans hun,hub.trans htb,Frame.trans hub huf htf⟩
    · nlinarith
    · convert hti using 1 <;> omega

/-- All K layers are executed once, and the bank pointed to by natural205
contains the exact colorful-path table. Its dependencies are the initial
zero cache and raw prepared start/edge/color arrays. -/
theorem memo_realized {N K : ℕ} (params : Parameters) (input : Inputs)
    (colorBase weightBase startBase : ℕ) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (s : State)
    (hs : Invariant colorBase weightBase startBase χ start w 0 s) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ K*((2^K*N)*(38*K+27*N+137)+21)+5 ∧
      (∀ S j, t.realMem (rowAddress N (t.natReg 205) S j.val)=
        SpinGlass.ColorPath.pathTable χ start w S j) ∧
      Invariant colorBase weightBase startBase χ start w K t ∧ t.natMem=s.natMem ∧
      Banks s t ∧ Frame N K s t := by
  obtain ⟨c,t,he,hc,hi,hn,hb,hf⟩ := layers_repeats params input colorBase weightBase startBase χ start w K 0 s hs
  refine ⟨c+2,t,?_,?_,?_,by simpa using hi,hn,hb,hf⟩
  · exact Exec.repeat (by simpa only [hs.colors] using he)
  · have heq : layerCost N K+5=(2^K*N)*(38*K+27*N+137)+21 := by rfl
    rw [heq] at hc
    omega
  · intro S j
    have hh := hi.oldRead S j
    simpa only [Nat.zero_add,← SpinGlass.ColorMemoExecution.memo_correct χ start w S j,
      Fintype.card_fin] using hh

end Manuscript.SKMemoLayers
