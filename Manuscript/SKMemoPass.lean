import Manuscript.SKMemoUpdate

/-! A uniform runtime traversal of every mask/endpoint cell of a memo layer.
The source bank is held fixed while the complete next bank is filled. -/
noncomputable section
namespace Manuscript.SKMemoPass
open RestrictedMachine SKBasisEncoding SKMemoUpdate

def cellEquiv (N K : ℕ) : (Finset (Fin K) × Fin N) ≃ Fin (2^K*N) :=
  (Equiv.prodCongr (maskEquiv K) (Equiv.refl (Fin N))).trans finProdFinEquiv

def cellIndex {N K : ℕ} (S : Finset (Fin K)) (j : Fin N) : ℕ :=
  (maskEquiv K S).val*N+j.val

theorem cellIndex_eq {N K : ℕ} (S : Finset (Fin K)) (j : Fin N) :
    cellIndex S j = (cellEquiv N K (S,j)).val := by
  simp [cellIndex,cellEquiv,finProdFinEquiv]
  ring

theorem cellIndex_injective {N K : ℕ} {S T : Finset (Fin K)} {i j : Fin N}
    (h : cellIndex S i=cellIndex T j) : S=T ∧ i=j := by
  rw [cellIndex_eq,cellIndex_eq] at h
  exact Prod.mk.inj ((cellEquiv N K).injective (Fin.ext h))

def preludeCode : List Instruction := [.ndiv 202 221 200, .nmod 203 221 200]
def tailCode : List Instruction := [.nadd 221 221 222]
def body : Program := .seq (code preludeCode) (.seq SKMemoUpdate.program (code tailCode))
def program : Program := .repeat 220 body

structure Layout (N K : ℕ) where
  colorBase : ℕ
  oldBase : ℕ
  newBase : ℕ
  weightBase : ℕ
  startBase : ℕ
  layer : ℕ
  new_ne_old : ∀ (S T : Finset (Fin K)) (i j : Fin N),
    rowAddress N newBase S i.val ≠ rowAddress N oldBase T j.val
  new_ne_weight : ∀ (S : Finset (Fin K)) (j i k : Fin N),
    rowAddress N newBase S j.val ≠ weightBase+i.val*N+k.val
  new_ne_start : ∀ (S : Finset (Fin K)) (j i : Fin N),
    rowAddress N newBase S j.val ≠ startBase+i.val

def layerValue {N K : ℕ} (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (old : Finset (Fin K) → Fin N → ℝ)
    (layer : ℕ) (S : Finset (Fin K)) (j : Fin N) : ℝ :=
  if S.card=layer then SpinGlass.ColorMemoExecution.update χ start w old S j else old S j

def Frame {N K : ℕ} (layout : Layout N K) (s t : State) : Prop :=
  ∀ address, (∀ (S : Finset (Fin K)) (j : Fin N),
    address ≠ rowAddress N layout.newBase S j.val) → t.realMem address=s.realMem address

structure Invariant {N K : ℕ} (layout : Layout N K) (χ : Fin N → Fin K)
    (start : Fin N → ℝ) (w : Fin N → Fin N → ℝ)
    (old : Finset (Fin K) → Fin N → ℝ) (n : ℕ) (s : State) : Prop where
  size : s.natReg 200=N
  colors : s.natReg 201=K
  colorBase : s.natReg 204=layout.colorBase
  oldBase : s.natReg 205=layout.oldBase
  newBase : s.natReg 206=layout.newBase
  weightBase : s.natReg 207=layout.weightBase
  startBase : s.natReg 208=layout.startBase
  layer : s.natReg 209=layout.layer
  bound : s.natReg 220=2^K*N
  counter : s.natReg 221=n
  one : s.natReg 222=1
  colorRead : ∀ j, s.natMem (layout.colorBase+j.val)=(χ j).val
  oldRead : ∀ S j, s.realMem (rowAddress N layout.oldBase S j.val)=old S j
  weightRead : ∀ i j, s.realMem (layout.weightBase+i.val*N+j.val)=w i j
  startRead : ∀ j, s.realMem (layout.startBase+j.val)=start j
  computed : ∀ S j, cellIndex S j<n → s.realMem (rowAddress N layout.newBase S j.val)=
    layerValue χ start w old layout.layer S j

theorem update_high_frame (params : Parameters) (input : Inputs) (s t : State)
    (c r : ℕ) (h : Exec params input SKMemoUpdate.program s c t) (hr : 214<r) :
    t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [SKMemoUpdate.program, SKMemoMetadata.program, SKMemoMetadata.preludeCode,
    SKMemoMetadata.middle, SKMemoMetadata.suffix, IndexGeneration.powerProgram,
    IndexGeneration.powerInit, IndexGeneration.powerBody, IndexGeneration.overlapProgram,
    IndexGeneration.overlapInit, IndexGeneration.overlapBody, SKRestrictedMemoCell.program,
    SKRestrictedKernels.dotProgram, SKRestrictedKernels.dotBody, code, Program.All,
    Instruction.natDestination]
  omega

theorem body_realized {N K : ℕ} (params : Parameters) (input : Inputs)
    (layout : Layout N K) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (old : Finset (Fin K) → Fin N → ℝ)
    (n : ℕ) (s : State) (hinv : Invariant layout χ start w old n s) (hlt : n<2^K*N) :
    ∃ count t, Exec params input body s count t ∧ count ≤ 38*K+27*N+132 ∧
      Invariant layout χ start w old (n+1) t ∧ t.natMem=s.natMem ∧ Frame layout s t := by
  let pair := (cellEquiv N K).symm ⟨n,hlt⟩
  let S := pair.1
  let j := pair.2
  have hindex : cellIndex S j=n := by
    rw [cellIndex_eq]
    exact congrArg Fin.val ((cellEquiv N K).apply_symm_apply ⟨n,hlt⟩)
  have hN : 0<N := Nat.zero_lt_of_lt j.isLt
  have hmask : n/N=(maskEquiv K S).val := by
    rw [← hindex,cellIndex,Nat.mul_comm _ N,Nat.mul_add_div hN,
      Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have hend : n%N=j.val := by
    rw [← hindex,cellIndex,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt j.isLt]
  let a := runCode params input preludeCode s
  have hreg : Registers layout.colorBase layout.oldBase layout.newBase layout.weightBase
      layout.startBase layout.layer S j a := by
    simp [Registers,a,preludeCode,runCode,step,hinv.size,hinv.colors,hinv.counter,
      hmask,hend,hinv.colorBase,hinv.oldBase,hinv.newBase,hinv.weightBase,
      hinv.startBase,hinv.layer]
  obtain ⟨cu,u,hu,bu,mu,nu,_⟩ := update_realized params input a χ start w old S j
    layout.colorBase layout.oldBase layout.newBase layout.weightBase layout.startBase layout.layer
    hreg (by simpa [a,preludeCode,runCode,step] using hinv.colorRead j)
    (by simpa [a,preludeCode,runCode,step] using hinv.oldRead)
    (by simpa [a,preludeCode,runCode,step] using fun i => hinv.weightRead i j)
    (by simpa [a,preludeCode,runCode,step] using hinv.startRead j)
  have uf (r : ℕ) (hr : 200≤r ∧ r≤209) : u.natReg r=a.natReg r :=
    SKMemoUpdate.natReg_frame params input a u cu r hu hr
  have uh (r : ℕ) (hr : 214<r) : u.natReg r=a.natReg r :=
    update_high_frame params input a u cu r hu hr
  have hnmem : u.natMem=s.natMem := by simpa [a,preludeCode,runCode,step] using nu
  have humem : u.realMem=Function.update s.realMem (rowAddress N layout.newBase S j.val)
      (layerValue χ start w old layout.layer S j) := by
    simpa [a,preludeCode,runCode,step,layerValue] using mu
  let t := runCode params input tailCode u
  have htnat : ∀ r, t.natReg r = if r=221 then n+1 else u.natReg r := by
    intro r
    simp [t,tailCode,runCode,step,uh 221 (by omega),uh 222 (by omega),
      a,preludeCode,hinv.counter,hinv.one]
  have htmem : t.realMem=u.realMem := by simp [t,tailCode,runCode,step]
  have htnmem : t.natMem=s.natMem := by simpa [t,tailCode,runCode,step] using hnmem
  refine ⟨8+(cu+4),t,Exec.seq (exec_code params input preludeCode s)
    (Exec.seq hu (exec_code params input tailCode u)),by omega,?_,htnmem,?_⟩
  rotate_left
  · intro address haway
    rw [htmem,humem,Function.update_of_ne (haway S j)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [htnat,uf 200 (by omega),a,preludeCode,runCode,step,hinv.size]
  · simp [htnat,uf 201 (by omega),a,preludeCode,runCode,step,hinv.colors]
  · simp [htnat,uf 204 (by omega),a,preludeCode,runCode,step,hinv.colorBase]
  · simp [htnat,uf 205 (by omega),a,preludeCode,runCode,step,hinv.oldBase]
  · simp [htnat,uf 206 (by omega),a,preludeCode,runCode,step,hinv.newBase]
  · simp [htnat,uf 207 (by omega),a,preludeCode,runCode,step,hinv.weightBase]
  · simp [htnat,uf 208 (by omega),a,preludeCode,runCode,step,hinv.startBase]
  · simp [htnat,uf 209 (by omega),a,preludeCode,runCode,step,hinv.layer]
  · simp [htnat,uh 220 (by omega),a,preludeCode,runCode,step,hinv.bound]
  · simp [htnat]
  · simp [htnat,uh 222 (by omega),a,preludeCode,runCode,step,hinv.one]
  · intro i; rw [htnmem]; exact hinv.colorRead i
  · intro T i; rw [htmem,humem,Function.update_of_ne (layout.new_ne_old S T j i).symm]; exact hinv.oldRead T i
  · intro i k; rw [htmem,humem,Function.update_of_ne (layout.new_ne_weight S j i k).symm]; exact hinv.weightRead i k
  · intro i; rw [htmem,humem,Function.update_of_ne (layout.new_ne_start S j i).symm]; exact hinv.startRead i
  · intro T i hi
    by_cases heq : cellIndex T i=n
    · obtain ⟨rfl,rfl⟩ := cellIndex_injective (heq.trans hindex.symm)
      rw [htmem,humem,Function.update_self]
    · have hne : rowAddress N layout.newBase T i.val ≠ rowAddress N layout.newBase S j.val := by
        intro h
        have h' : cellIndex T i=cellIndex S j := by dsimp [rowAddress,cellIndex] at *; omega
        exact heq (h'.trans hindex)
      rw [htmem,humem,Function.update_of_ne hne]
      exact hinv.computed T i (by omega)

theorem pass_repeats {N K : ℕ} (params : Parameters) (input : Inputs)
    (layout : Layout N K) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (old : Finset (Fin K) → Fin N → ℝ)
    (remaining : ℕ) : ∀ n s, Invariant layout χ start w old n s →
      n+remaining ≤ 2^K*N →
      ∃ count t, Repeats params input body remaining s count t ∧
        count ≤ remaining*(38*K+27*N+137)+3 ∧
        Invariant layout χ start w old (n+remaining) t ∧ t.natMem=s.natMem ∧ Frame layout s t := by
  induction remaining with
  | zero =>
    intro n s hs _
    exact ⟨3,s,Repeats.zero body s,by simp,by simpa using hs,rfl,fun _ _ => rfl⟩
  | succ k ih =>
    intro n s hs hbound
    obtain ⟨c,u,hu,bc,hui,hun,huf⟩ := body_realized params input layout χ start w old n s hs (by omega)
    obtain ⟨d,t,ht,bd,hti,htn,htf⟩ := ih (n+1) u hui (by omega)
    refine ⟨c+d+5,t,Repeats.succ hu ht,?_,?_,htn.trans hun,fun address haway => (htf address haway).trans (huf address haway)⟩
    · nlinarith
    · convert hti using 1 <;> omega

/-- Actual runtime completion of all cells; old and edge/start caches are
preserved, and every output cell is the next memo layer. -/
theorem pass_realized {N K : ℕ} (params : Parameters) (input : Inputs)
    (layout : Layout N K) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (old : Finset (Fin K) → Fin N → ℝ)
    (s : State) (hs : Invariant layout χ start w old 0 s) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ (2^K*N)*(38*K+27*N+137)+5 ∧
      (∀ S j, t.realMem (rowAddress N layout.newBase S j.val)=
        layerValue χ start w old layout.layer S j) ∧
      Invariant layout χ start w old (2^K*N) t ∧ t.natMem=s.natMem ∧ Frame layout s t := by
  obtain ⟨c,t,he,hc,hi,hn,hf⟩ := pass_repeats params input layout χ start w old (2^K*N) 0 s hs (by omega)
  refine ⟨c+2,t,?_,by omega,?_,by simpa using hi,hn,hf⟩
  · exact Exec.repeat (by simpa only [hs.bound] using he)
  · intro S j
    apply hi.computed S j
    rw [cellIndex_eq]
    simpa using (cellEquiv N K (S,j)).isLt

end Manuscript.SKMemoPass
