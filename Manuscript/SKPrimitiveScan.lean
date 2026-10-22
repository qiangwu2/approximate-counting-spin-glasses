import Manuscript.SKPrimitiveTerms
import Manuscript.SKRestrictedArrays

/-! Uniform primitive-key enumeration. Pair keys are decoded by runtime
quotient/remainder operations; no host-generated instruction schedule is used. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace Manuscript.SKPrimitiveScan
open RestrictedMachine SKBasisEncoding SKPrimitiveTerms
open SpinGlass SKCoefficient SKCountedExecution SKFastEvaluator
open scoped BigOperators

def pairSetup : List Instruction :=
  [.ndiv 250 290 274,.nmod 251 250 256,.ndiv 250 250 256,
   .nmod 252 290 274,.ncopy 254 255]
def cycleSetup : List Instruction := [.ncopy 252 290,.ncopy 254 257]
def advance : List Instruction := [.nadd 290 290 292]
def pairBody : Program := .seq (code pairSetup) (.seq SKPrimitivePair.program (code advance))
def cycleBody : Program := .seq (code cycleSetup) (.seq SKPrimitiveCycleInsert.program (code advance))
def pairInit : List Instruction := [.nconst 290 0,.nconst 292 1,.nmul 291 256 256,.nmul 291 291 274]
def cycleInit : List Instruction := [.nconst 290 0]
def pairProgram : Program := .seq (code pairInit) (.repeat 291 pairBody)
def cycleProgram : Program := .seq (code cycleInit) (.repeat 274 cycleBody)

def pairEquiv (b K : ℕ) : ((Fin b × Fin b) × Finset (Fin K)) ≃ Fin ((b*b)*2^K) :=
  (Equiv.prodCongr finProdFinEquiv (maskEquiv K)).trans finProdFinEquiv

def pairEntry {V : Type*} [DecidableEq V] {N b K : ℕ}
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (j : ℕ) : Coefficients b K :=
  if h : j<(b*b)*2^K then
    let key := (pairEquiv b K).symm ⟨j,h⟩
    pairTerm q branch outside f cache key.1.1 key.1.2 key.2 else 0

def cycleEntry {V : Type*} [DecidableEq V] {N b K : ℕ}
    (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (j : ℕ) : Coefficients b K :=
  if h : j<2^K then cycleTerm outside f cache ((maskEquiv K).symm ⟨j,h⟩) else 0

def stableRegs : Finset ℕ := {200,201,220,253,255,256,257,273,274,275,276,282,292}
def Stable (initial s : State) : Prop :=
  (∀ r∈stableRegs,s.natReg r=initial.natReg r) ∧ s.natMem=initial.natMem ∧
    ∀ address,address < initial.natReg 276 → s.realMem address=initial.realMem address

theorem stable_refl (s : State) : Stable s s := ⟨fun _ _ => rfl,rfl,fun _ _ => rfl⟩
theorem Stable.trans {s t u : State} (hst : Stable s t) (htu : Stable t u) : Stable s u := by
  refine ⟨fun r hr => (htu.1 r hr).trans (hst.1 r hr),htu.2.1.trans hst.2.1,?_⟩
  intro a ha
  rw [htu.2.2 a (by rw [hst.1 276 (by simp [stableRegs])]; exact ha),hst.2.2 a ha]

structure Data {V : Type*} [DecidableEq V] {N b K : ℕ}
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (s : State) : Prop where
  vertices : s.natReg 200=N
  palette : s.natReg 201=K
  stride : s.natReg 220=2^K*N
  branches : s.natReg 256=b
  capacity : s.natReg 273=K
  colors : s.natReg 274=2^K
  degrees : s.natReg 275=6^b
  one : s.natReg 292=1
  chargeData : ∀ a,s.natMem (s.natReg 282+a.val)=q a
  branchCache : ∀ a S j,s.realMem (s.natReg 253+a.val*(2^K*N)+(maskEquiv K S).val*N+j.val)=cache (Sum.inl a) S j
  branchCacheBound : ∀ (a : Fin b) (S : Finset (Fin K)) (j : Fin N),
    s.natReg 253+a.val*(2^K*N)+(maskEquiv K S).val*N+j.val<s.natReg 276
  outsideCache : ∀ r S j,s.realMem (s.natReg 253+(b+r.val)*(2^K*N)+(maskEquiv K S).val*N+j.val)=cache (Sum.inr r) S j
  outsideCacheBound : ∀ (r : Fin N) (S : Finset (Fin K)) (j : Fin N),
    s.natReg 253+(b+r.val)*(2^K*N)+(maskEquiv K S).val*N+j.val<s.natReg 276
  branchWeights : ∀ a j,s.realMem (s.natReg 255+a.val*N+j.val)=pairWeight f (outside j) (branch a)
  branchWeightsBound : ∀ (a : Fin b) (j : Fin N),s.natReg 255+a.val*N+j.val<s.natReg 276
  outsideWeights : ∀ r j,s.realMem (s.natReg 257+r.val*N+j.val)=pairWeight f (outside r) (outside j)
  outsideWeightsBound : ∀ (r j : Fin N),s.natReg 257+r.val*N+j.val<s.natReg 276

theorem Data.stable {V : Type*} [DecidableEq V] {N b K : ℕ}
    {q : Fin b → ℕ} {branch : Fin b → V} {outside : Fin N → V} {f : Finset V → ℝ}
    {cache : Root (Fin N) b → Table (Fin N) K} {s t : State}
    (hs : Data q branch outside f cache s) (hst : Stable s t) : Data q branch outside f cache t := by
  have hf (r) (hr : r∈stableRegs) := hst.1 r hr
  refine ⟨(hf 200 (by simp [stableRegs])).trans hs.vertices,(hf 201 (by simp [stableRegs])).trans hs.palette,
    (hf 220 (by simp [stableRegs])).trans hs.stride,(hf 256 (by simp [stableRegs])).trans hs.branches,
    (hf 273 (by simp [stableRegs])).trans hs.capacity,(hf 274 (by simp [stableRegs])).trans hs.colors,
    (hf 275 (by simp [stableRegs])).trans hs.degrees,(hf 292 (by simp [stableRegs])).trans hs.one,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a; rw [hst.2.1,hf 282 (by simp [stableRegs])]; exact hs.chargeData a
  · intro a S j; rw [hf 253 (by simp [stableRegs]),hst.2.2 _ (hs.branchCacheBound a S j)]; exact hs.branchCache a S j
  · simpa [hf 253 (by simp [stableRegs]),hf 276 (by simp [stableRegs])] using hs.branchCacheBound
  · intro r S j; rw [hf 253 (by simp [stableRegs]),hst.2.2 _ (hs.outsideCacheBound r S j)]; exact hs.outsideCache r S j
  · simpa [hf 253 (by simp [stableRegs]),hf 276 (by simp [stableRegs])] using hs.outsideCacheBound
  · intro a j; rw [hf 255 (by simp [stableRegs]),hst.2.2 _ (hs.branchWeightsBound a j)]; exact hs.branchWeights a j
  · simpa [hf 255 (by simp [stableRegs]),hf 276 (by simp [stableRegs])] using hs.branchWeightsBound
  · intro r j; rw [hf 257 (by simp [stableRegs]),hst.2.2 _ (hs.outsideWeightsBound r j)]; exact hs.outsideWeights r j
  · simpa [hf 257 (by simp [stableRegs]),hf 276 (by simp [stableRegs])] using hs.outsideWeightsBound

theorem pair_nat_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i pairBody s c t) (hr : r∈stableRegs ∨ r=291 ∨ 299<r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp only [stableRegs,Finset.mem_insert,Finset.mem_singleton] at hr
  simp [pairBody,pairSetup,advance,SKPrimitivePair.program,SKPrimitivePair.closureProgram,SKPrimitivePair.checkCode,
    SKPrimitiveReturn.program,SKPrimitivePath.program,SKPrimitivePath.setupCode,SKPrimitiveNormalize.program,
    SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,
    SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,
    SKPrimitiveIndex.pairProgram,SKPrimitiveIndex.cardCode,SKPrimitiveIndex.firstCode,SKPrimitiveIndex.secondCode,SKPrimitiveIndex.pairFinish,
    IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,
    IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
    SKPrimitiveInsert.program,SKPrimitiveInsert.checkCode,SKPrimitiveInsert.updateCode,code,Program.All,Instruction.natDestination]
  omega

theorem pair_body_exec {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (old : Coefficients b K) (index : ℕ)
    (hs : Data q branch outside f cache s) (hi : index<(b*b)*2^K) (hindex : s.natReg 290=index)
    (hm : ∀ y,s.realMem (s.natReg 276+encode y)=old y) :
    ∃ count t, Exec p i pairBody s count t ∧ count≤27*N+58*K+18*b+224 ∧
      Stable s t ∧ t.natReg 290=index+1 ∧
      (∀ y,t.realMem (s.natReg 276+encode y)=old y+pairEntry q branch outside f cache index y) := by
  let key := (pairEquiv b K).symm ⟨index,hi⟩
  let a := key.1.1
  let c := key.1.2
  let S := key.2
  have ha : a.val=index/2^K/b := rfl
  have hc : c.val=index/2^K%b := rfl
  have hS : (maskEquiv K S).val=index%2^K := by
    change (maskEquiv K ((maskEquiv K).symm _)).val=_
    rw [Equiv.apply_symm_apply]; rfl
  let d := runCode p i pairSetup s
  obtain ⟨cc,e,he,bcc,hvalue,hen⟩ := SKPrimitivePair.pair_realized p i d q branch outside f cache a c S
    (by simpa [d,pairSetup,runCode,step] using hs.vertices)
    (by simpa [d,pairSetup,runCode,step] using hs.palette)
    (by simpa [d,pairSetup,runCode,step] using hs.stride)
    (by simp [d,pairSetup,runCode,step,hs.colors,hs.branches,hindex,ha])
    (by simp [d,pairSetup,runCode,step,hs.colors,hs.branches,hindex,hc])
    (by simp [d,pairSetup,runCode,step,hs.colors,hindex,hS])
    (by simpa [d,pairSetup,runCode,step] using hs.capacity)
    (by simpa [d,pairSetup,runCode,step] using hs.colors)
    (by simpa [d,pairSetup,runCode,step] using hs.degrees)
    (by simpa [d,pairSetup,runCode,step] using hs.chargeData)
    (by simpa [d,pairSetup,runCode,step] using hs.branchCache a S)
    (by simpa [d,pairSetup,runCode,step] using hs.branchWeights c)
  obtain ⟨hcoeff,hframe⟩ := pair_memory q branch outside f cache a c S (s.natReg 276) s.realMem e.realMem old hm
    (by simpa [d,pairSetup,runCode,step] using hvalue)
  let t := runCode p i advance e
  have heall : Exec p i pairBody s (18+(cc+4)) t :=
    Exec.seq (exec_code p i pairSetup s) (Exec.seq he (exec_code p i advance e))
  have hf (r) (hr : r∈stableRegs ∨ r=291 ∨ 299<r) := pair_nat_frame heall hr
  refine ⟨_,t,heall,by omega,⟨fun r hr => hf r (Or.inl hr),hen,hframe⟩,?_,?_⟩
  · have ei : e.natReg 290=d.natReg 290 := by
      apply he.natReg_frame
      simp [SKPrimitivePair.program,SKPrimitivePair.closureProgram,SKPrimitivePair.checkCode,
        SKPrimitiveReturn.program,SKPrimitivePath.program,SKPrimitivePath.setupCode,SKPrimitiveNormalize.program,
        SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,
        SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,
        SKPrimitiveIndex.pairProgram,SKPrimitiveIndex.cardCode,SKPrimitiveIndex.firstCode,SKPrimitiveIndex.secondCode,SKPrimitiveIndex.pairFinish,
        IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,
        IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
        SKPrimitiveInsert.program,SKPrimitiveInsert.checkCode,SKPrimitiveInsert.updateCode,code,Program.All,Instruction.natDestination]
    have eone : e.natReg 292=1 := by
      have hh : t.natReg 292=s.natReg 292 := hf 292 (by simp [stableRegs])
      simpa [t,advance,runCode,step,hs.one] using hh
    simp [t,advance,runCode,step,ei,d,pairSetup,hindex,eone]
  · simpa [t,advance,runCode,step,pairEntry,hi,key,a,c,S] using hcoeff


theorem cycle_nat_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i cycleBody s c t) (hr : r∈stableRegs ∨ r=291 ∨ 299<r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp only [stableRegs,Finset.mem_insert,Finset.mem_singleton] at hr
  simp [cycleBody,cycleSetup,advance,SKPrimitiveCycleInsert.program,
    SKPrimitiveCycle.program,SKPrimitiveCycle.sumProgram,SKPrimitiveCycle.setupCode,
    SKRestrictedGrid.program,SKRestrictedGrid.body,SKRestrictedGrid.tailCode,
    SKPrimitiveNormalize.program,SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,
    SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,
    SKPrimitiveIndex.cycleProgram,SKPrimitiveIndex.cardCode,SKPrimitiveIndex.cycleFinish,
    IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,
    SKPrimitiveInsert.program,SKPrimitiveInsert.checkCode,SKPrimitiveInsert.updateCode,code,Program.All,Instruction.natDestination]
  omega

theorem cycle_body_exec {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (old : Coefficients b K) (index : ℕ)
    (hs : Data q branch outside f cache s) (hi : index<2^K) (hindex : s.natReg 290=index)
    (hm : ∀ y,s.realMem (s.natReg 276+encode y)=old y) :
    ∃ count t, Exec p i cycleBody s count t ∧ count≤N*(27*N+18)+58*K+142 ∧
      Stable s t ∧ t.natReg 290=index+1 ∧
      (∀ y,t.realMem (s.natReg 276+encode y)=old y+cycleEntry outside f cache index y) := by
  let S := (maskEquiv K).symm ⟨index,hi⟩
  have hS : (maskEquiv K S).val=index := congrArg Fin.val ((maskEquiv K).apply_symm_apply _)
  let d := runCode p i cycleSetup s
  obtain ⟨cc,e,he,bcc,hvalue,hen⟩ := SKPrimitiveCycleInsert.cycle_realized p i d outside f cache S
    (by simpa [d,cycleSetup,runCode,step] using hs.vertices)
    (by simpa [d,cycleSetup,runCode,step] using hs.palette)
    (by simpa [d,cycleSetup,runCode,step] using hs.stride)
    (by simpa [d,cycleSetup,runCode,step] using hs.branches)
    (by simp [d,cycleSetup,runCode,step,hindex,hS])
    (by simpa [d,cycleSetup,runCode,step] using hs.capacity)
    (by simpa [d,cycleSetup,runCode,step] using hs.colors)
    (by simpa [d,cycleSetup,runCode,step] using hs.degrees)
    (by simpa [d,cycleSetup,runCode,step] using fun r j => hs.outsideCache r S j)
    (by simpa [d,cycleSetup,runCode,step] using hs.outsideWeights)
  obtain ⟨hcoeff,hframe⟩ := cycle_memory outside f cache S (s.natReg 276) s.realMem e.realMem old hm
    (by simpa [d,cycleSetup,runCode,step] using hvalue)
  let t := runCode p i advance e
  have heall : Exec p i cycleBody s (4+(cc+4)) t :=
    Exec.seq (exec_code p i cycleSetup s) (Exec.seq he (exec_code p i advance e))
  have hf (r) (hr : r∈stableRegs ∨ r=291 ∨ 299<r) := cycle_nat_frame heall hr
  refine ⟨_,t,heall,by omega,⟨fun r hr => hf r (Or.inl hr),hen,hframe⟩,?_,?_⟩
  · have ei : e.natReg 290=d.natReg 290 := by
      apply he.natReg_frame
      simp [SKPrimitiveCycleInsert.program,SKPrimitiveCycle.program,SKPrimitiveCycle.sumProgram,SKPrimitiveCycle.setupCode,
        SKRestrictedGrid.program,SKRestrictedGrid.body,SKRestrictedGrid.tailCode,
        SKPrimitiveNormalize.program,SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,
        SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,
        SKPrimitiveIndex.cycleProgram,SKPrimitiveIndex.cardCode,SKPrimitiveIndex.cycleFinish,
        IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,
        SKPrimitiveInsert.program,SKPrimitiveInsert.checkCode,SKPrimitiveInsert.updateCode,code,Program.All,Instruction.natDestination]
    have eone : e.natReg 292=1 := by
      have hh : t.natReg 292=s.natReg 292 := hf 292 (by simp [stableRegs])
      simpa [t,advance,runCode,step,hs.one] using hh
    simp [t,advance,runCode,step,ei,d,cycleSetup,hindex,eone]
  · simpa [t,advance,runCode,step,cycleEntry,hi,S] using hcoeff
end Manuscript.SKPrimitiveScan
