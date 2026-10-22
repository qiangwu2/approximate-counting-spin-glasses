import Manuscript.SKPrimitiveReturn
import Manuscript.SKPrimitiveIndex

/-! One actual pair primitive: choose its endpoint closure, compute its
charged degree and basis address, then insert it into the coefficient array. -/
noncomputable section
namespace Manuscript.SKPrimitivePair
open RestrictedMachine SKBasisEncoding SKIndexSpecifications
open SpinGlass SKCoefficient SKCountedExecution SKFastEvaluator

def checkCode : List Instruction := [.neq 262 250 251]
def closureProgram : Program := .seq (code checkCode)
  (.branch 262 SKPrimitiveReturn.program SKPrimitivePath.program)
def program : Program := .seq closureProgram
  (.seq SKPrimitiveIndex.pairProgram SKPrimitiveInsert.program)

def scalar {V : Type*} [DecidableEq V] {N b K : ℕ}
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (a c : Fin b) (S : Finset (Fin K)) : ℝ :=
  if a=c then (cachedReturn branch outside f cache a S).value
  else (cachedPath branch outside f cache a c S).value

theorem closure_nat_frame {p : Parameters} {i : Inputs} {s t : State} {count r : ℕ}
    (h : Exec p i closureProgram s count t)
    (hr : (132<r ∧ r≠260 ∧ r≠261 ∧ r≠262)) : t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [closureProgram,checkCode,SKPrimitiveReturn.program,SKPrimitivePath.program,SKPrimitivePath.setupCode,
    SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,SKPrimitiveNormalize.program,
    SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,
    IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,
    code,Program.All,Instruction.natDestination]
  omega

theorem closure_realized {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K)
    (a c : Fin b) (S : Finset (Fin K))
    (hN : s.natReg 200=N) (hK : s.natReg 201=K) (hT : s.natReg 220=2^K*N)
    (ha : s.natReg 250=a.val) (hc : s.natReg 251=c.val)
    (hS : s.natReg 252=(maskEquiv K S).val)
    (hcache : ∀ j : Fin N,
      s.realMem (s.natReg 253+a.val*(2^K*N)+(maskEquiv K S).val*N+j.val)=cache (Sum.inl a) S j)
    (hweight : ∀ j : Fin N,s.realMem (s.natReg 254+c.val*N+j.val)=pairWeight f (outside j) (branch c)) :
    ∃ count t, Exec p i closureProgram s count t ∧ count≤27*N+29*K+74 ∧
      t.realReg 0=scalar branch outside f cache a c S ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let d := runCode p i checkCode s
  by_cases heq : a=c
  · subst c
    have hflag : d.natReg 262≠0 := by simp [d,checkCode,runCode,step,ha,hc]
    obtain ⟨count,t,he,bc,hv,hm,hn⟩ := SKPrimitiveReturn.return_realized p i d branch outside f cache a S
      (by simpa [d,checkCode,runCode,step] using hN)
      (by simpa [d,checkCode,runCode,step] using hK)
      (by simpa [d,checkCode,runCode,step] using hT)
      (by simpa [d,checkCode,runCode,step] using ha)
      (by simpa [d,checkCode,runCode,step] using hc)
      (by simpa [d,checkCode,runCode,step] using hS)
      (by simpa [d,checkCode,runCode,step] using hcache)
      (by simpa [d,checkCode,runCode,step] using hweight)
    exact ⟨4+(count+3),t,Exec.seq (exec_code p i checkCode s) (Exec.branchNonzero hflag he),by omega,
      by simpa [scalar] using hv,hm,hn⟩
  · have hvals : a.val≠c.val := fun hh => heq (Fin.ext hh)
    have hflag : d.natReg 262=0 := by simp [d,checkCode,runCode,step,ha,hc,hvals]
    obtain ⟨t,he,hv,hm,hn,_⟩ := SKPrimitivePath.path_realized p i d branch outside f cache a c S
      (by simpa [d,checkCode,runCode,step] using hN)
      (by simpa [d,checkCode,runCode,step] using hT)
      (by simpa [d,checkCode,runCode,step] using ha)
      (by simpa [d,checkCode,runCode,step] using hc)
      (by simpa [d,checkCode,runCode,step] using hS)
      (by simpa [d,checkCode,runCode,step] using hcache)
      (by simpa [d,checkCode,runCode,step] using hweight)
    exact ⟨4+(27*N+34+3),t,Exec.seq (exec_code p i checkCode s) (Exec.branchZero hflag he),by omega,
      by simpa [scalar,heq] using hv,hm,hn⟩

def valid {b K : ℕ} (a c : Fin b) (S : Finset (Fin K)) : Prop :=
  (if a=c then 2 else 1)≤S.card ∧ a≤c
instance {b K : ℕ} (a c : Fin b) (S : Finset (Fin K)) : Decidable (valid a c S) :=
  inferInstanceAs (Decidable ((if a=c then 2 else 1)≤S.card ∧ a≤c))
def charge {b K : ℕ} (q : Fin b → ℕ) (a c : Fin b) (S : Finset (Fin K)) : ℕ :=
  S.card-1+q a+q c

def insertionAddress {b K : ℕ} (q : Fin b → ℕ) (a c : Fin b) (S : Finset (Fin K)) (base : ℕ) : ℕ :=
  base+(charge q a c S*2^K+(maskEquiv K S).val)*6^b+
    (degreeEquiv b (pathDegrees a c)).val

theorem pair_realized {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K)
    (a c : Fin b) (S : Finset (Fin K))
    (hN : s.natReg 200=N) (hK : s.natReg 201=K) (hT : s.natReg 220=2^K*N)
    (ha : s.natReg 250=a.val) (hc : s.natReg 251=c.val)
    (hS : s.natReg 252=(maskEquiv K S).val)
    (hcapacity : s.natReg 273=K) (hp : s.natReg 274=2^K) (hq : s.natReg 275=6^b)
    (hcharges : ∀ j,s.natMem (s.natReg 282+j.val)=q j)
    (hcache : ∀ j : Fin N,
      s.realMem (s.natReg 253+a.val*(2^K*N)+(maskEquiv K S).val*N+j.val)=cache (Sum.inl a) S j)
    (hweight : ∀ j : Fin N,s.realMem (s.natReg 254+c.val*N+j.val)=pairWeight f (outside j) (branch c)) :
    ∃ count t, Exec p i program s count t ∧ count≤27*N+58*K+18*b+202 ∧
      t.realMem=(if valid a c S ∧ charge q a c S≤K then
        Function.update s.realMem (insertionAddress q a c S (s.natReg 276))
          (s.realMem (insertionAddress q a c S (s.natReg 276))+scalar branch outside f cache a c S)
        else s.realMem) ∧ t.natMem=s.natMem := by
  obtain ⟨cc,d,hed,bcc,hscalar,hdm,hdn⟩ := closure_realized p i s branch outside f cache a c S hN hK hT ha hc hS hcache hweight
  have df (r) (hr : 132<r ∧ r≠260 ∧ r≠261 ∧ r≠262) := closure_nat_frame hed hr
  obtain ⟨ci,e,hee,bci,hcharge,hmask,hdegree,hvalid,hem,hen,her⟩ := SKPrimitiveIndex.pair_realized p i d
  have ef (r) (hr : (132<r ∧ r<270) ∨ r=273 ∨ r=274 ∨ r=275 ∨ r=276 ∨ r=282 ∨ 289<r) :=
    SKPrimitiveIndex.pair_natReg_frame hee hr
  have hc' : e.natReg 270=charge q a c S := by
    simpa [df 201 (by omega),df 252 (by omega),df 282 (by omega),df 250 (by omega),df 251 (by omega),
      hK,hS,ha,hc,hdn,hcharges,overlapFold_self,charge] using hcharge
  have hm' : e.natReg 271=(maskEquiv K S).val := by simpa [df 252 (by omega),hS] using hmask
  have hd' : e.natReg 272=(degreeEquiv b (pathDegrees a c)).val := by
    simpa [df 250 (by omega),df 251 (by omega),ha,hc,SKPrimitiveIndex.path_degree_index] using hdegree
  have hv' : e.natReg 277=if valid a c S then 1 else 0 := by
    simpa [df 201 (by omega),df 252 (by omega),df 250 (by omega),df 251 (by omega),hK,hS,ha,hc,
      overlapFold_self,valid,Fin.ext_iff] using hvalid
  obtain ⟨cs,t,het,bcs,hvalue,htn⟩ := SKPrimitiveInsert.insert_realized p i e
  refine ⟨cc+(ci+cs),t,Exec.seq hed (Exec.seq hee het),?_,?_,htn.trans (hen.trans hdn)⟩
  · have bi : ci≤29*K+9*(a.val+c.val)+85 := by
      simpa [df 201 (by omega),df 250 (by omega),df 251 (by omega),hK,ha,hc] using bci
    have hab := a.isLt; have hcb := c.isLt
    omega
  · rw [hvalue]
    have ea : SKPrimitiveInsert.address e=insertionAddress q a c S (s.natReg 276) := by
      rw [SKPrimitiveInsert.address,hc',hm',hd',ef 274 (by omega),ef 275 (by omega),ef 276 (by omega),
        df 274 (by omega),df 275 (by omega),df 276 (by omega),hp,hq]
      rfl
    simp [ea,hv',hc',ef 273 (by omega),df 273 (by omega),hcapacity,hem,hdm,her 0,hscalar]
end Manuscript.SKPrimitivePair
