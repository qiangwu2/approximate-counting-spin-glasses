import Manuscript.SKPrimitiveCycle
import Manuscript.SKPrimitiveIndex

/-! The cycle primitive closes actual cached outside paths, computes its
charge and color mask, and adds the result to the dense coefficient array. -/
noncomputable section
namespace Manuscript.SKPrimitiveCycleInsert
open RestrictedMachine SKBasisEncoding SKIndexSpecifications
open SpinGlass SKCoefficient SKCountedExecution SKFastEvaluator

def program : Program := .seq SKPrimitiveCycle.program
  (.seq SKPrimitiveIndex.cycleProgram SKPrimitiveInsert.program)

def insertionAddress {K : ℕ} (b base : ℕ) (S : Finset (Fin K)) : ℕ :=
  base+(S.card*2^K+(maskEquiv K S).val)*6^b

theorem closure_nat_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i SKPrimitiveCycle.program s c t)
    (hr : 132<r ∧ r≠260 ∧ r≠261) : t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [SKPrimitiveCycle.program,SKPrimitiveCycle.sumProgram,SKPrimitiveCycle.setupCode,
    SKRestrictedGrid.program,SKRestrictedGrid.body,SKRestrictedGrid.tailCode,
    SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,SKPrimitiveNormalize.program,
    SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,
    IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,
    code,Program.All,Instruction.natDestination]
  omega

theorem cycle_realized {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State)
    (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (S : Finset (Fin K))
    (hN : s.natReg 200=N) (hK : s.natReg 201=K) (hT : s.natReg 220=2^K*N)
    (hb : s.natReg 256=b) (hS : s.natReg 252=(maskEquiv K S).val)
    (hcapacity : s.natReg 273=K) (hp : s.natReg 274=2^K) (hq : s.natReg 275=6^b)
    (hcache : ∀ r j : Fin N,
      s.realMem (s.natReg 253+(b+r.val)*(2^K*N)+(maskEquiv K S).val*N+j.val)=cache (Sum.inr r) S j)
    (hweight : ∀ r j : Fin N,s.realMem (s.natReg 254+r.val*N+j.val)=pairWeight f (outside r) (outside j)) :
    ∃ count t, Exec p i program s count t ∧ count≤N*(27*N+18)+58*K+134 ∧
      t.realMem=(if 3≤S.card then
        Function.update s.realMem (insertionAddress b (s.natReg 276) S)
          (s.realMem (insertionAddress b (s.natReg 276) S)+(cachedCycle outside f cache S).value)
        else s.realMem) ∧ t.natMem=s.natMem := by
  obtain ⟨cc,d,hed,bcc,hscalar,hdm,hdn⟩ := SKPrimitiveCycle.cycle_realized p i s outside f cache S hN hK hT hb hS hcache hweight
  have df (r) (hr : 132<r ∧ r≠260 ∧ r≠261) := closure_nat_frame hed hr
  obtain ⟨ci,e,hee,bci,hcharge,hmask,hdegree,hvalid,hem,hen,her⟩ := SKPrimitiveIndex.cycle_realized p i d
  have ef (r) (hr : (127<r ∧ r<270) ∨ r=273 ∨ r=274 ∨ r=275 ∨ r=276 ∨ 286<r) := SKPrimitiveIndex.cycle_natReg_frame hee hr
  have hc' : e.natReg 270=S.card := by
    simpa [df 201 (by omega),df 252 (by omega),hK,hS,overlapFold_self] using hcharge
  have hm' : e.natReg 271=(maskEquiv K S).val := by simpa [df 252 (by omega),hS] using hmask
  have hv' : e.natReg 277=if 3≤S.card then 1 else 0 := by
    simpa [df 201 (by omega),df 252 (by omega),hK,hS,overlapFold_self] using hvalid
  obtain ⟨cs,t,het,bcs,hvalue,htn⟩ := SKPrimitiveInsert.insert_realized p i e
  refine ⟨cc+(ci+cs),t,Exec.seq hed (Exec.seq hee het),?_,?_,htn.trans (hen.trans hdn)⟩
  · have bi : ci≤29*K+23 := by simpa [df 201 (by omega),hK] using bci
    omega
  · rw [hvalue]
    have ea : SKPrimitiveInsert.address e=insertionAddress b (s.natReg 276) S := by
      rw [SKPrimitiveInsert.address,hc',hm',hdegree,ef 274 (by omega),ef 275 (by omega),ef 276 (by omega),
        df 274 (by omega),df 275 (by omega),df 276 (by omega),hp,hq]
      simp [insertionAddress]
    have hcard : S.card≤K := by simpa using Finset.card_le_univ S
    simp [ea,hv',hc',ef 273 (by omega),df 273 (by omega),hcapacity,hcard,hem,hdm,her 0,hscalar]
end Manuscript.SKPrimitiveCycleInsert
