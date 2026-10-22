import Manuscript.SKDirectIndex
import Manuscript.SKRestrictedSingle

noncomputable section
namespace Manuscript.SKDirectFactor
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays

def test : List Instruction := [.nle 458 443 442]
def zero : List Instruction := [.nconst 42 0,.rconst 42 0]
def program : Program := .seq (code test)
  (.branch 458 (.seq (code zero) SKRestrictedSingle.program)
    (.seq SKDirectIndex.program SKRestrictedSingle.program))

def factor {V : Type*} [DecidableEq V] {b K : ℕ}
    (endpointCharge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ)
    (a c : Fin b) : Coefficients b K :=
  if a<c then (SKChargedExecution.direct endpointCharge branch f a c).coeff else 0

theorem program_frame (params : Parameters) (input : Inputs) {s t : State} {count : ℕ}
    (he : Exec params input program s count t) :
    (∀ r, 15≤r → r≠42 → (r<130 ∨ 132<r) → (r<450 ∨ 458<r) →
      t.natReg r=s.natReg r) ∧
    (∀ r, 5≤r → r≠42 → t.realReg r=s.realReg r) ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_,?_⟩
  · intro r hr h42 hpower hdirect; apply he.natReg_frame
    simp [program,test,zero,SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,
      SKDirectIndex.finish,IndexGeneration.powerProgram,IndexGeneration.powerInit,
      IndexGeneration.powerBody,SKRestrictedSingle.program,SKRestrictedSingle.setup,
      SKRestrictedSingle.finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.natDestination]; omega
  · intro r hr h42; apply he.realReg_frame
    simp [program,test,zero,SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,
      SKDirectIndex.finish,IndexGeneration.powerProgram,IndexGeneration.powerInit,
      IndexGeneration.powerBody,SKRestrictedSingle.program,SKRestrictedSingle.setup,
      SKRestrictedSingle.finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.realDestination]; omega
  · apply he.natMem_frame
    simp [program,test,zero,SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,
      SKDirectIndex.finish,IndexGeneration.powerProgram,IndexGeneration.powerInit,
      IndexGeneration.powerBody,SKRestrictedSingle.program,SKRestrictedSingle.setup,
      SKRestrictedSingle.finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.writesNatMemory]

theorem index_frame (params : Parameters) (input : Inputs) {s t : State} {count : ℕ}
    (he : Exec params input SKDirectIndex.program s count t) (r : ℕ)
    (hr : r<130 ∨ (132<r ∧ r<450)) (h42 : r≠42) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,SKDirectIndex.finish,
    IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
    code,Program.All,Instruction.natDestination]; omega

theorem program_exec {V : Type*} [DecidableEq V] {b K : ℕ} (hK : 1≤K)
    (params : Parameters) (input : Inputs) (s : State) (base chargeBase weightBase : ℕ)
    (endpointCharge : Fin b → ℕ) (branch : Fin b → V) (f : Finset V → ℝ)
    (a c : Fin b)
    (hb : s.natReg 440=b) (ha : s.natReg 442=a.val) (hc : s.natReg 443=c.val)
    (hcharge : s.natReg 444=chargeBase) (hweight : s.natReg 445=weightBase)
    (hcolors : s.natReg 447=2^K) (hdegrees : s.natReg 448=6^b)
    (hp : s.natReg 37=base) (hM : s.natReg 31=(K+1)*2^K*6^b) (hone : s.natReg 36=1)
    (hcharges : ∀ i : Fin b, s.natMem (chargeBase+i.val)=endpointCharge i)
    (hweights : ∀ i j : Fin b, s.realMem (weightBase+i.val*b+j.val)=
      SKFastEvaluator.pairWeight f (branch i) (branch j)) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 30*((K+1)*2^K*6^b)+18*b+116 ∧
      Represents base (factor (K:=K) endpointCharge branch f a c) t.realMem ∧
      (∀ address, (∀ i, i<(K+1)*2^K*6^b → address≠base+i) →
        t.realMem address=s.realMem address) := by
  let u := runCode params input test s
  have hu : Exec params input (code test) s 4 u := exec_code _ _ _ _
  have un (r : ℕ) (hr : r≠458) : u.natReg r=s.natReg r := by simp [u,test,runCode,step,hr]
  by_cases hlt : a<c
  · have hflag : u.natReg 458=0 := by
      simp [u,test,runCode,step,ha,hc,show ¬c.val≤a.val by exact not_le.mpr hlt]
    obtain ⟨d,v,hv,hd,hindex,hvalue,hm,hnm⟩ := SKDirectIndex.program_exec params input u
    let charge := if endpointCharge a=0 ∨ endpointCharge c=0 then 0 else 1
    have hck : charge≤K := by dsimp [charge]; split <;> omega
    let x : Basis b K := (⟨charge,Nat.lt_succ_of_le hck⟩,∅,SKFastEvaluator.pathDegrees a c)
    have xe : encode x=charge*2^K*6^b+6^a.val+6^c.val := by
      rw [encode_formula,mask_formula,SKDirectIndex.path_degree_index a c (ne_of_lt hlt)]
      simp [x,Nat.add_assoc]
    have vi : v.natReg 42=encode x := by
      rw [xe]
      simpa [u,test,runCode,step,ha,hc,hcharge,hcolors,hdegrees,hcharges,charge] using hindex
    have vv : v.realReg 42=SKFastEvaluator.pairWeight f (branch a) (branch c) := by
      simpa [u,test,runCode,step,ha,hc,hb,hweight,hweights] using hvalue
    have vn (r : ℕ) (hr : r<130) (h42 : r≠42) : v.natReg r=s.natReg r :=
      (index_frame params input hv r (Or.inl hr) h42).trans (un r (by omega))
    obtain ⟨e,t,ht,he,hout,hframe⟩ := SKRestrictedSingle.program_exec params input v base x
      (SKFastEvaluator.pairWeight f (branch a) (branch c))
      ((vn 37 (by omega) (by omega)).trans hp) ((vn 31 (by omega) (by omega)).trans hM)
      ((vn 36 (by omega) (by omega)).trans hone) vi vv
    refine ⟨4+((d+e)+3),t,Exec.seq hu (Exec.branchZero hflag (Exec.seq hv ht)),?_,?_,?_⟩
    · have dd : d≤9*(a.val+c.val)+86 := by simpa [u,test,runCode,step,ha,hc] using hd
      have ai := a.isLt; have ci := c.isLt; omega
    · simpa [factor,hlt,SKChargedExecution.direct,SKFastEvaluator.insertMonomial,
        show (if endpointCharge a=0 ∨ endpointCharge c=0 then 0 else 1)≤K from hck,
        SKRing.monomial,x,charge] using hout
    · intro address had; exact (hframe address had).trans (congrFun hm address)
  · have hflag : u.natReg 458≠0 := by
      simp [u,test,runCode,step,ha,hc,show c.val≤a.val by exact le_of_not_gt hlt]
    let v := runCode params input zero u
    have hv : Exec params input (code zero) u 2 v := exec_code _ _ _ _
    obtain ⟨e,t,ht,he,hout,hframe⟩ := SKRestrictedSingle.program_exec params input v base
      (oneBasis b K) 0
      (by simp [v,zero,u,test,runCode,step,hp])
      (by simp [v,zero,u,test,runCode,step,hM])
      (by simp [v,zero,u,test,runCode,step,hone])
      (by simp [v,zero,runCode,step,SKRestrictedOne.one_encode])
      (by simp [v,zero,runCode,step])
    refine ⟨4+((2+e)+3),t,Exec.seq hu (Exec.branchNonzero hflag (Exec.seq hv ht)),by omega,?_,hframe⟩
    simpa [Represents,factor,hlt,single] using hout

end Manuscript.SKDirectFactor
