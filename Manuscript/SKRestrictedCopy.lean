import Manuscript.SKRestrictedArrays

noncomputable section
namespace Manuscript.SKRestrictedCopy
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays

/-- Runtime source/destination pointers in registers37/38, length31, unit36. -/
def setup : List Instruction :=
  [.ncopy 10 37,.ncopy 11 37,.ncopy 12 38,.ncopy 13 36,.ncopy 14 31]
def program : Program := .seq (code setup) (RestrictedArrays.program .copy)

theorem program_frame (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input program s c t) :
    (∀ r, 15 ≤ r → t.natReg r=s.natReg r) ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_⟩
  · intro r hr
    apply he.natReg_frame
    simp [program,setup,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.natDestination]; omega
  · apply he.natMem_frame
    simp [program,setup,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.writesNatMemory]

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (source dest : ℕ) (f : Coefficients b K)
    (hsource : s.natReg 37=source) (hdest : s.natReg 38=dest)
    (hM : s.natReg 31=(K+1)*2^K*6^b) (hone : s.natReg 36=1)
    (hf : Represents source f s.realMem)
    (hdisjoint : ∀ i j, i < (K+1)*2^K*6^b → j < i → source+i ≠ dest+j) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 30*((K+1)*2^K*6^b)+15 ∧ Represents dest f t.realMem ∧
      (∀ address, (∀ i, i < (K+1)*2^K*6^b → address ≠ dest+i) →
        t.realMem address=s.realMem address) := by
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 10 u := exec_code _ _ _ _
  have um : u.realMem=s.realMem := rfl
  have up : u.natReg 12=dest := by simp [u,setup,runCode,step,hdest]
  have ulen : u.natReg 14=(K+1)*2^K*6^b := by simp [u,setup,runCode,step,hM]
  obtain ⟨c,t,ht,hc,hout,hi⟩ := coefficient_array .copy params input u source source dest f f
    (by simp [u,setup,runCode,step,hsource]) (by simp [u,setup,runCode,step,hsource])
    up (by simp [u,setup,runCode,step,hone]) ulen hf hf
    (fun i j hi hj => ⟨hdisjoint i j hi hj,hdisjoint i j hi hj⟩)
  refine ⟨10+c,t,Exec.seq hu ht,by omega,hout,?_⟩
  intro address ha
  rw [preserved_outside .copy params input hi address (by simpa only [up,ulen] using ha),um]

end Manuscript.SKRestrictedCopy
