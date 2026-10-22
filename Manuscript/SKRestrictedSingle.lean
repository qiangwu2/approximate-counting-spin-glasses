import Manuscript.SKRestrictedOne

noncomputable section
namespace Manuscript.SKRestrictedSingle
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays

def setup : List Instruction :=
  [.ncopy 10 37,.ncopy 11 37,.ncopy 12 37,.ncopy 13 36,.ncopy 14 31,.rconst 4 0]
def finish : List Instruction := [.nadd 12 37 42,.storeReal 12 42]
def program : Program := .seq (code setup) (.seq (RestrictedArrays.program .fill) (code finish))

theorem program_frame (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input program s c t) :
    (∀ r, 15 ≤ r → t.natReg r=s.natReg r) ∧
    (∀ r, 5 ≤ r → t.realReg r=s.realReg r) ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_,?_⟩
  · intro r hr; apply he.natReg_frame
    simp [program,setup,finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.natDestination]; omega
  · intro r hr; apply he.realReg_frame
    simp [program,setup,finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.realDestination]; omega
  · apply he.natMem_frame
    simp [program,setup,finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.writesNatMemory]

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base : ℕ) (x : Basis b K) (value : ℝ)
    (hp : s.natReg 37=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hone : s.natReg 36=1) (hx : s.natReg 42=encode x) (hv : s.realReg 42=value) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 30*((K+1)*2^K*6^b)+23 ∧ Represents base (single x value) t.realMem ∧
      (∀ address, (∀ i, i < (K+1)*2^K*6^b → address ≠ base+i) →
        t.realMem address=s.realMem address) := by
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 11 u := exec_code _ _ _ _
  obtain ⟨c,v,he,hc,hzero,vi⟩ := fill_array (b:=b) (K:=K) params input u base
    (by simp [u,setup,runCode,step,hp]) (by simp [u,setup,runCode,step,hp])
    (by simp [u,setup,runCode,step,hp]) (by simp [u,setup,runCode,step,hone])
    (by simp [u,setup,runCode,step,hM])
  have vn (r : ℕ) (hr : 15 ≤ r) : v.natReg r=s.natReg r := by
    apply ((array_frame .fill params input he).1 r hr).trans
    apply hu.natReg_frame
    simp [setup,code,Program.All,Instruction.natDestination]; omega
  have vr : v.realReg 42=value := by
    rw [(array_frame .fill params input he).2.1 42 (by omega)]
    simpa [u,setup,runCode,step] using hv
  let t := runCode params input finish v
  have ht : Exec params input (code finish) v 7 t := exec_code _ _ _ _
  have tm : t.realMem=Function.update v.realMem (base+encode x) value := by
    simp [t,finish,runCode,step,writeRealMem,vn 37 (by omega),vn 42 (by omega),hp,hx,vr]
  refine ⟨11+(c+7),t,Exec.seq hu (Exec.seq he ht),by omega,?_,?_⟩
  · intro y
    rw [tm]
    by_cases hxy : x=y
    · subst y; simp [single]
    · have hn : base+encode y ≠ base+encode x := by
        intro hh; exact hxy ((encode_injective b K (by omega)).symm)
      rw [Function.update_of_ne hn]
      simpa [single,hxy,u,setup,runCode,step] using hzero y
  · intro address ha
    rw [tm,Function.update_of_ne (ha (encode x) (encode_lt x))]
    simpa [u,setup,runCode,step,hp,hM] using
      preserved_outside .fill params input vi address
        (by simpa [u,setup,runCode,step,hp,hM] using ha)

end Manuscript.SKRestrictedSingle
