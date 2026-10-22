import Manuscript.SKRestrictedArrays

noncomputable section
namespace Manuscript.SKRestrictedOne
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays

def setup : List Instruction :=
  [.ncopy 10 37, .ncopy 11 37, .ncopy 12 37, .ncopy 13 36, .ncopy 14 31, .rconst 4 0]
def finish : List Instruction := [.ncopy 12 37, .rconst 0 1, .storeReal 12 0]
def program : Program := .seq (code setup) (.seq (RestrictedArrays.program .fill) (code finish))

theorem one_encode (b K : ℕ) : encode (oneBasis b K)=0 := by
  rw [encode_formula,mask_formula,degree_formula]
  simp [oneBasis]

theorem one_formula {b K : ℕ} (x : Basis b K) : one b K x=if encode x=0 then 1 else 0 := by
  have hiff : oneBasis b K=x ↔ encode x=0 := by
    constructor
    · intro h; rw [← h,one_encode]
    · intro h; apply encode_injective b K; rw [h,one_encode]
  simp only [one,single,hiff]

theorem program_frame (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input program s c t) :
    (∀ r, 15 ≤ r → t.natReg r=s.natReg r) ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_⟩
  · intro r hr
    apply he.natReg_frame
    simp [program,setup,finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.natDestination]; omega
  · apply he.natMem_frame
    simp [program,setup,finish,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.writesNatMemory]

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base : ℕ) (hp : s.natReg 37=base)
    (hM : s.natReg 31=(K+1)*2^K*6^b) (hone : s.natReg 36=1) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 30*((K+1)*2^K*6^b)+22 ∧ Represents base (one b K) t.realMem ∧
      (∀ address, (∀ i, i < (K+1)*2^K*6^b → address ≠ base+i) →
        t.realMem address=s.realMem address) := by
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 11 u := exec_code _ _ _ _
  have um : u.realMem=s.realMem := rfl
  have up : u.natReg 37=base := by simp [u,setup,runCode,step,hp]
  have uout : u.natReg 12=base := by simp [u,setup,runCode,step,hp]
  have ulen : u.natReg 14=(K+1)*2^K*6^b := by simp [u,setup,runCode,step,hM]
  obtain ⟨c,v,hv,hc,hzero,vi⟩ := fill_array (b:=b) (K:=K) params input u base
    (by simp [u,setup,runCode,step,hp]) (by simp [u,setup,runCode,step,hp])
    uout (by simp [u,setup,runCode,step,hone]) ulen
  have vp : v.natReg 37=base := ((array_frame .fill params input hv).1 37 (by omega)).trans up
  let t := runCode params input finish v
  have ht : Exec params input (code finish) v 6 t := exec_code _ _ _ _
  have tm : t.realMem=Function.update v.realMem base 1 := by simp [t,finish,runCode,step,writeRealMem,vp]
  refine ⟨11+(c+6),t,Exec.seq hu (Exec.seq hv ht),by omega,?_,?_⟩
  · intro x
    rw [tm,one_formula]
    by_cases hx : encode x=0
    · simp [hx]
    · rw [Function.update_of_ne (by omega : base+encode x ≠ base)]
      simpa [hx,u,setup,runCode,step] using hzero x
  · intro address ha
    have Mpos : 0 < (K+1)*2^K*6^b := by positivity
    have hn : address ≠ base := by simpa using ha 0 Mpos
    rw [tm,Function.update_of_ne hn]
    rw [preserved_outside .fill params input vi address (by simpa only [uout,ulen] using ha),um]

end Manuscript.SKRestrictedOne
