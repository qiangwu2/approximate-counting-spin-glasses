import Manuscript.SKRestrictedArrays

noncomputable section
namespace Manuscript.SKRestrictedMultiply
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays
open SKRestrictedAlgebra SKRestrictedScatter

def clearSetup : List Instruction :=
  [.ncopy 10 30, .nadd 10 10 31, .nadd 10 10 31,
   .ncopy 11 10, .ncopy 12 10, .ncopy 13 36, .ncopy 14 31, .rconst 4 0]
def scatterSetup : List Instruction := [.ncopy 4 33, .ncopy 5 32, .ncopy 6 36]
def program : Program := .seq (code clearSetup) (.seq (RestrictedArrays.program .fill)
  (.seq (code scatterSetup) SKRestrictedScatter.program))

theorem schedule_outside {b K : ℕ} (layout : Layout b K) (metadata : ℕ → ℕ)
    (pairs : List (Basis b K × Basis b K)) (p : ℕ) (memory : ℕ → ℝ)
    (hm : ScheduleMatches layout metadata p pairs) (address : ℕ)
    (ha : ∀ x, address ≠ layout.out x) :
    memoryLoop metadata p pairs.length memory address=memory address := by
  rw [← memoryRun_eq_loop]
  induction pairs generalizing p memory with
  | nil => rfl
  | cons pair pairs ih =>
    obtain ⟨hfirst,hrest⟩ := hm
    rw [List.length_cons,memoryRun,ih _ _ hrest]
    cases he : basisMul pair.1 pair.2 with
    | none =>
      have hz : metadata p=0 := by simpa [RecordMatches,he] using hfirst
      simp [memoryStep,hz]
    | some z =>
      obtain ⟨hn,_,_,ho⟩ : metadata p ≠ 0 ∧ metadata (p+1)=layout.left pair.1 ∧
          metadata (p+2)=layout.right pair.2 ∧ metadata (p+3)=layout.out z := by
        simpa [RecordMatches,he] using hfirst
      simp [memoryStep,hn,ho,Function.update_of_ne (ha z)]

theorem program_frame (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input program s c t) :
    (∀ r, 15 ≤ r → t.natReg r=s.natReg r) ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_⟩
  · intro r hr
    apply he.natReg_frame
    simp [program,clearSetup,scatterSetup,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,SKRestrictedScatter.program,body,header,
      SKRestrictedKernels.accumulateBody,code,Program.All,Instruction.natDestination]
    omega
  · apply he.natMem_frame
    simp [program,clearSetup,scatterSetup,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,SKRestrictedScatter.program,body,header,
      SKRestrictedKernels.accumulateBody,code,Program.All,Instruction.writesNatMemory]

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset : ℕ) (f g : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hmeta : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1)
    (hf : SKRestrictedArrays.Represents base f s.realMem)
    (hg : SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) g s.realMem)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K)) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 56*((K+1)*2^K*6^b)^2+30*((K+1)*2^K*6^b)+35 ∧
      SKRestrictedAlgebra.Represents (denseLayout b K base) f g (SKCoefficient.mul f g) t.realMem ∧
      (∀ address, (∀ i, i < (K+1)*2^K*6^b → address ≠ base+2*((K+1)*2^K*6^b)+i) →
        t.realMem address=s.realMem address) := by
  let M := (K+1)*2^K*6^b
  let u := runCode params input clearSetup s
  have hu : Exec params input (code clearSetup) s 19 u := by
    convert exec_code params input clearSetup s using 1
    norm_num [clearSetup,codeCost,instrCost]
  have um : u.realMem=s.realMem := by simp [u,clearSetup,runCode,step]
  have unm : u.natMem=s.natMem := by simp [u,clearSetup,runCode,step]
  have un (r : ℕ) (hr : 15 ≤ r) : u.natReg r=s.natReg r := by
    apply hu.natReg_frame
    simp [clearSetup,code,Program.All,Instruction.natDestination]; omega
  have uout : u.natReg 12=base+2*M := by simp [u,clearSetup,runCode,step,hbase,hM,M]; omega
  have ulength : u.natReg 14=M := by simp [u,clearSetup,runCode,step,hM,M]
  obtain ⟨c₁,v,hv,bc₁,vzero,vi⟩ := fill_array (b:=b) (K:=K) params input u (base+2*M)
    (by simp [u,clearSetup,runCode,step,hbase,hM,M]; omega)
    (by simp [u,clearSetup,runCode,step,hbase,hM,M]; omega)
    uout (by simp [u,clearSetup,runCode,step,hone]) ulength
  have vn (r : ℕ) (hr : 15 ≤ r) : v.natReg r=s.natReg r :=
    ((array_frame .fill params input hv).1 r hr).trans (un r hr)
  have vmem (address : ℕ) (ha : ∀ i, i < M → address ≠ base+2*M+i) :
      v.realMem address=s.realMem address := by
    rw [preserved_outside .fill params input vi address (by simpa only [uout,ulength] using ha),um]
  have vnm : v.natMem=s.natMem := ((array_frame .fill params input hv).2.2).trans unm
  let w := runCode params input scatterSetup v
  have hw : Exec params input (code scatterSetup) v 6 w := exec_code _ _ _ _
  have wm : w.realMem=v.realMem := rfl
  have wnm : w.natMem=s.natMem := vnm
  have wptr : w.natReg 5=offset := by simp [w,scatterSetup,runCode,step,vn 32 (by omega),hmeta]
  have wcount : w.natReg 4=M^2 := by simp [w,scatterSetup,runCode,step,vn 33 (by omega),hpairs,M]
  have wone : w.natReg 6=1 := by simp [w,scatterSetup,runCode,step,vn 36 (by omega),hone]
  obtain ⟨c₂,t,ht,bc₂,ti⟩ := SKRestrictedScatter.program_realized params input w wone
  have plen : (pairList b K).length=M^2 := by
    have hh := (pairList_permutation b K).length_eq
    simpa [Finset.length_toList,Finset.card_univ,Fintype.card_prod,card_basis,pow_two,M,Nat.mul_assoc] using hh
  have wrep : SKRestrictedAlgebra.Represents (denseLayout b K base) f g 0 w.realMem := by
    refine ⟨?_,?_,?_⟩
    · intro x
      change v.realMem (base+encode x)=f x
      rw [vmem _ (by intro i hi; have hx:=encode_lt x; dsimp [M] at *; omega)]
      exact hf x
    · intro x
      change v.realMem (base+M+encode x)=g x
      rw [vmem _ (by intro i hi; have hx:=encode_lt x; dsimp [M] at *; omega)]
      exact hg x
    · intro x
      change v.realMem (base+2*M+encode x)=0
      simpa [u,clearSetup,runCode,step] using vzero x
  have hval : SKDenseExecution.pushLoop f g (pairList b K) 0=SKCoefficient.mul f g := by
    rw [← SKDenseExecution.denseMul_correct,SKDenseExecution.denseMul,
      SKDenseExecution.pushLoop_correct,SKDenseExecution.pushLoop_correct]
    rw [((pairList_permutation b K).map (fun p => fun z => pairContribution p.1 p.2 z (f p.1) (g p.2))).sum_eq]
  have trep := schedule_represents (denseLayout b K base) f g s.natMem
    (pairList b K) offset 0 w.realMem wrep hrecords
  rw [hval,plen] at trep
  refine ⟨19+(c₁+(6+c₂)),t,Exec.seq hu (Exec.seq hv (Exec.seq hw ht)),?_,?_,?_⟩
  · rw [wcount] at bc₂; dsimp [M] at *; omega
  · rw [ti.1,wnm,wptr,wcount]; exact trep
  · intro address ha
    rw [ti.1,wnm,wptr,wcount,← plen]
    rw [schedule_outside (denseLayout b K base) s.natMem (pairList b K) offset w.realMem
      hrecords address (fun x => ha (encode x) (encode_lt x)),wm]
    exact vmem address ha

end Manuscript.SKRestrictedMultiply
