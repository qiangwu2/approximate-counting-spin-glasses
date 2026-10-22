import Manuscript.SKMemoLayers
import Manuscript.RestrictedArrays

/-! The initial zero table and its size are computed by actual instructions;
the memo engine does not receive a free zero-cache or a precomputed 2^K bound. -/
noncomputable section
namespace Manuscript.SKMemoInitialization
open RestrictedMachine SKMemoUpdate SKMemoPass SKMemoLayers

def preludeCode : List Instruction := [.nconst 130 2, .ncopy 131 201]
def setupCode : List Instruction :=
  [.nmul 220 132 200, .ncopy 10 205, .ncopy 11 205, .ncopy 12 205,
   .nconst 13 1, .ncopy 14 220, .rconst 4 0, .nconst 209 0, .nconst 222 1]
def program : Program := .seq (code preludeCode)
  (.seq IndexGeneration.powerProgram (.seq (code setupCode) (RestrictedArrays.program .fill)))
def fullProgram : Program := .seq program SKMemoLayers.program

structure InputsReady {N K : ℕ} (colorBase weightBase startBase : ℕ)
    (χ : Fin N → Fin K) (start : Fin N → ℝ) (w : Fin N → Fin N → ℝ) (s : State) : Prop where
  size : s.natReg 200=N
  colors : s.natReg 201=K
  colorBaseReg : s.natReg 204=colorBase
  weightBaseReg : s.natReg 207=weightBase
  startBaseReg : s.natReg 208=startBase
  separation : Separation N K (s.natReg 205) (s.natReg 206) weightBase startBase
  colorRead : ∀ j, s.natMem (colorBase+j.val)=(χ j).val
  weightRead : ∀ i j, s.realMem (weightBase+i.val*N+j.val)=w i j
  startRead : ∀ j, s.realMem (startBase+j.val)=start j

theorem outside_bank {N K base address : ℕ}
    (h : ∀ (S : Finset (Fin K)) (j : Fin N), address ≠ rowAddress N base S j.val) :
    ∀ i, i<2^K*N → address ≠ base+i := by
  intro i hi
  let p := (cellEquiv N K).symm ⟨i,hi⟩
  have hp : cellIndex p.1 p.2=i := by
    rw [cellIndex_eq]
    exact congrArg Fin.val ((cellEquiv N K).apply_symm_apply ⟨i,hi⟩)
  have hn := h p.1 p.2
  have heq : rowAddress N base p.1 p.2.val=base+cellIndex p.1 p.2 := by
    simp [rowAddress,cellIndex,Nat.add_assoc]
  rw [heq,hp] at hn
  exact hn

theorem initialized {N K : ℕ} (params : Parameters) (input : Inputs)
    (colorBase weightBase startBase : ℕ) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (s : State)
    (hs : InputsReady colorBase weightBase startBase χ start w s) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 9*K+30*(2^K*N)+30 ∧
      SKMemoLayers.Invariant colorBase weightBase startBase χ start w 0 t ∧ t.natMem=s.natMem ∧
      Banks s t ∧ SKMemoLayers.Frame N K s t := by
  let a := runCode params input preludeCode s
  obtain ⟨cp,b,hp,bp,vp⟩ := IndexGeneration.power_execution params input a
  have bf (r : ℕ) (hr : r ≠ 132) : b.natReg r=a.natReg r := by
    apply hp.natReg_frame
    simpa [IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
      code,Program.All,Instruction.natDestination,ne_comm] using hr
  have bm : b.realMem=s.realMem := by
    have hh := hp.realMem_frame (by
      simp [IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
        code,Program.All,Instruction.writesRealMemory])
    simpa [a,preludeCode,runCode,step] using hh
  have bn : b.natMem=s.natMem := by
    have hh := hp.natMem_frame (by
      simp [IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
        code,Program.All,Instruction.writesNatMemory])
    simpa [a,preludeCode,runCode,step] using hh
  have bv : b.natReg 132=2^K := by simpa [a,preludeCode,runCode,step,hs.colors] using vp
  let d := runCode params input setupCode b
  have df (r : ℕ) (hr : 200≤r ∧ r≤208) : d.natReg r=s.natReg r := by
    have hn : r ≠ 220 ∧ r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧
        r ≠ 209 ∧ r ≠ 222 ∧ r ≠ 130 ∧ r ≠ 131 := by omega
    simp [d,setupCode,runCode,step,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,
      hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.1,
      bf r (by omega),a,preludeCode,hn.2.2.2.2.2.2.2.2.1,hn.2.2.2.2.2.2.2.2.2]
  have dl : d.natReg 14=2^K*N := by
    simp [d,setupCode,runCode,step,bv,bf 200 (by omega),a,preludeCode,hs.size]
  have dp : d.natReg 10=s.natReg 205 ∧ d.natReg 11=s.natReg 205 ∧ d.natReg 12=s.natReg 205 := by
    simp [d,setupCode,runCode,step,bf 205 (by omega),a,preludeCode]
  have dz : d.realReg 4=0 := by simp [d,setupCode,runCode,step]
  have dm : d.realMem=s.realMem := by simp [d,setupCode,runCode,step,bm]
  have dn : d.natMem=s.natMem := by simp [d,setupCode,runCode,step,bn]
  have done : d.natReg 13=1 := by simp [d,setupCode,runCode,step]
  obtain ⟨cf,t,hf,bc,hi,hvalues⟩ := RestrictedArrays.pointwise_realized .fill params input d done (by
    intro i j _ hj
    rw [dp.1,dp.2.1,dp.2.2]
    constructor <;> omega)
  have tf (r : ℕ) (hr : r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 12) : t.natReg r=d.natReg r :=
    hi.2.2.2.2.2.1 r hr.1 hr.2.1 hr.2.2
  have tn : t.natMem=s.natMem := hi.2.1.trans dn
  have tm : t.realMem=RestrictedArrays.memoryLoop .fill 0 (s.natReg 205) (s.natReg 205)
      (s.natReg 205) (2^K*N) s.realMem := by
    simpa only [dz,dp.1,dp.2.1,dp.2.2,dl,dm] using hi.1
  have tbanks : Banks s t := by
    apply Or.inl
    rw [tf 205 (by omega),tf 206 (by omega),df 205 (by omega),df 206 (by omega)]
    exact ⟨rfl,rfl⟩
  have tframe : SKMemoLayers.Frame N K s t := by
    intro address haway
    rw [tm]
    exact RestrictedArrays.loop_frame _ _ _ _ _ _ _ _
      (outside_bank (fun S j => (haway S j).1))
  refine ⟨3+(cp+(16+cf)),t,?_,?_,?_,tn,tbanks,tframe⟩
  · exact Exec.seq (exec_code params input preludeCode s)
      (Exec.seq hp (Exec.seq (exec_code params input setupCode b) hf))
  · have bcp : cp≤9*K+6 := by simpa [a,preludeCode,runCode,step,hs.colors] using bp
    rw [dl] at bc
    omega
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [tf 200 (by omega),df 200 (by omega)]; exact hs.size
    · rw [tf 201 (by omega),df 201 (by omega)]; exact hs.colors
    · rw [tf 204 (by omega),df 204 (by omega)]; exact hs.colorBaseReg
    · rw [tf 207 (by omega),df 207 (by omega)]; exact hs.weightBaseReg
    · rw [tf 208 (by omega),df 208 (by omega)]; exact hs.startBaseReg
    · rw [tf 209 (by omega)]; simp [d,setupCode,runCode,step]
    · rw [tf 220 (by omega)]
      simp [d,setupCode,runCode,step,bv,bf 200 (by omega),a,preludeCode,hs.size]
    · rw [tf 222 (by omega)]; simp [d,setupCode,runCode,step]
    · rw [tf 205 (by omega),tf 206 (by omega),df 205 (by omega),df 206 (by omega)]
      exact hs.separation
    · intro j; rw [tn]; exact hs.colorRead j
    · intro S j
      rw [tf 205 (by omega),df 205 (by omega)]
      have hx := hvalues (cellIndex S j) (by rw [dl,cellIndex_eq]; exact (cellEquiv N K (S,j)).isLt)
      simpa [dp.2.2,dz,RestrictedArrays.Operation.eval,rowAddress,cellIndex,Nat.add_assoc,
        SpinGlass.ColorMemoExecution.memo] using hx
    · intro i j
      rw [tm,RestrictedArrays.loop_frame]
      · exact hs.weightRead i j
      · exact outside_bank (fun S k => (hs.separation.leftWeight S k i j).symm)
    · intro j
      rw [tm,RestrictedArrays.loop_frame]
      · exact hs.startRead j
      · exact outside_bank (fun S k => (hs.separation.leftStart S k j).symm)

/-- Uniform path-table computation from prepared source arrays, including
zero initialization, runtime state-space size generation, every cell, every
layer, and bank swaps. -/
theorem full_memo_realized {N K : ℕ} (params : Parameters) (input : Inputs)
    (colorBase weightBase startBase : ℕ) (χ : Fin N → Fin K) (start : Fin N → ℝ)
    (w : Fin N → Fin N → ℝ) (s : State)
    (hs : InputsReady colorBase weightBase startBase χ start w s) :
    ∃ count t, Exec params input fullProgram s count t ∧
      count ≤ 9*K+30*(2^K*N)+K*((2^K*N)*(38*K+27*N+137)+21)+35 ∧
      (∀ S j, t.realMem (rowAddress N (t.natReg 205) S j.val)=
        SpinGlass.ColorPath.pathTable χ start w S j) ∧ t.natMem=s.natMem ∧
      Banks s t ∧ SKMemoLayers.Frame N K s t := by
  obtain ⟨ci,m,he,bc,hm,hn,hbm,hfm⟩ := initialized params input colorBase weightBase startBase χ start w s hs
  obtain ⟨cm,t,het,bc',hvalue,_,hn',hbt,hft⟩ := SKMemoLayers.memo_realized params input colorBase weightBase startBase χ start w m hm
  exact ⟨ci+cm,t,Exec.seq he het,by omega,hvalue,hn'.trans hn,hbm.trans hbt,SKMemoLayers.Frame.trans hbm hfm hft⟩

/-- Registers used by the outer root-cache loop survive all initialization,
cell traversal, layer traversal and bank swaps. Register223 is swap scratch. -/
theorem full_natReg_frame (params : Parameters) (input : Inputs) (s t : State)
    (count r : ℕ) (h : Exec params input fullProgram s count t)
    (hr : r=200 ∨ r=201 ∨ r=204 ∨ r=207 ∨ r=208 ∨ 223<r) :
    t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [fullProgram,program,preludeCode,setupCode,IndexGeneration.powerProgram,
    IndexGeneration.powerInit,IndexGeneration.powerBody,RestrictedArrays.program,
    RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,SKMemoLayers.program,
    SKMemoLayers.body,SKMemoLayers.preludeCode,SKMemoLayers.tailCode,SKMemoPass.program,
    SKMemoPass.body,SKMemoPass.preludeCode,SKMemoPass.tailCode,SKMemoUpdate.program,
    SKMemoMetadata.program,SKMemoMetadata.preludeCode,SKMemoMetadata.middle,SKMemoMetadata.suffix,
    IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,
    SKRestrictedMemoCell.program,SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,
    code,Program.All,Instruction.natDestination]
  omega

end Manuscript.SKMemoInitialization
