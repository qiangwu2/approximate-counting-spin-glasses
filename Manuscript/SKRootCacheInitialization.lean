import Manuscript.SKRootCache

noncomputable section
namespace Manuscript.SKRootCache
open RestrictedMachine

def initPrelude : List Instruction := [.nconst 130 2,.ncopy 131 201]
def initCode : List Instruction :=
  [.nadd 233 230 200,.nconst 234 0,.nconst 235 1,.nmul 236 132 200,
   .nadd 238 232 200,.nadd 239 238 236,.nadd 240 239 236]
def initProgram : Program := .seq (code initPrelude)
  (.seq IndexGeneration.powerProgram (code initCode))
def program : Program := .seq initProgram (.repeat 233 body)

structure InputsReady (d : Layout) (χ : Fin d.N→Fin d.K)
    (w : Fin d.N→Fin d.N→ℝ) (branch : Fin d.B→Fin d.N→ℝ) (s : State) : Prop where
  size : s.natReg 200=d.N
  colors : s.natReg 201=d.K
  colorBase : s.natReg 204=d.colorBase
  weightBase : s.natReg 207=d.weightBase
  branches : s.natReg 230=d.B
  branchBase : s.natReg 231=d.branchBase
  arena : s.natReg 232=d.arena
  colorRead : ∀j,s.natMem (d.colorBase+j.val)=(χ j).val
  weightRead : ∀i j,s.realMem (d.weightBase+i.val*d.N+j.val)=w i j
  branchRead : ∀i j,s.realMem (d.branchBase+i.val*d.N+j.val)=branch i j

theorem initialize_execution (params : Parameters) (input : Inputs) (d : Layout)
    (χ : Fin d.N→Fin d.K) (w : Fin d.N→Fin d.N→ℝ) (branch : Fin d.B→Fin d.N→ℝ)
    (s : State) (hs : InputsReady d χ w branch s) :
    ∃c t,Exec params input initProgram s c t ∧ c≤9*d.K+31 ∧
      Invariant d χ w branch 0 t ∧ t.natMem=s.natMem ∧ t.realMem=s.realMem := by
  let a := runCode params input initPrelude s
  obtain ⟨cp,b,hp,bp,hv⟩ := IndexGeneration.power_execution params input a
  have bf (r : ℕ) (hr : r≠132) : b.natReg r=a.natReg r := by
    apply hp.natReg_frame
    simpa [IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
      code,Program.All,Instruction.natDestination,ne_comm] using hr
  have bm : b.realMem=s.realMem := by
    have hh := hp.realMem_frame (by simp [IndexGeneration.powerProgram,
      IndexGeneration.powerInit,IndexGeneration.powerBody,code,Program.All,Instruction.writesRealMemory])
    simpa [a,initPrelude,runCode,step] using hh
  have bn : b.natMem=s.natMem := by
    have hh := hp.natMem_frame (by simp [IndexGeneration.powerProgram,
      IndexGeneration.powerInit,IndexGeneration.powerBody,code,Program.All,Instruction.writesNatMemory])
    simpa [a,initPrelude,runCode,step] using hh
  have bv : b.natReg 132=2^d.K := by simpa [a,initPrelude,runCode,step,hs.colors] using hv
  have high (r : ℕ) (hr : 200≤r) : b.natReg r=s.natReg r := by
    rw [bf r (by omega)]
    have h130 : r≠130 := by omega
    have h131 : r≠131 := by omega
    simp [a,initPrelude,runCode,step,h130,h131]
  let t := runCode params input initCode b
  have tm : t.realMem=s.realMem := by simp [t,initCode,runCode,step,bm]
  have tn : t.natMem=s.natMem := by simp [t,initCode,runCode,step,bn]
  refine ⟨3+(cp+22),t,?_,?_,?_,tn,tm⟩
  · exact Exec.seq (exec_code params input initPrelude s)
      (Exec.seq hp (exec_code params input initCode b))
  · have hbp : cp≤9*d.K+6 := by simpa [a,initPrelude,runCode,step,hs.colors] using bp
    omega
  · refine ⟨?_,?_,?_,?_,?_⟩
    · constructor
      all_goals simp [t,initCode,runCode,step,bv,high 200 (by omega),high 201 (by omega),
        high 204 (by omega),high 207 (by omega),high 230 (by omega),high 231 (by omega),
        high 232 (by omega),hs.size,hs.colors,hs.colorBase,hs.weightBase,hs.branches,
        hs.branchBase,hs.arena,Layout.T,Layout.left,Layout.right,Layout.cache]
      <;> omega
    · intro j; rw [tn]; exact hs.colorRead j
    · intro i j; rw [tm]; exact hs.weightRead i j
    · intro i j; rw [tm]; exact hs.branchRead i j
    · intro a ha; omega

/-- The once-per-root cache is computed by one fixed RAM program. The only
initial arrays are prepared edge weights and colors; every start vector,
zero bank, memo layer and saved root table is produced by charged instructions. -/
theorem cache_execution (params : Parameters) (input : Inputs) (d : Layout)
    (χ : Fin d.N→Fin d.K) (w : Fin d.N→Fin d.N→ℝ) (branch : Fin d.B→Fin d.N→ℝ)
    (s : State) (hs : InputsReady d χ w branch s) :
    ∃c t,Exec params input program s c t ∧
      c≤9*d.K+36+(d.B+d.N)*(bodyCost d+5) ∧
      Invariant d χ w branch (d.B+d.N) t ∧ t.natMem=s.natMem ∧
      (∀a,a<d.arena → t.realMem a=s.realMem a) := by
  obtain ⟨ci,m,hi,bi,hm,hn,hmem⟩ := initialize_execution params input d χ w branch s hs
  obtain ⟨cl,t,hl,bl,ht,htn,htf⟩ := loop_execution params input d χ w branch (d.B+d.N) 0 m hm
  refine ⟨ci+(cl+2),t,?_,by omega,by simpa using ht,htn.trans hn,?_⟩
  · exact Exec.seq hi (Exec.repeat (by simpa only [hm.regs.roots] using hl))
  · intro a ha; rw [htf a ha,hmem]

end Manuscript.SKRootCache
