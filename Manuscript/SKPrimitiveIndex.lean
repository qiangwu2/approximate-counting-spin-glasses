import Manuscript.SKPrimitiveInsert
import Manuscript.SKIndexSpecifications
import Manuscript.SKDirectIndex

/-! Uniform primitive-index construction from endpoint labels, the color
mask, and the actual stored endpoint charges. -/
noncomputable section
namespace Manuscript.SKPrimitiveIndex
open RestrictedMachine IndexGeneration SKBasisEncoding SKIndexSpecifications
open SpinGlass (CappedDegree)
open scoped BigOperators

def cardCode : List Instruction := [.ncopy 120 252,.ncopy 121 252,.ncopy 123 201]
def firstCode : List Instruction := [.nconst 130 6,.ncopy 131 250]
def secondCode : List Instruction := [.ncopy 281 132,.ncopy 131 251]
def pairFinish : List Instruction :=
  [.nadd 272 281 132,.nadd 283 282 250,.loadNat 284 283,
   .nadd 283 282 251,.loadNat 285 283,.nconst 286 1,
   .nsub 270 122 286,.nadd 270 270 284,.nadd 270 270 285,
   .neq 287 250 251,.nadd 287 286 287,.nle 288 287 122,
   .nle 289 250 251,.nmul 277 288 289,.ncopy 271 252]
def pairProgram : Program := .seq (code cardCode) (.seq overlapProgram
  (.seq (code firstCode) (.seq powerProgram
    (.seq (code secondCode) (.seq powerProgram (code pairFinish))))))
def cycleFinish : List Instruction :=
  [.ncopy 270 122,.ncopy 271 252,.nconst 272 0,.nconst 286 3,.nle 277 286 122]
def cycleProgram : Program := .seq (code cardCode) (.seq overlapProgram (code cycleFinish))

theorem path_degree_index {b : ℕ} (a c : Fin b) :
    (degreeEquiv b (SpinGlass.SKFastEvaluator.pathDegrees a c)).val=6^a.val+6^c.val := by
  by_cases hac : a=c
  · subst c
    rw [degree_formula]
    have ht (j : Fin b) : (SpinGlass.SKFastEvaluator.pathDegrees a a j).val*6^j.val=
        if j=a then 2*6^j.val else 0 := by
      by_cases hj : j=a <;> simp [SpinGlass.SKFastEvaluator.pathDegrees,hj,CappedDegree.val,CappedDegree.ofNat,SpinGlass.rho]
    simp_rw [ht]
    simp
    omega
  · exact SKDirectIndex.path_degree_index a c hac

theorem pair_realized (p : Parameters) (i : Inputs) (s : State) :
    ∃ count t, Exec p i pairProgram s count t ∧
      count≤29*s.natReg 201+9*(s.natReg 250+s.natReg 251)+85 ∧
      t.natReg 270=overlapFold (s.natReg 201) (s.natReg 252) (s.natReg 252) 0-1+
        s.natMem (s.natReg 282+s.natReg 250)+s.natMem (s.natReg 282+s.natReg 251) ∧
      t.natReg 271=s.natReg 252 ∧ t.natReg 272=6^s.natReg 250+6^s.natReg 251 ∧
      t.natReg 277=(if (if s.natReg 250=s.natReg 251 then 2 else 1)≤
        overlapFold (s.natReg 201) (s.natReg 252) (s.natReg 252) 0 ∧
        s.natReg 250≤s.natReg 251 then 1 else 0) ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem ∧ (∀ r,t.realReg r=s.realReg r) := by
  let a := runCode p i cardCode s
  obtain ⟨co,d,heo,bco,hcard⟩ := overlap_execution p i a
  have df (r) (hr : r<120 ∨ 127<r) := overlap_natReg_frame p i a d co r heo hr
  have dm := (overlap_memory_frame p i a d co heo).2
  let e := runCode p i firstCode d
  obtain ⟨c1,f,he1,bc1,hpow1⟩ := power_execution p i e
  have ff (r) (hr : r≠132) := (SKDirectIndex.power_frames p i he1).1 r hr
  have fm := (SKDirectIndex.power_frames p i he1).2.2
  let h := runCode p i secondCode f
  obtain ⟨c2,j,he2,bc2,hpow2⟩ := power_execution p i h
  have jf (r) (hr : r≠132) := (SKDirectIndex.power_frames p i he2).1 r hr
  have jm := (SKDirectIndex.power_frames p i he2).2.2
  have jp : j.natReg 132=6^s.natReg 251 := by
    simpa [h,secondCode,runCode,step,ff 130 (by omega),ff 251 (by omega),
      e,firstCode,df 251 (by omega),a,cardCode] using hpow2
  have jps : j.natReg 281=6^s.natReg 250 := by
    rw [jf 281 (by omega)]
    simpa [h,secondCode,runCode,step,e,firstCode,df 250 (by omega),a,cardCode] using hpow1
  have jcard : j.natReg 122=overlapFold (s.natReg 201) (s.natReg 252) (s.natReg 252) 0 := by
    rw [jf 122 (by omega)]
    simpa [h,secondCode,runCode,step,ff 122 (by omega),e,firstCode,a,cardCode] using hcard
  have jhigh (r : ℕ) (hr : 200≤r ∧ r≠281) : j.natReg r=s.natReg r := by
    rw [jf r (by omega)]
    have hne : r≠131 ∧ r≠130 ∧ r≠123 ∧ r≠121 ∧ r≠120 := by omega
    simp [h,secondCode,runCode,step,hr.2,hne.1,hne.2.1,hne.2.2.1,hne.2.2.2.1,hne.2.2.2.2,ff r (by omega),e,firstCode,
      df r (by omega),a,cardCode]
  have jmem : j.natMem=s.natMem := by simpa [h,secondCode,runCode,step,fm,e,firstCode,dm,a,cardCode] using jm
  let t := runCode p i pairFinish j
  have heall : Exec p i pairProgram s (6+(co+(3+(c1+(4+(c2+53)))))) t :=
    Exec.seq (exec_code p i cardCode s) (Exec.seq heo (Exec.seq (exec_code p i firstCode d)
      (Exec.seq he1 (Exec.seq (exec_code p i secondCode f) (Exec.seq he2 (exec_code p i pairFinish j))))))
  refine ⟨_,t,heall,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have b0 : co≤29*s.natReg 201+7 := by simpa [a,cardCode,runCode,step] using bco
    have b1 : c1≤9*s.natReg 250+6 := by simpa [e,firstCode,runCode,step,df 250 (by omega),a,cardCode] using bc1
    have b2 : c2≤9*s.natReg 251+6 := by simpa [h,secondCode,runCode,step,ff 251 (by omega),e,firstCode,df 251 (by omega),a,cardCode] using bc2
    omega
  · simp [t,pairFinish,runCode,step,jcard,jmem,jhigh 282 (by omega),jhigh 250 (by omega),jhigh 251 (by omega)]
  · simp [t,pairFinish,runCode,step,jhigh 252 (by omega)]
  · simp [t,pairFinish,runCode,step,jps,jp]
  · by_cases heq : s.natReg 250=s.natReg 251 <;>
      by_cases hle : s.natReg 250≤s.natReg 251 <;>
      simp [t,pairFinish,runCode,step,jcard,jhigh 250 (by omega),jhigh 251 (by omega),heq,hle]
  · apply heall.realMem_frame
    simp [pairProgram,cardCode,firstCode,secondCode,pairFinish,overlapProgram,overlapInit,overlapBody,powerProgram,powerInit,powerBody,code,Program.All,Instruction.writesRealMemory]
  · apply heall.natMem_frame
    simp [pairProgram,cardCode,firstCode,secondCode,pairFinish,overlapProgram,overlapInit,overlapBody,powerProgram,powerInit,powerBody,code,Program.All,Instruction.writesNatMemory]
  · intro r; apply heall.realReg_frame
    simp [pairProgram,cardCode,firstCode,secondCode,pairFinish,overlapProgram,overlapInit,overlapBody,powerProgram,powerInit,powerBody,code,Program.All,Instruction.realDestination]


theorem cycle_realized (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i cycleProgram s c t ∧ c≤29*s.natReg 201+23 ∧
      t.natReg 270=overlapFold (s.natReg 201) (s.natReg 252) (s.natReg 252) 0 ∧
      t.natReg 271=s.natReg 252 ∧ t.natReg 272=0 ∧
      t.natReg 277=(if 3≤overlapFold (s.natReg 201) (s.natReg 252) (s.natReg 252) 0 then 1 else 0) ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem ∧ (∀ r,t.realReg r=s.realReg r) := by
  let a := runCode p i cardCode s
  obtain ⟨c,d,he,bc,hv⟩ := overlap_execution p i a
  have df (r) (hr : r<120 ∨ 127<r) := overlap_natReg_frame p i a d c r he hr
  have hd : d.natReg 122=overlapFold (s.natReg 201) (s.natReg 252) (s.natReg 252) 0 := by
    simpa [a,cardCode,runCode,step] using hv
  let t := runCode p i cycleFinish d
  have heall : Exec p i cycleProgram s (6+(c+10)) t :=
    Exec.seq (exec_code p i cardCode s) (Exec.seq he (exec_code p i cycleFinish d))
  refine ⟨_,t,heall,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hc : c≤29*s.natReg 201+7 := by simpa [a,cardCode,runCode,step] using bc
    omega
  · simp [t,cycleFinish,runCode,step,hd]
  · simp [t,cycleFinish,runCode,step,df 252 (by omega),a,cardCode]
  · simp [t,cycleFinish,runCode,step]
  · simp [t,cycleFinish,runCode,step,hd]
  · apply heall.realMem_frame
    simp [cycleProgram,cardCode,cycleFinish,overlapProgram,overlapInit,overlapBody,code,Program.All,Instruction.writesRealMemory]
  · apply heall.natMem_frame
    simp [cycleProgram,cardCode,cycleFinish,overlapProgram,overlapInit,overlapBody,code,Program.All,Instruction.writesNatMemory]
  · intro r; apply heall.realReg_frame
    simp [cycleProgram,cardCode,cycleFinish,overlapProgram,overlapInit,overlapBody,code,Program.All,Instruction.realDestination]

theorem pair_natReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i pairProgram s c t)
    (hr : (132<r ∧ r<270) ∨ r=273 ∨ r=274 ∨ r=275 ∨ r=276 ∨ r=282 ∨ 289<r) :
    t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [pairProgram,cardCode,firstCode,secondCode,pairFinish,overlapProgram,overlapInit,overlapBody,
    powerProgram,powerInit,powerBody,code,Program.All,Instruction.natDestination]
  omega

theorem cycle_natReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i cycleProgram s c t)
    (hr : (127<r ∧ r<270) ∨ r=273 ∨ r=274 ∨ r=275 ∨ r=276 ∨ 286<r) :
    t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [cycleProgram,cardCode,cycleFinish,overlapProgram,overlapInit,overlapBody,code,Program.All,Instruction.natDestination]
  omega
end Manuscript.SKPrimitiveIndex
