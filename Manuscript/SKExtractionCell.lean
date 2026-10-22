import Manuscript.SKDegreeAcceptance
import Manuscript.SKColorCorrection
import Manuscript.SKIndexSpecifications

/-! A coefficient-extraction step computes its base-six acceptance test,
subset size, and exact color correction, and reads the actual coefficient. -/
noncomputable section
namespace Manuscript.SKExtractionCell
open RestrictedMachine IndexGeneration SKBasisEncoding SKIndexSpecifications
open SpinGlass (CappedDegree)
open SpinGlass.SKCoefficient (Basis)

def accepted {b : ℕ} (g : Fin b) : Finset (Fin b → CappedDegree) :=
  Finset.univ.filter (fun d => ∀ i, if i=g then
    d i=CappedDegree.ofNat 0 ∨ d i=CappedDegree.ofNat 2 ∨ d i=CappedDegree.ofNat 4
    else d i=CappedDegree.ofNat 4)

def decodeCode : List Instruction :=
  [.nmod 320 350 351,.ncopy 321 354,.ncopy 322 355,
   .ndiv 360 350 351,.nmod 120 360 352,.ncopy 121 120,.ncopy 123 353,
   .ndiv 360 360 352]
def correctionSetup : List Instruction := [.ncopy 300 353,.ncopy 301 122]
def preProgram : Program := .seq (code decodeCode) (.seq SKDegreeAcceptance.program
  (.seq overlapProgram (.seq (code correctionSetup) SKColorCorrection.program)))
def finishCode : List Instruction :=
  [.nconst 361 0,.neq 362 324 361,.nle 363 360 356,.nmul 362 362 363,
   .natToReal 305 362,.nadd 361 357 350,.loadReal 306 361,
   .rmul 306 304 306,.rmul 306 305 306,.radd 310 310 306,
   .nadd 350 350 359]
def program : Program := .seq preProgram (code finishCode)

structure Registers {b K : ℕ} (x : Basis b K) (g : Fin b) (L : ℕ) (s : State) : Prop where
  index : s.natReg 350=encode x
  degreeSize : s.natReg 351=6^b
  maskSize : s.natReg 352=2^K
  palette : s.natReg 353=K
  branches : s.natReg 354=b
  ghost : s.natReg 355=g.val
  retained : s.natReg 356=L
  one : s.natReg 359=1

theorem prefix_nat_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i preProgram s c t) (hr : 349<r ∧ r≠360) : t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [preProgram,decodeCode,correctionSetup,SKDegreeAcceptance.program,SKDegreeAcceptance.body,
    SKDegreeAcceptance.initCode,SKDegreeAcceptance.headCode,SKDegreeAcceptance.ghostCode,
    SKDegreeAcceptance.otherCode,SKDegreeAcceptance.tailCode,overlapProgram,overlapInit,overlapBody,
    SKColorCorrection.program,SKColorCorrection.setupCode,SKColorCorrection.bodyCode,
    code,Program.All,Instruction.natDestination]
  omega

theorem prefix_real_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i preProgram s c t) (hr : r<300 ∨ 304<r) : t.realReg r=s.realReg r := by
  apply h.realReg_frame
  simp [preProgram,decodeCode,correctionSetup,SKDegreeAcceptance.program,SKDegreeAcceptance.body,
    SKDegreeAcceptance.initCode,SKDegreeAcceptance.headCode,SKDegreeAcceptance.ghostCode,
    SKDegreeAcceptance.otherCode,SKDegreeAcceptance.tailCode,overlapProgram,overlapInit,overlapBody,
    SKColorCorrection.program,SKColorCorrection.setupCode,SKColorCorrection.bodyCode,
    code,Program.All,Instruction.realDestination]
  omega

theorem prefix_realized {b K : ℕ} (p : Parameters) (i : Inputs) (s : State)
    (x : Basis b K) (g : Fin b) (L : ℕ) (hs : Registers x g L s) :
    ∃ c t, Exec p i preProgram s c t ∧ c≤40*b+53*K+65 ∧
      t.natReg 360=x.1.val ∧
      (t.natReg 324=0 ↔ x.2.2 ∈ accepted g) ∧
      t.realReg 304=(SpinGlass.ColoringProbability.probability K x.2.1.card)⁻¹ ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let a := runCode p i decodeCode s
  have ha320 : a.natReg 320=(degreeEquiv b x.2.2).val := by
    simp [a,decodeCode,runCode,step,hs.index,hs.degreeSize,encode_mod_degree]
  have ha321 : a.natReg 321=b := by simp [a,decodeCode,runCode,step,hs.branches]
  have ha322 : a.natReg 322=g.val := by simp [a,decodeCode,runCode,step,hs.ghost]
  have ha120 : a.natReg 120=(maskEquiv K x.2.1).val := by
    simp [a,decodeCode,runCode,step,hs.index,hs.degreeSize,hs.maskSize,encode_mask]
  have ha121 : a.natReg 121=(maskEquiv K x.2.1).val := by
    simp [a,decodeCode,runCode,step,hs.index,hs.degreeSize,hs.maskSize,encode_mask]
  have ha123 : a.natReg 123=K := by simp [a,decodeCode,runCode,step,hs.palette]
  have ha360 : a.natReg 360=x.1.val := by
    simp [a,decodeCode,runCode,step,hs.index,hs.degreeSize,hs.maskSize,encode_charge]
  obtain ⟨ca,d,hea,bca,hda⟩ := SKDegreeAcceptance.acceptance_realized p i a
  have hd324 : d.natReg 324=0 ↔ x.2.2∈accepted g := by
    rw [hda,ha321,ha320,ha322,SKDegreeAcceptance.encoded_acceptance_iff]
    simp [accepted]
  have df (r) (hr : r<320 ∨ 334<r ∨ r=321 ∨ r=322) := SKDegreeAcceptance.natReg_frame hea hr
  obtain ⟨co,e,heo,bco,hcard⟩ := overlap_execution p i d
  have hecard : e.natReg 122=x.2.1.card := by
    rw [hcard,df 123 (by omega),df 120 (by omega),df 121 (by omega),ha123,ha120,ha121]
    exact overlapFold_self x.2.1
  have ef (r) (hr : r<120 ∨ 127<r) := overlap_natReg_frame p i d e co r heo hr
  let f := runCode p i correctionSetup e
  have hf300 : f.natReg 300=K := by
    simp [f,correctionSetup,runCode,step,ef 353 (by omega),df 353 (by omega),a,decodeCode,hs.palette]
  have hf301 : f.natReg 301=x.2.1.card := by simp [f,correctionSetup,runCode,step,hecard]
  obtain ⟨t,het,hv,htm,htn⟩ := SKColorCorrection.correction_realized p i f
  have tf (r) (hr : r≠302 ∧ r≠303 ∧ r≠304) := SKColorCorrection.natReg_frame het hr
  have heall : Exec p i preProgram s (24+(ca+(co+(4+(24*f.natReg 301+16))))) t := by
    exact Exec.seq (exec_code p i decodeCode s) (Exec.seq hea
      (Exec.seq heo (Exec.seq (exec_code p i correctionSetup e) het)))
  refine ⟨_,t,heall,?_,?_,?_,?_,?_,?_⟩
  · have hca : ca≤40*b+12 := by simpa [ha321] using bca
    have hco : co≤29*K+7 := by simpa [df 123 (by omega),ha123] using bco
    have hm : x.2.1.card≤K := by simpa using Finset.card_le_univ x.2.1
    rw [hf301]; omega
  · rw [tf 360 (by omega)]
    simpa [f,correctionSetup,runCode,step,ef 360 (by omega),df 360 (by omega)] using ha360
  · rw [tf 324 (by omega)]
    simpa [f,correctionSetup,runCode,step,ef 324 (by omega)] using hd324
  · simpa [hf300,hf301] using hv
  · rw [htm]
    simp only [f,correctionSetup,runCode,step,writeNatReg_realMem]
    rw [(overlap_memory_frame p i d e co heo).1,(SKDegreeAcceptance.memory_frame hea).1]
    simp [a,decodeCode,runCode,step]
  · rw [htn]
    simp only [f,correctionSetup,runCode,step,writeNatReg_natMem]
    rw [(overlap_memory_frame p i d e co heo).2,(SKDegreeAcceptance.memory_frame hea).2]
    simp [a,decodeCode,runCode,step]

theorem cell_realized {b K : ℕ} (p : Parameters) (i : Inputs) (s : State)
    (x : Basis b K) (g : Fin b) (L : ℕ) (hs : Registers x g L s) :
    ∃ c t, Exec p i program s c t ∧ c≤40*b+53*K+105 ∧
      t.natReg 350=s.natReg 350+1 ∧
      t.realReg 310=s.realReg 310+(if x.1.val≤L ∧ x.2.2∈accepted g then
        (SpinGlass.ColoringProbability.probability K x.2.1.card)⁻¹*s.realMem (s.natReg 357+encode x) else 0) ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  obtain ⟨c,a,he,bc,hcharge,haccept,hvalue,hm,hn⟩ := prefix_realized p i s x g L hs
  let t := runCode p i finishCode a
  have hf (r) (hr : 349<r ∧ r≠360) := prefix_nat_frame he hr
  have hr := prefix_real_frame he (show 310<300 ∨ 304<310 by omega)
  have heall : Exec p i program s (c+39) t := by
    exact Exec.seq he (exec_code p i finishCode a)
  refine ⟨_,t,heall,by omega,?_,?_,?_,?_⟩
  · simp [t,finishCode,runCode,step,hf 350 (by omega),hf 359 (by omega),hs.one]
  · by_cases ha : x.2.2∈accepted g <;> by_cases hc : x.1.val≤L
    all_goals have hh : (a.natReg 324=0) ↔ x.2.2∈accepted g := haccept
    all_goals simp [t,finishCode,runCode,step,hf 350 (by omega),hf 356 (by omega),
      hf 357 (by omega),hs.index,hs.retained,hcharge,hvalue,hm,hr,hh,ha,hc]
  · simp [t,finishCode,runCode,step,hm]
  · simp [t,finishCode,runCode,step,hn]

theorem natReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i program s c t) (hr : 350<r ∧ r≠360 ∧ r≠361 ∧ r≠362 ∧ r≠363) :
    t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [program,preProgram,decodeCode,finishCode,correctionSetup,SKDegreeAcceptance.program,SKDegreeAcceptance.body,
    SKDegreeAcceptance.initCode,SKDegreeAcceptance.headCode,SKDegreeAcceptance.ghostCode,
    SKDegreeAcceptance.otherCode,SKDegreeAcceptance.tailCode,overlapProgram,overlapInit,overlapBody,
    SKColorCorrection.program,SKColorCorrection.setupCode,SKColorCorrection.bodyCode,
    code,Program.All,Instruction.natDestination]
  omega
end Manuscript.SKExtractionCell
