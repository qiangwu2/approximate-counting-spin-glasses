import Manuscript.RestrictedHigherLayer
import Manuscript.RestrictedRecursiveFrames

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace Manuscript.RestrictedLayerProgram
open RestrictedMachine RestrictedLocalSum RestrictedHigherLayer

/-- Parameters N,k,s and disjoint support scratch are held in
282,310,311,312. The physical data fields use the local evaluator layout. -/
def setupCode : List Instruction :=
  [.ncopy 70 282,.ncopy 71 310,.ncopy 72 311,
   .ncopy 200 282,.ncopy 201 311,.ncopy 204 312]
def storeCode : List Instruction := [.rcopy 310 80]
def initCode : List Instruction :=
  [.nsub 313 204 312,.ncopy 300 204,.rconst 311 0,.nconst 314 0,.nconst 315 1]
def program : RestrictedRecursiveMachine.Program 2 :=
  .seq (.base (code setupCode))
    (.seq (.base RestrictedCoefficients.coefficientProgram)
      (.seq (.base (code storeCode))
        (.seq (RestrictedSubsets.program.rename subsetId)
          (.seq (.base (code initCode)) (.repeat 313 RestrictedHigherLayer.body)))))

def masks (s : State) : List ℕ := RestrictedSubsets.masks (s.natReg 282) (s.natReg 311) 0 1

def layerData (s : State) : Data :=
  {data s with
    spinBase:=s.natReg 312+(masks s).length
    natMemory:=RestrictedSubsets.writeList s.natMem (s.natReg 312) (masks s)}

def coefficient (s : State) : ℝ :=
  SupportEvaluation.coefficient (s.natReg 282) (s.natReg 310) (s.natReg 311)
def cost (s : State) : ℕ :=
  31*(s.natReg 310-s.natReg 311)+RestrictedSubsets.work (s.natReg 282) (s.natReg 311)+
    workSupports (visible (layerData s)) (s.natReg 312) 0 (masks s).length+64

theorem program_realized (params : Parameters) (input : Inputs) (s : State)
    (hspace : s.natReg 284+s.natReg 283≤s.natReg 312) :
    ∃ final, RestrictedRecursiveMachine.Exec table params input program s (cost s) final ∧
      final.realReg 311=sumSupports (visible (layerData s)) (coefficient s)
        (s.natReg 312) 0 (masks s).length ∧
      visible (data final)=visible (layerData s) ∧
      (∀ r, 310≤r → r≠313 → r≠314 → r≠315 → r≠316 → final.natReg r=s.natReg r) := by
  let start := runCode params input setupCode s
  obtain ⟨coeff,hcoeff,hvalue⟩ := RestrictedCoefficients.coefficient_realized params input start
  have hn (r : ℕ) (hr : 200≤r) : coeff.natReg r=start.natReg r := by
    apply hcoeff.natReg_frame
    simp [RestrictedCoefficients.coefficientProgram,RestrictedCoefficients.initCode,
      RestrictedCoefficients.bodyCode,code,Program.All,Instruction.natDestination]
    omega
  have hr (r : ℕ) (hr : 200≤r) : coeff.realReg r=start.realReg r := by
    apply hcoeff.realReg_frame
    simp [RestrictedCoefficients.coefficientProgram,RestrictedCoefficients.initCode,
      RestrictedCoefficients.bodyCode,code,Program.All,Instruction.realDestination]
    omega
  have hnm : coeff.natMem=s.natMem := by
    have hh := hcoeff.natMem_frame (by
      simp [RestrictedCoefficients.coefficientProgram,RestrictedCoefficients.initCode,
        RestrictedCoefficients.bodyCode,code,Program.All,Instruction.writesNatMemory])
    exact hh
  have hrm : coeff.realMem=s.realMem := by
    have hh := hcoeff.realMem_frame (by
      simp [RestrictedCoefficients.coefficientProgram,RestrictedCoefficients.initCode,
        RestrictedCoefficients.bodyCode,code,Program.All,Instruction.writesRealMemory])
    exact hh
  let stored := runCode params input storeCode coeff
  let generated := RestrictedSubsets.output
    (runCode params input RestrictedSubsets.initCode stored) (masks s)
  have hgen := (RestrictedSubsets.program_exact params input stored).rename subsetId table subset_table
  have hgen' : RestrictedRecursiveMachine.Exec table params input
      (RestrictedSubsets.program.rename subsetId) stored
      (5+RestrictedSubsets.work (s.natReg 282) (s.natReg 311)) generated := by
    simpa [stored,storeCode,runCode,step,hn,start,setupCode,masks,generated] using hgen
  let ready := runCode params input initCode generated
  have hready : data ready=layerData s := by
    simp [ready,initCode,generated,RestrictedSubsets.output,RestrictedSubsets.initCode,
      stored,storeCode,runCode,step,data,layerData,hn,hr,hnm,hrm,start,setupCode]
  have hregs (r : ℕ) (h : 310≤r) : ready.natReg r=
      if r=313 then (masks s).length else if r=314 then 0 else if r=315 then 1 else s.natReg r := by
    have hlarge : 200≤r := by omega
    simp [ready,initCode,generated,RestrictedSubsets.output,RestrictedSubsets.initCode,
      stored,storeCode,runCode,step,Function.update_apply,hn,hlarge,start,setupCode,
      show r≠300 by omega,show r≠204 by omega,show r≠207 by omega,show r≠206 by omega,show r≠205 by omega,show r≠203 by omega,show r≠202 by omega,show r≠201 by omega,show r≠200 by omega,show r≠72 by omega,show r≠71 by omega,show r≠70 by omega]
    split_ifs <;> omega
  have hc : ready.realReg 310=coefficient s := by
    simpa [ready,initCode,generated,RestrictedSubsets.output,RestrictedSubsets.initCode,
      stored,storeCode,runCode,step,coefficient,start,setupCode] using hvalue
  have hzero : ready.realReg 311=0 := by simp [ready,initCode,runCode,step]
  have hs : (data ready).edgeBase+(data ready).M≤(data ready).spinBase := by
    rw [hready]; dsimp [layerData,data]; omega
  have hb : ready.natReg 312+ready.natReg 314+(masks s).length≤(data ready).spinBase := by
    rw [hready,hregs 312 (by omega),hregs 314 (by omega)]
    simp [layerData]
  obtain ⟨final,he,hv,hi,hd,hf,hc'⟩ := RestrictedHigherLayer.body_repeats params input
    (masks s).length ready (by simp [hregs]) hs hb
  have he' : RestrictedRecursiveMachine.Repeats table params input RestrictedHigherLayer.body
      (ready.natReg 313) ready
      (workSupports (visible (data ready)) (ready.natReg 312) (ready.natReg 314) (masks s).length+3) final := by
    simpa [hregs] using he
  have hloop := RestrictedRecursiveMachine.Exec.repeat he'
  refine ⟨final,?_,?_,hd.trans (congrArg visible hready),?_⟩
  · have hh := RestrictedRecursiveMachine.Exec.seq
      (RestrictedRecursiveMachine.Exec.base (exec_code params input setupCode s))
      (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hcoeff)
        (RestrictedRecursiveMachine.Exec.seq
          (RestrictedRecursiveMachine.Exec.base (exec_code params input storeCode coeff))
          (RestrictedRecursiveMachine.Exec.seq hgen'
            (RestrictedRecursiveMachine.Exec.seq
              (RestrictedRecursiveMachine.Exec.base (exec_code params input initCode generated)) hloop))))
    convert hh using 1
    · rfl
    · simp [cost,setupCode,storeCode,initCode,codeCost,instrCost,start,runCode,step,hready,hregs]
      omega
  · simpa [hready,hc,hzero,hregs] using hv
  · intro r hlow h313 h314 h315 h316
    rw [hf r hlow h314 h316,hregs r hlow]
    simp [h313,h314,h315]

theorem nat_frame {params : Parameters} {input : Inputs} {s t : State} {c r : ℕ}
    (he : RestrictedRecursiveMachine.Exec table params input program s c t) (hr : 320≤r) :
    t.natReg r=s.natReg r := by
  apply he.natReg_frame
  · simp [program,setupCode,storeCode,initCode,
      RestrictedCoefficients.coefficientProgram,RestrictedCoefficients.initCode,RestrictedCoefficients.bodyCode,
      RestrictedSubsets.program,RestrictedSubsets.initCode,
      RestrictedHigherLayer.body,RestrictedHigherLayer.prefixCode,RestrictedHigherLayer.suffixCode,
      RestrictedLocalEvaluation.program,RestrictedLocalEvaluation.prefixCode,RestrictedLocalEvaluation.suffixCode,
      RestrictedCubes.program,RestrictedCubes.initCode,
      RestrictedLocalSum.program,RestrictedLocalSum.initCode,RestrictedLocalSum.body,
      RestrictedLocalSum.prefixCode,RestrictedLocalSum.suffixCode,
      RestrictedSpinTerm.program,RestrictedSpinTerm.fieldPrefix,RestrictedSpinTerm.fieldSuffix,
      RestrictedSpinTerm.edgeBody,RestrictedSpinTerm.edgePrefix,RestrictedSpinTerm.edgeSuffix,
      RestrictedMaskArithmetic.characterProgram,RestrictedMaskArithmetic.fieldProgram,
      RestrictedMaskArithmetic.initCode,RestrictedMaskArithmetic.characterBody,RestrictedMaskArithmetic.fieldBody,
      RestrictedRecursiveMachine.Program.rename,RestrictedRecursiveMachine.Program.All,code,Program.All,Instruction.natDestination]
    omega
  · intro id
    simp [table,RestrictedSubsets.procedure,RestrictedSubsets.recursiveBody,
      RestrictedSubsets.firstCode,RestrictedSubsets.secondCode,RestrictedSubsets.leafCode,
      RestrictedSubsets.beforeCode,RestrictedSubsets.betweenCode,
      RestrictedCubes.procedure,RestrictedCubes.recursiveBody,RestrictedCubes.firstCode,
      RestrictedCubes.leafCode,RestrictedCubes.beforeCode,RestrictedCubes.betweenCode,
      RestrictedRecursiveMachine.Procedure.rename,RestrictedRecursiveMachine.Program.rename,
      RestrictedRecursiveMachine.Program.All,code,Program.All,Instruction.natDestination]
    split_ifs <;> simp_all [RestrictedRecursiveMachine.Program.All,Program.All] <;> omega

theorem real_frame {params : Parameters} {input : Inputs} {s t : State} {c r : ℕ}
    (he : RestrictedRecursiveMachine.Exec table params input program s c t) (hr : 320≤r) :
    t.realReg r=s.realReg r := by
  apply he.realReg_frame
  · simp [program,setupCode,storeCode,initCode,
      RestrictedCoefficients.coefficientProgram,RestrictedCoefficients.initCode,RestrictedCoefficients.bodyCode,
      RestrictedSubsets.program,RestrictedSubsets.initCode,
      RestrictedHigherLayer.body,RestrictedHigherLayer.prefixCode,RestrictedHigherLayer.suffixCode,
      RestrictedLocalEvaluation.program,RestrictedLocalEvaluation.prefixCode,RestrictedLocalEvaluation.suffixCode,
      RestrictedCubes.program,RestrictedCubes.initCode,
      RestrictedLocalSum.program,RestrictedLocalSum.initCode,RestrictedLocalSum.body,
      RestrictedLocalSum.prefixCode,RestrictedLocalSum.suffixCode,
      RestrictedSpinTerm.program,RestrictedSpinTerm.fieldPrefix,RestrictedSpinTerm.fieldSuffix,
      RestrictedSpinTerm.edgeBody,RestrictedSpinTerm.edgePrefix,RestrictedSpinTerm.edgeSuffix,
      RestrictedMaskArithmetic.characterProgram,RestrictedMaskArithmetic.fieldProgram,
      RestrictedMaskArithmetic.initCode,RestrictedMaskArithmetic.characterBody,RestrictedMaskArithmetic.fieldBody,
      RestrictedRecursiveMachine.Program.rename,RestrictedRecursiveMachine.Program.All,code,Program.All,Instruction.realDestination]
    omega
  · intro id
    simp [table,RestrictedSubsets.procedure,RestrictedSubsets.recursiveBody,
      RestrictedSubsets.firstCode,RestrictedSubsets.secondCode,RestrictedSubsets.leafCode,
      RestrictedSubsets.beforeCode,RestrictedSubsets.betweenCode,
      RestrictedCubes.procedure,RestrictedCubes.recursiveBody,RestrictedCubes.firstCode,
      RestrictedCubes.leafCode,RestrictedCubes.beforeCode,RestrictedCubes.betweenCode,
      RestrictedRecursiveMachine.Procedure.rename,RestrictedRecursiveMachine.Program.rename,
      RestrictedRecursiveMachine.Program.All,code,Program.All,Instruction.realDestination]
    split_ifs <;> simp_all [RestrictedRecursiveMachine.Program.All,Program.All] <;> omega

theorem realMem_frame {params : Parameters} {input : Inputs} {s t : State} {c : ℕ}
    (he : RestrictedRecursiveMachine.Exec table params input program s c t) :
    t.realMem=s.realMem := by
  apply he.realMem_frame
  · simp [program,setupCode,storeCode,initCode,
      RestrictedCoefficients.coefficientProgram,RestrictedCoefficients.initCode,RestrictedCoefficients.bodyCode,
      RestrictedSubsets.program,RestrictedSubsets.initCode,
      RestrictedHigherLayer.body,RestrictedHigherLayer.prefixCode,RestrictedHigherLayer.suffixCode,
      RestrictedLocalEvaluation.program,RestrictedLocalEvaluation.prefixCode,RestrictedLocalEvaluation.suffixCode,
      RestrictedCubes.program,RestrictedCubes.initCode,
      RestrictedLocalSum.program,RestrictedLocalSum.initCode,RestrictedLocalSum.body,
      RestrictedLocalSum.prefixCode,RestrictedLocalSum.suffixCode,
      RestrictedSpinTerm.program,RestrictedSpinTerm.fieldPrefix,RestrictedSpinTerm.fieldSuffix,
      RestrictedSpinTerm.edgeBody,RestrictedSpinTerm.edgePrefix,RestrictedSpinTerm.edgeSuffix,
      RestrictedMaskArithmetic.characterProgram,RestrictedMaskArithmetic.fieldProgram,
      RestrictedMaskArithmetic.initCode,RestrictedMaskArithmetic.characterBody,RestrictedMaskArithmetic.fieldBody,
      RestrictedRecursiveMachine.Program.rename,RestrictedRecursiveMachine.Program.All,code,Program.All,Instruction.writesRealMemory]
  · intro id
    simp [table,RestrictedSubsets.procedure,RestrictedSubsets.recursiveBody,
      RestrictedSubsets.firstCode,RestrictedSubsets.secondCode,RestrictedSubsets.leafCode,
      RestrictedSubsets.beforeCode,RestrictedSubsets.betweenCode,
      RestrictedCubes.procedure,RestrictedCubes.recursiveBody,RestrictedCubes.firstCode,
      RestrictedCubes.leafCode,RestrictedCubes.beforeCode,RestrictedCubes.betweenCode,
      RestrictedRecursiveMachine.Procedure.rename,RestrictedRecursiveMachine.Program.rename,
      RestrictedRecursiveMachine.Program.All,code,Program.All,Instruction.writesRealMemory]
    split_ifs <;> simp_all [RestrictedRecursiveMachine.Program.All,Program.All]

end Manuscript.RestrictedLayerProgram
