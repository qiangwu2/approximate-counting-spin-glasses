import Manuscript.RestrictedScalars
import Manuscript.RestrictedFrames

noncomputable section
namespace Manuscript.RestrictedInputScalars
open RestrictedMachine InputPreparation

def readCode (budgetBase : ℕ) : List Instruction :=
  [.nconst 0 0,.nconst 1 1,.readNatInput 500 0,.readNatInput 501 1,
   .nconst 2 1,.nadd 3 501 2,.readRealInput 500 3,
   .nadd 3 3 2,.readRealInput 501 3,.nadd 3 3 2,.readRealInput 502 3,
   .readRealInput 503 0,.nconst 4 budgetBase,.readParam 0 4,
   .nconst 4 (budgetBase+1),.readParam 3 4,.rcopy 1 502,.rcopy 2 501]
def budgetSave : List Instruction := [.rcopy 508 19,.rcopy 509 14]
def fieldSetup : List Instruction := [.natToReal 0 500,.rcopy 1 500]
def fieldSave : List Instruction := [.rcopy 504 16,.rcopy 505 18,.rcopy 506 23,.rcopy 507 25]
def scalarCode (budgetBase : ℕ) : List Instruction := readCode budgetBase ++
  RestrictedScalars.budgetCode ++ budgetSave ++ fieldSetup ++ RestrictedScalars.fieldCode ++ fieldSave

def budget (params : Parameters) (input : Inputs) (budgetBase : ℕ) : Budget :=
  prepareBudget (params budgetBase) (input.real (input.nat 1+3))
    (input.real (input.nat 1+2)) (params (budgetBase+1))

def Ready (params : Parameters) (input : Inputs) (budgetBase : ℕ) (s : State) : Prop :=
  s.natReg 500=input.nat 0 ∧ s.natReg 501=input.nat 1 ∧
  s.realReg 500=input.real (input.nat 1+1) ∧
  s.realReg 501=input.real (input.nat 1+2) ∧
  s.realReg 502=input.real (input.nat 1+3) ∧ s.realReg 503=input.real 0 ∧
  s.realReg 504=(prepareField (input.nat 0) (input.real (input.nat 1+1))).mean ∧
  s.realReg 505=(prepareField (input.nat 0) (input.real (input.nat 1+1))).plusWeight ∧
  s.realReg 506=(prepareField (input.nat 0) (input.real (input.nat 1+1))).minusWeight ∧
  s.realReg 507=(prepareField (input.nat 0) (input.real (input.nat 1+1))).logBase ∧
  s.realReg 508=(budget params input budgetBase).u ∧
  s.realReg 509=(budget params input budgetBase).z

theorem scalar_cost (budgetBase : ℕ) : codeCost (scalarCode budgetBase)=154 := by
  norm_num [scalarCode,readCode,budgetSave,fieldSetup,fieldSave,codeCost,instrCost,
    RestrictedScalars.budgetCode,RestrictedScalars.fieldCode]

theorem scalar_values (params : Parameters) (input : Inputs) (s : State) (budgetBase : ℕ) :
    Ready params input budgetBase (runCode params input (scalarCode budgetBase) s) := by
  simp [Ready,scalarCode,readCode,budgetSave,fieldSetup,fieldSave,
    RestrictedScalars.budgetCode,RestrictedScalars.fieldCode,runCode,step,budget,
    prepareField,prepareBudget,hyperbolicCosine,hyperbolicTangent,divide,
    exponential,logarithm,SpinGlass.ArithmeticEvaluation.mul,SpinGlass.ArithmeticEvaluation.add,
    SpinGlass.ArithmeticEvaluation.literal,Nat.add_assoc]

theorem scalar_exec (params : Parameters) (input : Inputs) (s : State) (budgetBase : ℕ) :
    ∃ t, Exec params input (code (scalarCode budgetBase)) s 154 t ∧
      Ready params input budgetBase t ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  refine ⟨runCode params input (scalarCode budgetBase) s,?_,scalar_values _ _ _ _,?_,?_⟩
  · simpa only [scalar_cost] using exec_code params input (scalarCode budgetBase) s
  · apply (exec_code params input (scalarCode budgetBase) s).realMem_frame
    simp [scalarCode,readCode,budgetSave,fieldSetup,fieldSave,
      RestrictedScalars.budgetCode,RestrictedScalars.fieldCode,code,Program.All,
      Instruction.writesRealMemory]
  · apply (exec_code params input (scalarCode budgetBase) s).natMem_frame
    simp [scalarCode,readCode,budgetSave,fieldSetup,fieldSave,
      RestrictedScalars.budgetCode,RestrictedScalars.fieldCode,code,Program.All,
      Instruction.writesNatMemory]

end Manuscript.RestrictedInputScalars
