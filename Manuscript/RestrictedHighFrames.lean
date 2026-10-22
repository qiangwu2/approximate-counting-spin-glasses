import Manuscript.RestrictedControlFrames

noncomputable section
namespace Manuscript.RestrictedHighFrames
open RestrictedMachine RestrictedControl

theorem higher (base threshold r : ℕ) (hr : 247 ≤ r) :
    (higherProgram base threshold).All (fun op => op.natDestination ≠ some r) ∧
    (higherProgram base threshold).All (fun op => op.realDestination ≠ some r) := by
  constructor
  all_goals
    simp [higherProgram,higherRead,higherTruncated,higherExact,higherFinish,kappaSetup,
      higherCutoffSetup,branchTest,RestrictedKappa.program,RestrictedKappa.zeroTest,
      RestrictedKappa.nonzeroProgram,RestrictedKappa.absoluteProgram,RestrictedKappa.negativeCode,
      RestrictedKappa.arithmeticCode,RestrictedKappa.minimumProgram,RestrictedCutoff.program,
      RestrictedCutoff.prepareCode,RestrictedCutoff.scanSetup,RestrictedCutoff.finishCode,
      RestrictedFloor.program,RestrictedFloor.loop,RestrictedFloor.bodyCode,RestrictedFloor.testCode,
      RestrictedCutoffScan.program,RestrictedCutoffScan.setupCode,RestrictedCutoffScan.loop,
      RestrictedCutoffScan.body,RestrictedCutoffScan.scoreCode,RestrictedCutoffScan.yesCode,
      RestrictedCutoffScan.noCode,Program.All,code,Instruction.natDestination,Instruction.realDestination]
    omega

theorem sk (base threshold r : ℕ) (hr : 247 ≤ r) :
    (skProgram base threshold).All (fun op => op.natDestination ≠ some r) ∧
    (skProgram base threshold).All (fun op => op.realDestination ≠ some r) := by
  constructor
  all_goals
    simp [skProgram,skRead,skTruncated,skExact,skFinish,skCutoffSetup,skParameterSetup,
      branchTest,RestrictedCutoff.program,RestrictedCutoff.prepareCode,RestrictedCutoff.scanSetup,
      RestrictedCutoff.finishCode,RestrictedFloor.program,RestrictedFloor.loop,RestrictedFloor.bodyCode,
      RestrictedFloor.testCode,RestrictedCutoffScan.program,RestrictedCutoffScan.setupCode,
      RestrictedCutoffScan.loop,RestrictedCutoffScan.body,RestrictedCutoffScan.scoreCode,
      RestrictedCutoffScan.yesCode,RestrictedCutoffScan.noCode,RestrictedSKParameters.program,
      RestrictedSKParameters.firstCode,RestrictedSKParameters.secondCode,RestrictedSKParameters.lastCode,
      RestrictedCeiling.program,RestrictedCeiling.loop,RestrictedCeiling.bodyCode,RestrictedCeiling.testCode,
      Program.All,code,Instruction.natDestination,Instruction.realDestination]
    omega

end Manuscript.RestrictedHighFrames
