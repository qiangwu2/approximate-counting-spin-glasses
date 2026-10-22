import Manuscript.SKRootCacheInitialization

noncomputable section
namespace Manuscript.SKRootCache
open RestrictedMachine

def boundedDestination (bound : ℕ) : Option ℕ→Prop
  | none => True
  | some r => r<bound

/-- These are kernel-checked computations on the finite instruction syntax;
there is no evaluation of a program execution by the native compiler. -/
theorem program_nat_footprint :
    program.All (fun i=>boundedDestination 245 i.natDestination) := by
  simp [program,initProgram,initPrelude,initCode,body,memoCode,copyCode,tailCode,
      SKRootStart.program,SKRootStart.preludeCode,RestrictedDeltaVector.program,
      RestrictedDeltaVector.bodyCode,SKMemoInitialization.fullProgram,
      SKMemoInitialization.program,SKMemoInitialization.preludeCode,SKMemoInitialization.setupCode,
      IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
      RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
      SKMemoLayers.program,SKMemoLayers.body,SKMemoLayers.preludeCode,SKMemoLayers.tailCode,
      SKMemoPass.program,SKMemoPass.body,SKMemoPass.preludeCode,SKMemoPass.tailCode,
      SKMemoUpdate.program,SKMemoMetadata.program,SKMemoMetadata.preludeCode,
      SKMemoMetadata.middle,SKMemoMetadata.suffix,IndexGeneration.overlapProgram,
      IndexGeneration.overlapInit,IndexGeneration.overlapBody,SKRestrictedMemoCell.program,
      SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,code,Program.All,
      boundedDestination,Instruction.natDestination]

theorem program_real_footprint :
    program.All (fun i=>boundedDestination 5 i.realDestination) := by
  simp [program,initProgram,initPrelude,initCode,body,memoCode,copyCode,tailCode,
      SKRootStart.program,SKRootStart.preludeCode,RestrictedDeltaVector.program,
      RestrictedDeltaVector.bodyCode,SKMemoInitialization.fullProgram,
      SKMemoInitialization.program,SKMemoInitialization.preludeCode,SKMemoInitialization.setupCode,
      IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
      RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
      SKMemoLayers.program,SKMemoLayers.body,SKMemoLayers.preludeCode,SKMemoLayers.tailCode,
      SKMemoPass.program,SKMemoPass.body,SKMemoPass.preludeCode,SKMemoPass.tailCode,
      SKMemoUpdate.program,SKMemoMetadata.program,SKMemoMetadata.preludeCode,
      SKMemoMetadata.middle,SKMemoMetadata.suffix,IndexGeneration.overlapProgram,
      IndexGeneration.overlapInit,IndexGeneration.overlapBody,SKRestrictedMemoCell.program,
      SKRestrictedKernels.dotProgram,SKRestrictedKernels.dotBody,code,Program.All,
      boundedDestination,Instruction.realDestination]

theorem natReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (h : Exec params input program s c t) (hr : 245≤r) : t.natReg r=s.natReg r := by
  apply h.natReg_frame
  apply program_nat_footprint.mono
  intro op ho he
  rw [he] at ho
  simp only [boundedDestination] at ho
  omega

theorem realReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (h : Exec params input program s c t) (hr : 5≤r) : t.realReg r=s.realReg r := by
  apply h.realReg_frame
  apply program_real_footprint.mono
  intro op ho he
  rw [he] at ho
  simp only [boundedDestination] at ho
  omega

end Manuscript.SKRootCache
