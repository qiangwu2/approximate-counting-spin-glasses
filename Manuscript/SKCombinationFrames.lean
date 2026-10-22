import Manuscript.SKRestrictedCombination

namespace Manuscript.SKRestrictedCombination
open RestrictedMachine

theorem program_frame (p : Parameters) (i : Inputs) {s t : State} {c : ℕ}
    (he : Exec p i program s c t) :
    (∀ r, 42≤r → t.natReg r=s.natReg r) ∧
    (∀ r, 6≤r → t.realReg r=s.realReg r) ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_,?_⟩
  · intro r hr
    apply he.natReg_frame
    simp [program,copySetup,directSetup,SKRestrictedInitialize.program,
      SKRestrictedInitialize.first,SKRestrictedInitialize.second,SKRestrictedOne.program,
      SKRestrictedOne.setup,SKRestrictedOne.finish,SKRestrictedExponential.program,
      SKRestrictedExponential.body,SKRestrictedMultiply.program,SKRestrictedMultiply.clearSetup,
      SKRestrictedMultiply.scatterSetup,SKRestrictedScaleAdd.program,SKRestrictedScaleAdd.scaleSetup,
      SKRestrictedScaleAdd.sumSetup,SKRestrictedCopy.program,SKRestrictedCopy.setup,
      SKRestrictedDirect.program,SKRestrictedDirectStep.program,SKRestrictedDirectStep.first,
      SKRestrictedDirectStep.second,SKRestrictedDirectStep.addOne,SKRestrictedDirectStep.finish,
      SKRestrictedScatter.program,SKRestrictedScatter.body,SKRestrictedScatter.header,
      SKRestrictedKernels.accumulateBody,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.natDestination]
    omega
  · intro r hr
    apply he.realReg_frame
    simp [program,copySetup,directSetup,SKRestrictedInitialize.program,
      SKRestrictedInitialize.first,SKRestrictedInitialize.second,SKRestrictedOne.program,
      SKRestrictedOne.setup,SKRestrictedOne.finish,SKRestrictedExponential.program,
      SKRestrictedExponential.body,SKRestrictedMultiply.program,SKRestrictedMultiply.clearSetup,
      SKRestrictedMultiply.scatterSetup,SKRestrictedScaleAdd.program,SKRestrictedScaleAdd.scaleSetup,
      SKRestrictedScaleAdd.sumSetup,SKRestrictedCopy.program,SKRestrictedCopy.setup,
      SKRestrictedDirect.program,SKRestrictedDirectStep.program,SKRestrictedDirectStep.first,
      SKRestrictedDirectStep.second,SKRestrictedDirectStep.addOne,SKRestrictedDirectStep.finish,
      SKRestrictedScatter.program,SKRestrictedScatter.body,SKRestrictedScatter.header,
      SKRestrictedKernels.accumulateBody,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.realDestination]
    omega
  · apply he.natMem_frame
    simp [program,copySetup,directSetup,SKRestrictedInitialize.program,
      SKRestrictedInitialize.first,SKRestrictedInitialize.second,SKRestrictedOne.program,
      SKRestrictedOne.setup,SKRestrictedOne.finish,SKRestrictedExponential.program,
      SKRestrictedExponential.body,SKRestrictedMultiply.program,SKRestrictedMultiply.clearSetup,
      SKRestrictedMultiply.scatterSetup,SKRestrictedScaleAdd.program,SKRestrictedScaleAdd.scaleSetup,
      SKRestrictedScaleAdd.sumSetup,SKRestrictedCopy.program,SKRestrictedCopy.setup,
      SKRestrictedDirect.program,SKRestrictedDirectStep.program,SKRestrictedDirectStep.first,
      SKRestrictedDirectStep.second,SKRestrictedDirectStep.addOne,SKRestrictedDirectStep.finish,
      SKRestrictedScatter.program,SKRestrictedScatter.body,SKRestrictedScatter.header,
      SKRestrictedKernels.accumulateBody,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.writesNatMemory]

end Manuscript.SKRestrictedCombination
