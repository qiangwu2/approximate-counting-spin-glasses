import Manuscript.SKPrimitiveAssembly

noncomputable section
namespace Manuscript.SKPrimitiveFrames
open RestrictedMachine

theorem natReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i SKPrimitiveAssembly.program s c t) (hr : 300≤r) :
    t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [SKPrimitiveAssembly.program,SKPrimitiveAssembly.initProgram,SKPrimitiveAssembly.fillSetup,SKPrimitiveLoops.program,
    SKPrimitiveLoops.initCode,SKPrimitiveLoops.boundRegister,SKPrimitiveLoops.body,SKPrimitiveScan.pairInit,
    SKPrimitiveScan.cycleInit,SKPrimitiveScan.pairBody,SKPrimitiveScan.cycleBody,SKPrimitiveScan.pairSetup,
    SKPrimitiveScan.cycleSetup,SKPrimitiveScan.advance,SKPrimitivePair.program,SKPrimitivePair.closureProgram,
    SKPrimitivePair.checkCode,SKPrimitiveCycleInsert.program,SKPrimitiveCycle.program,SKPrimitiveCycle.sumProgram,
    SKPrimitiveCycle.setupCode,SKRestrictedGrid.program,SKRestrictedGrid.body,SKRestrictedGrid.tailCode,
    SKPrimitiveReturn.program,SKPrimitivePath.program,SKPrimitivePath.setupCode,SKPrimitiveNormalize.program,
    SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,SKRestrictedKernels.dotProgram,
    SKRestrictedKernels.dotBody,SKPrimitiveIndex.pairProgram,SKPrimitiveIndex.cycleProgram,SKPrimitiveIndex.cardCode,
    SKPrimitiveIndex.firstCode,SKPrimitiveIndex.secondCode,SKPrimitiveIndex.pairFinish,SKPrimitiveIndex.cycleFinish,
    IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,IndexGeneration.powerProgram,
    IndexGeneration.powerInit,IndexGeneration.powerBody,SKPrimitiveInsert.program,SKPrimitiveInsert.checkCode,
    SKPrimitiveInsert.updateCode,RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
    code,Program.All,Instruction.natDestination]
  omega

theorem realReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i SKPrimitiveAssembly.program s c t) (hr : 5≤r) :
    t.realReg r=s.realReg r := by
  apply he.realReg_frame
  simp [SKPrimitiveAssembly.program,SKPrimitiveAssembly.initProgram,SKPrimitiveAssembly.fillSetup,SKPrimitiveLoops.program,
    SKPrimitiveLoops.initCode,SKPrimitiveLoops.boundRegister,SKPrimitiveLoops.body,SKPrimitiveScan.pairInit,
    SKPrimitiveScan.cycleInit,SKPrimitiveScan.pairBody,SKPrimitiveScan.cycleBody,SKPrimitiveScan.pairSetup,
    SKPrimitiveScan.cycleSetup,SKPrimitiveScan.advance,SKPrimitivePair.program,SKPrimitivePair.closureProgram,
    SKPrimitivePair.checkCode,SKPrimitiveCycleInsert.program,SKPrimitiveCycle.program,SKPrimitiveCycle.sumProgram,
    SKPrimitiveCycle.setupCode,SKRestrictedGrid.program,SKRestrictedGrid.body,SKRestrictedGrid.tailCode,
    SKPrimitiveReturn.program,SKPrimitivePath.program,SKPrimitivePath.setupCode,SKPrimitiveNormalize.program,
    SKPrimitiveNormalize.cardSetup,SKPrimitiveNormalize.testCode,SKPrimitiveNormalize.divideCode,SKRestrictedKernels.dotProgram,
    SKRestrictedKernels.dotBody,SKPrimitiveIndex.pairProgram,SKPrimitiveIndex.cycleProgram,SKPrimitiveIndex.cardCode,
    SKPrimitiveIndex.firstCode,SKPrimitiveIndex.secondCode,SKPrimitiveIndex.pairFinish,SKPrimitiveIndex.cycleFinish,
    IndexGeneration.overlapProgram,IndexGeneration.overlapInit,IndexGeneration.overlapBody,IndexGeneration.powerProgram,
    IndexGeneration.powerInit,IndexGeneration.powerBody,SKPrimitiveInsert.program,SKPrimitiveInsert.checkCode,
    SKPrimitiveInsert.updateCode,RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
    code,Program.All,Instruction.realDestination]
  omega
end Manuscript.SKPrimitiveFrames
