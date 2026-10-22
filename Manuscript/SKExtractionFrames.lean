import Manuscript.SKRestrictedExtraction

noncomputable section
namespace Manuscript.SKExtractionFrames
open RestrictedMachine

theorem natReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i SKRestrictedExtraction.program s c t) (hr : 364≤r) :
    t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [SKRestrictedExtraction.program,SKRestrictedExtraction.setupCode,SKExtractionCell.program,SKExtractionCell.preProgram,
    SKExtractionCell.decodeCode,SKExtractionCell.finishCode,SKExtractionCell.correctionSetup,SKDegreeAcceptance.program,
    SKDegreeAcceptance.body,SKDegreeAcceptance.initCode,SKDegreeAcceptance.headCode,SKDegreeAcceptance.ghostCode,
    SKDegreeAcceptance.otherCode,SKDegreeAcceptance.tailCode,IndexGeneration.overlapProgram,IndexGeneration.overlapInit,
    IndexGeneration.overlapBody,SKColorCorrection.program,SKColorCorrection.setupCode,SKColorCorrection.bodyCode,
    code,Program.All,Instruction.natDestination]
  omega

theorem realReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i SKRestrictedExtraction.program s c t) (hr : 311≤r) :
    t.realReg r=s.realReg r := by
  apply he.realReg_frame
  simp [SKRestrictedExtraction.program,SKRestrictedExtraction.setupCode,SKExtractionCell.program,SKExtractionCell.preProgram,
    SKExtractionCell.decodeCode,SKExtractionCell.finishCode,SKExtractionCell.correctionSetup,SKDegreeAcceptance.program,
    SKDegreeAcceptance.body,SKDegreeAcceptance.initCode,SKDegreeAcceptance.headCode,SKDegreeAcceptance.ghostCode,
    SKDegreeAcceptance.otherCode,SKDegreeAcceptance.tailCode,IndexGeneration.overlapProgram,IndexGeneration.overlapInit,
    IndexGeneration.overlapBody,SKColorCorrection.program,SKColorCorrection.setupCode,SKColorCorrection.bodyCode,
    code,Program.All,Instruction.realDestination]
  omega
end Manuscript.SKExtractionFrames
