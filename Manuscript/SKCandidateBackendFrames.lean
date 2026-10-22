import Manuscript.SKDirectBank
import Manuscript.SKMetadataSchedule
import Manuscript.SKCombinationFrames
import Manuscript.SKExtractionFrames

noncomputable section
namespace Manuscript.SKCandidateBackendFrames
open RestrictedMachine IndexGeneration

theorem bank_nat_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i SKDirectBank.program s c t) (hr : 300≤r) (hr' : r<440 ∨ 462≤r) :
    t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [SKDirectBank.program,SKDirectBank.body,SKDirectBank.setup,SKDirectBank.advance,SKDirectBank.initCode,
    SKDirectFactor.program,SKDirectFactor.test,SKDirectFactor.zero,
    SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,SKDirectIndex.finish,
    powerProgram,powerInit,powerBody,SKRestrictedSingle.program,SKRestrictedSingle.setup,SKRestrictedSingle.finish,
    RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
    code,Program.All,Instruction.natDestination]
  omega

theorem bank_frame {p : Parameters} {i : Inputs} {s t : State} {c : ℕ}
    (he : Exec p i SKDirectBank.program s c t) :
    (∀r,43≤r → t.realReg r=s.realReg r) ∧ t.natMem=s.natMem := by
  constructor
  · intro r hr
    apply he.realReg_frame
    simp [SKDirectBank.program,SKDirectBank.body,SKDirectBank.setup,SKDirectBank.advance,SKDirectBank.initCode,
      SKDirectFactor.program,SKDirectFactor.test,SKDirectFactor.zero,
      SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,SKDirectIndex.finish,
      powerProgram,powerInit,powerBody,SKRestrictedSingle.program,SKRestrictedSingle.setup,SKRestrictedSingle.finish,
      RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
      code,Program.All,Instruction.realDestination]
    omega
  · apply he.natMem_frame
    simp [SKDirectBank.program,SKDirectBank.body,SKDirectBank.setup,SKDirectBank.advance,SKDirectBank.initCode,
      SKDirectFactor.program,SKDirectFactor.test,SKDirectFactor.zero,
      SKDirectIndex.program,SKDirectIndex.first,SKDirectIndex.second,SKDirectIndex.finish,
      powerProgram,powerInit,powerBody,SKRestrictedSingle.program,SKRestrictedSingle.setup,SKRestrictedSingle.finish,
      RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
      code,Program.All,Instruction.writesNatMemory]

theorem metadata_frame {p : Parameters} {i : Inputs} {s t : State} {c : ℕ}
    (he : Exec p i metadataProgram s c t) :
    (∀r,170≤r → t.natReg r=s.natReg r) ∧ (∀r,t.realReg r=s.realReg r) := by
  constructor
  · intro r hr
    apply he.natReg_frame
    simp [metadataProgram,metadataBody,metadataInit,metadataDecode,pairProgram,pairDecode,pairAddress,pairEmit,
      degreeProgram,degreeInit,degreeBody,degreePrefix,degreeHigh,degreeLow,degreeTail,overlapProgram,overlapInit,overlapBody,
      code,Program.All,Instruction.natDestination]
    omega
  · intro r
    apply he.realReg_frame
    simp [metadataProgram,metadataBody,metadataInit,metadataDecode,pairProgram,pairDecode,pairAddress,pairEmit,
      degreeProgram,degreeInit,degreeBody,degreePrefix,degreeHigh,degreeLow,degreeTail,overlapProgram,overlapInit,overlapBody,
      code,Program.All,Instruction.realDestination]

theorem metadataPrefix_before (memory : ℕ→ℕ) (base : ℕ) (records : ℕ→PairRecord)
    (n address : ℕ) (ha : address<base) : metadataPrefix memory base records n address=memory address := by
  induction n with
  | zero => rfl
  | succ n ih => rw [metadataPrefix,writeRecord_outside _ _ _ _ (Or.inl (by omega)),ih]
end Manuscript.SKCandidateBackendFrames
