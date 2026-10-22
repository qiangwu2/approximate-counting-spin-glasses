import Manuscript.RestrictedSKControl

noncomputable section
namespace Manuscript.RestrictedControl
open RestrictedMachine

theorem higher_memory_frame (params : Parameters) (input : Inputs)
    (base threshold : ℕ) (s t : State) (c : ℕ)
    (h : Exec params input (higherProgram base threshold) s c t) :
    t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  have hs : (higherProgram base threshold).All
      (fun op => op.writesRealMemory=false ∧ op.writesNatMemory=false) := by
    simp [higherProgram, higherRead, higherTruncated,
      higherExact, higherFinish, kappaSetup,
      higherCutoffSetup, branchTest, RestrictedKappa.program,
      RestrictedKappa.zeroTest, RestrictedKappa.nonzeroProgram, RestrictedKappa.absoluteProgram,
      RestrictedKappa.negativeCode, RestrictedKappa.arithmeticCode, RestrictedKappa.minimumProgram,
      RestrictedCutoff.program, RestrictedCutoff.prepareCode, RestrictedCutoff.scanSetup,
      RestrictedCutoff.finishCode, RestrictedFloor.program, RestrictedFloor.loop,
      RestrictedFloor.bodyCode, RestrictedFloor.testCode, RestrictedCutoffScan.program,
      RestrictedCutoffScan.setupCode, RestrictedCutoffScan.loop, RestrictedCutoffScan.body,
      RestrictedCutoffScan.scoreCode, RestrictedCutoffScan.yesCode, RestrictedCutoffScan.noCode,
      Program.All, code, Instruction.writesRealMemory,
      Instruction.writesNatMemory]
  exact ⟨h.realMem_frame (hs.mono fun _ h => h.1), h.natMem_frame (hs.mono fun _ h => h.2)⟩

theorem higher_source_frame (params : Parameters) (input : Inputs)
    (base threshold : ℕ) (s t : State) (c : ℕ)
    (h : Exec params input (higherProgram base threshold) s c t) :
    t.natReg 200=s.natReg 200 ∧
    (∀ r, 200≤r → r≤202 → t.realReg r=s.realReg r) := by
  constructor
  · apply h.natReg_frame
    simp [higherProgram, higherRead, higherTruncated,
      higherExact, higherFinish, kappaSetup,
      higherCutoffSetup, branchTest, RestrictedKappa.program,
      RestrictedKappa.zeroTest, RestrictedKappa.nonzeroProgram, RestrictedKappa.absoluteProgram,
      RestrictedKappa.negativeCode, RestrictedKappa.arithmeticCode, RestrictedKappa.minimumProgram,
      RestrictedCutoff.program, RestrictedCutoff.prepareCode, RestrictedCutoff.scanSetup,
      RestrictedCutoff.finishCode, RestrictedFloor.program, RestrictedFloor.loop,
      RestrictedFloor.bodyCode, RestrictedFloor.testCode, RestrictedCutoffScan.program,
      RestrictedCutoffScan.setupCode, RestrictedCutoffScan.loop, RestrictedCutoffScan.body,
      RestrictedCutoffScan.scoreCode, RestrictedCutoffScan.yesCode, RestrictedCutoffScan.noCode,
      Program.All, code, Instruction.natDestination]
  · intro r hr hr'
    apply h.realReg_frame
    simp [higherProgram, higherRead, higherTruncated,
      higherExact, higherFinish, kappaSetup,
      higherCutoffSetup, branchTest, RestrictedKappa.program,
      RestrictedKappa.zeroTest, RestrictedKappa.nonzeroProgram, RestrictedKappa.absoluteProgram,
      RestrictedKappa.negativeCode, RestrictedKappa.arithmeticCode, RestrictedKappa.minimumProgram,
      RestrictedCutoff.program, RestrictedCutoff.prepareCode, RestrictedCutoff.scanSetup,
      RestrictedCutoff.finishCode, RestrictedFloor.program, RestrictedFloor.loop,
      RestrictedFloor.bodyCode, RestrictedFloor.testCode, RestrictedCutoffScan.program,
      RestrictedCutoffScan.setupCode, RestrictedCutoffScan.loop, RestrictedCutoffScan.body,
      RestrictedCutoffScan.scoreCode, RestrictedCutoffScan.yesCode, RestrictedCutoffScan.noCode,
      Program.All, code, Instruction.realDestination]
    omega

theorem sk_memory_frame (params : Parameters) (input : Inputs)
    (base threshold : ℕ) (s t : State) (c : ℕ)
    (h : Exec params input (skProgram base threshold) s c t) :
    t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  have hs : (skProgram base threshold).All
      (fun op => op.writesRealMemory=false ∧ op.writesNatMemory=false) := by
    simp [skProgram, skRead, skTruncated,
      skExact, skFinish, skCutoffSetup,
      skParameterSetup, branchTest, RestrictedCutoff.program,
      RestrictedCutoff.prepareCode, RestrictedCutoff.scanSetup, RestrictedCutoff.finishCode,
      RestrictedFloor.program, RestrictedFloor.loop, RestrictedFloor.bodyCode,
      RestrictedFloor.testCode, RestrictedCutoffScan.program, RestrictedCutoffScan.setupCode,
      RestrictedCutoffScan.loop, RestrictedCutoffScan.body, RestrictedCutoffScan.scoreCode,
      RestrictedCutoffScan.yesCode, RestrictedCutoffScan.noCode, RestrictedSKParameters.program,
      RestrictedSKParameters.firstCode, RestrictedSKParameters.secondCode, RestrictedSKParameters.lastCode,
      RestrictedCeiling.program, RestrictedCeiling.loop, RestrictedCeiling.bodyCode,
      RestrictedCeiling.testCode, Program.All, code,
      Instruction.writesRealMemory, Instruction.writesNatMemory]
  exact ⟨h.realMem_frame (hs.mono fun _ h => h.1), h.natMem_frame (hs.mono fun _ h => h.2)⟩

theorem sk_source_frame (params : Parameters) (input : Inputs)
    (base threshold : ℕ) (s t : State) (c : ℕ)
    (h : Exec params input (skProgram base threshold) s c t) :
    t.natReg 200=s.natReg 200 ∧
    (∀ r, 200≤r → r≤202 → t.realReg r=s.realReg r) := by
  constructor
  · apply h.natReg_frame
    simp [skProgram, skRead, skTruncated,
      skExact, skFinish, skCutoffSetup,
      skParameterSetup, branchTest, RestrictedCutoff.program,
      RestrictedCutoff.prepareCode, RestrictedCutoff.scanSetup, RestrictedCutoff.finishCode,
      RestrictedFloor.program, RestrictedFloor.loop, RestrictedFloor.bodyCode,
      RestrictedFloor.testCode, RestrictedCutoffScan.program, RestrictedCutoffScan.setupCode,
      RestrictedCutoffScan.loop, RestrictedCutoffScan.body, RestrictedCutoffScan.scoreCode,
      RestrictedCutoffScan.yesCode, RestrictedCutoffScan.noCode, RestrictedSKParameters.program,
      RestrictedSKParameters.firstCode, RestrictedSKParameters.secondCode, RestrictedSKParameters.lastCode,
      RestrictedCeiling.program, RestrictedCeiling.loop, RestrictedCeiling.bodyCode,
      RestrictedCeiling.testCode, Program.All, code,
      Instruction.natDestination]
  · intro r hr hr'
    apply h.realReg_frame
    simp [skProgram, skRead, skTruncated,
      skExact, skFinish, skCutoffSetup,
      skParameterSetup, branchTest, RestrictedCutoff.program,
      RestrictedCutoff.prepareCode, RestrictedCutoff.scanSetup, RestrictedCutoff.finishCode,
      RestrictedFloor.program, RestrictedFloor.loop, RestrictedFloor.bodyCode,
      RestrictedFloor.testCode, RestrictedCutoffScan.program, RestrictedCutoffScan.setupCode,
      RestrictedCutoffScan.loop, RestrictedCutoffScan.body, RestrictedCutoffScan.scoreCode,
      RestrictedCutoffScan.yesCode, RestrictedCutoffScan.noCode, RestrictedSKParameters.program,
      RestrictedSKParameters.firstCode, RestrictedSKParameters.secondCode, RestrictedSKParameters.lastCode,
      RestrictedCeiling.program, RestrictedCeiling.loop, RestrictedCeiling.bodyCode,
      RestrictedCeiling.testCode, Program.All, code,
      Instruction.realDestination]
    omega

/-- A fixed finite block of model constants in the read-only parameter array.
The block is chosen before runtime input, and all accesses still execute reads. -/
def parameterBlock (base length : ℕ) (values : ℕ→ℝ) (background : Parameters) : Parameters :=
  fun address => if base≤address ∧ address<base+length then values (address-base) else background address

theorem parameterBlock_value (base length j : ℕ) (values : ℕ→ℝ) (background : Parameters)
    (hj : j<length) : parameterBlock base length values background (base+j)=values j := by
  simp [parameterBlock,show base≤base+j by omega,show base+j<base+length by omega]

theorem parameterBlock_outside (base length address : ℕ) (values : ℕ→ℝ) (background : Parameters)
    (h : address<base ∨ base+length≤address) : parameterBlock base length values background address=background address := by
  simp [parameterBlock,show ¬(base≤address ∧ address<base+length) by omega]

theorem higher_control_execution (input : Inputs) (s : State) (base : ℕ) (background : Parameters)
    (pmax : ℕ) (P : Finset ℕ) (a : ℕ→ℝ) (B rho pmin : ℝ) :
    let d := manuscriptHigherDesign pmax P a B rho pmin
    let params := parameterBlock base 7 (higherConstants d) background
    ∃ c t, Exec params input (higherProgram base d.threshold) s c t ∧
      c≤78*s.natReg 200+220 ∧
      t.natReg 201=(HigherOrderExecution.control (s.natReg 200) pmax P a B rho pmin
        (s.realReg 201) (s.realReg 200) (s.realReg 202)).cutoff ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  dsimp only
  let d := manuscriptHigherDesign pmax P a B rho pmin
  let params := parameterBlock base 7 (higherConstants d) background
  obtain ⟨c,t,he,hc,hv⟩ := higher_execution params input s base d
    (HigherOrderTail.scale_pos P a B rho pmin)
    (fun j hj => parameterBlock_value base 7 j (higherConstants d) background hj)
  refine ⟨c,t,he,hc,?_,higher_memory_frame params input base d.threshold s t c he⟩
  simpa only [d,higherChoice_eq_control] using hv

theorem sk_control_execution (input : Inputs) (s : State) (base : ℕ) (background : Parameters)
    (a : ℕ→ℝ) (B rho : ℝ) :
    let d := manuscriptSKDesign a B rho
    let params := parameterBlock base 5 (skConstants d) background
    ∃ c t, Exec params input (skProgram base d.threshold) s c t ∧
      c≤78*s.natReg 200+
        9*(SKControl.parameters (SKAlgorithm.q a B)
          (Real.log (SKAlgorithm.errorConstant a B rho/s.realReg 200))).operations+160 ∧
      (⟨t.natReg 201,t.natReg 202,t.natReg 203,t.natReg 204⟩ : ControlResult)=
        ⟨(SKControl.control (s.natReg 200) a B rho (s.realReg 200)).branchLimit,
         (SKControl.control (s.natReg 200) a B rho (s.realReg 200)).exact.toNat,
         (SKControl.control (s.natReg 200) a B rho (s.realReg 200)).edgeLimit,
         (SKControl.control (s.natReg 200) a B rho (s.realReg 200)).trials⟩ ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  dsimp only
  let d := manuscriptSKDesign a B rho
  let params := parameterBlock base 5 (skConstants d) background
  obtain ⟨c,t,he,hc,hv⟩ := sk_execution params input s base d (SKAlgorithm.scale_pos B rho)
    (fun j hj => parameterBlock_value base 5 j (skConstants d) background hj)
  refine ⟨c,t,he,hc,?_,sk_memory_frame params input base d.threshold s t c he⟩
  simpa only [d,skChoice_eq_control] using hv

end Manuscript.RestrictedControl
