import Manuscript.SKRestrictedCandidateExecution
import Manuscript.SKGhostCoefficient
import Manuscript.SKCanonicalLabels

/-! The existing candidate program retains every computed coefficient in RAM,
including after its optional corrected scalar extraction. -/
noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
namespace Manuscript.SKCandidateCoefficientOutput
open RestrictedMachine IndexGeneration SKCandidateLayout SKBasisEncoding SKCandidateBackendFrames
open SpinGlass SKCoefficient SKFastEvaluator
open SKCandidateBackend

theorem backend_exec {V : Type*} [DecidableEq V] (p : Parameters) (i : RestrictedMachine.Inputs)
    (d : Layout) (hK : 1≤d.root.K) (q : Fin d.root.B→ℕ) (branch : Fin d.root.B→V)
    (f : Finset V→ℝ) (prim : Coefficients d.root.B d.root.K) (s : State)
    (hs : Shape d s)
    (hq : ∀a,s.natMem (d.chargeBase+a.val)=q a)
    (hw : ∀a c,s.realMem (d.branchWeightBase+a.val*d.root.B+c.val)=pairWeight f (branch a) (branch c))
    (hp : SKRestrictedArrays.Represents d.primitiveBase prim s.realMem) :
    ∃ count t, Exec p i SKCandidateBackend.program s count t ∧ count≤operationBound d ∧
      t.realReg 310=(SKChargedExtractionExecution.extract
        (SKExponential.algebraEvaluator prim (SKChargedTrialExecution.directList q branch f))
        d.retained (SKExtractionCell.accepted d.ghost)).value ∧
      SKRestrictedArrays.Represents d.base
        (SKExponential.algebraEvaluator prim (SKChargedTrialExecution.directList q branch f)) t.realMem ∧
      (∀address,address<d.root.arena → t.realMem address=s.realMem address) ∧
      (∀address,address<d.metadataBase → t.natMem address=s.natMem address) ∧
      (∀r,500≤r → t.natReg r=s.natReg r) ∧ (∀r,500≤r → t.realReg r=s.realReg r) := by
  unfold Shape at hs
  let a := runCode p i directSetup s
  have ha : SKDirectBank.Ready (K:=d.root.K) d.bank d.chargeBase d.branchWeightBase q branch f a := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,hq,hw⟩
    all_goals try { simp [a,directSetup,runCode,step,hs,expected,Layout.M] }
    have h1 := d.branchWeightFit; have h2 := d.arena_le_base
    unfold Layout.bank; omega
  obtain ⟨c1,b,he1,bc1,hbready,hbank,hmb⟩ := SKDirectBank.program_exec hK p i a d.bank d.chargeBase d.branchWeightBase q branch f ha
  have hb : Shape d b := by
    intro r hlo hhi
    rw [bank_nat_frame he1 (by omega) (by omega)]
    exact direct_setup_shape p i d s hs r hlo hhi
  unfold Shape at hb
  have hprim : SKRestrictedArrays.Represents d.primitiveBase prim b.realMem := by
    intro x
    rw [hmb _ (Or.inl (by
      have hx := encode_lt x
      change _<d.M at hx
      unfold Layout.bank Layout.primitiveBase
      omega))]
    exact hp x
  let c := runCode p i metadataSetup b
  have hc : SKMetadataSchedule.TableRegisters d.root.B d.root.K d.base c := by
    simp [SKMetadataSchedule.TableRegisters,c,metadataSetup,runCode,step,hb,expected,Layout.M]
    omega
  obtain ⟨c2,e,he2,bc2,henm,heptr,hem⟩ := metadata_execution p i c
  have he : Shape d e := by
    intro r hlo hhi
    rw [(metadata_frame he2).1 r (by omega)]
    exact metadata_setup_shape p i d b hb r hlo hhi
  unfold Shape at he
  have hoff : c.natReg 147=d.metadataBase := by simp [c,metadataSetup,runCode,step,hb,expected]
  have hrecords : SKRestrictedAlgebra.ScheduleMatches (denseLayout d.root.B d.root.K d.base)
      e.natMem d.metadataBase (pairList d.root.B d.root.K) := by
    rw [henm,← hoff,← SKMetadataSchedule.numericPairs_eq_pairList]
    exact SKMetadataSchedule.metadata_schedule d.root.B d.root.K d.base c hc
  let es := SKDirectBank.segment (SKDirectBank.entry (K:=d.root.K) q branch f) 0 (d.root.B*d.root.B)
  let g := runCode p i combineSetup e
  obtain ⟨c3,h,he3,bc3,hout,hmh⟩ := SKRestrictedCombination.program_exec_framed p i g
    d.base d.metadataBase d.bank d.root.K prim es
    (by simp [g,combineSetup,runCode,step,he,expected])
    (by simp [g,combineSetup,runCode,step,he,expected,Layout.M])
    (by simp [g,combineSetup,runCode,step,he,expected])
    (by simp [g,combineSetup,runCode,step,he,expected,Layout.M,pow_two])
    (by simp [g,combineSetup,runCode,step,he,expected])
    (by simp [g,combineSetup,runCode,step])
    (by simp [g,combineSetup,runCode,step,he,expected,es])
    (by simp [g,combineSetup,runCode,step,he,expected])
    (by simp [Layout.bank,Layout.M])
    hrecords
    (by intro x; change e.realMem _=_; rw [hem]; exact hprim x)
    (by change SKRestrictedDirect.Bank _ _ e.realMem; rw [hem]; exact hbank)
  have hh : Shape d h := by
    intro r hlo hhi
    rw [(SKRestrictedCombination.program_frame p i he3).1 r (by omega)]
    exact combination_setup_shape p i d e he r hlo hhi
  unfold Shape at hh
  let j := runCode p i extractSetup h
  have hj : SKRestrictedExtraction.Shape d.root.B d.root.K d.ghost d.retained d.base j := by
    constructor <;> simp [j,extractSetup,runCode,step,hh,expected,SKRestrictedExtraction.width,Layout.M]
  obtain ⟨c4,t,he4,bc4,hvalue,htm,htn⟩ := SKRestrictedExtraction.extraction_realized p i
    (SKExponential.directLoop es (SKExponential.expLoop prim d.root.K).2) d.ghost d.retained d.base j hj hout
  have hexec : Exec p i SKCandidateBackend.program s (15+(c1+(24+(c2+(19+(c3+(16+c4))))))) t :=
    Exec.seq (exec_code p i directSetup s) (Exec.seq he1
      (Exec.seq (exec_code p i metadataSetup b) (Exec.seq he2
        (Exec.seq (exec_code p i combineSetup e) (Exec.seq he3
          (Exec.seq (exec_code p i extractSetup h) he4))))))
  refine ⟨_,t,hexec,?_,?_,?_,?_,?_,?_,?_⟩
  · have b2 : c2≤d.M^2*(52*d.root.B+29*d.root.K+157)+11 := by
      simpa [c,metadataSetup,runCode,step,hb,expected,pow_two] using bc2
    have b3 : c3≤(d.root.K+d.root.B*d.root.B)*(56*d.M^2+90*d.M+111)+90*d.M+104 := by
      simpa [es,Layout.M] using bc3
    have b4 : c4≤d.M*(40*d.root.B+53*d.root.K+110)+8 := by
      simpa [SKRestrictedExtraction.width,Layout.M] using bc4
    change c1≤d.root.B*d.root.B*(30*d.M+18*d.root.B+141)+10 at bc1
    dsimp [operationBound]
    omega
  · rw [hvalue]
    simp only [es,SKDirectBankSemantics.loop_eq,SKExponential.algebraEvaluator]
  · intro x
    rw [htm]
    change h.realMem (d.base+encode x)=_
    rw [hout]
    simp only [es,SKDirectBankSemantics.loop_eq,SKExponential.algebraEvaluator]
  · intro address haddress
    rw [htm]
    change h.realMem address=s.realMem address
    rw [hmh address (by have ha := d.arena_le_base; omega)]
    change e.realMem address=s.realMem address
    rw [hem]
    change b.realMem address=s.realMem address
    rw [hmb address (Or.inl (by have ha := d.arena_le_base; unfold Layout.bank; omega))]
    rfl
  · intro address haddress
    rw [htn]
    change h.natMem address=s.natMem address
    rw [(SKRestrictedCombination.program_frame p i he3).2.2]
    change e.natMem address=s.natMem address
    rw [henm,metadataPrefix_before _ _ _ _ _ (by rw [hoff]; exact haddress)]
    change b.natMem address=s.natMem address
    rw [(bank_frame he1).2]
    rfl
  · intro r hr
    rw [SKExtractionFrames.natReg_frame he4 (by omega)]
    have hjr : j.natReg r=h.natReg r := by
      apply (exec_code p i extractSetup h).natReg_frame
      simp [extractSetup,code,Program.All,Instruction.natDestination]; omega
    rw [hjr,(SKRestrictedCombination.program_frame p i he3).1 r (by omega)]
    have hgr : g.natReg r=e.natReg r := by
      apply (exec_code p i combineSetup e).natReg_frame
      simp [combineSetup,code,Program.All,Instruction.natDestination]; omega
    rw [hgr,(metadata_frame he2).1 r (by omega)]
    have hcr : c.natReg r=b.natReg r := by
      apply (exec_code p i metadataSetup b).natReg_frame
      simp [metadataSetup,code,Program.All,Instruction.natDestination]; omega
    rw [hcr,bank_nat_frame he1 (by omega) (by omega)]
    apply (exec_code p i directSetup s).natReg_frame
    simp [directSetup,code,Program.All,Instruction.natDestination]; omega
  · intro r hr
    rw [SKExtractionFrames.realReg_frame he4 (by omega)]
    change h.realReg r=s.realReg r
    rw [(SKRestrictedCombination.program_frame p i he3).2.1 r (by omega)]
    change e.realReg r=s.realReg r
    rw [(metadata_frame he2).2 r]
    change b.realReg r=s.realReg r
    rw [(bank_frame he1).1 r (by omega)]
    rfl
theorem candidate_exec {V : Type*} [DecidableEq V] (p : Parameters) (i : RestrictedMachine.Inputs)
    (d : Layout) (hK : 1≤d.root.K) (q : Fin d.root.B→ℕ)
    (branch : Fin d.root.B→V) (outside : Fin d.root.N→V)
    (χ : Fin d.root.N→Fin d.root.K) (f : Finset V→ℝ) (s : State)
    (hs : SKRootCache.InputsReady d.root χ
      (fun x y => pairWeight f (outside x) (outside y))
      (fun x y => pairWeight f (branch x) (outside y)) s)
    (hl : SKCandidateLayout.Inputs d s)
    (hq : ∀x,s.natMem (d.chargeBase+x.val)=q x)
    (hw : ∀a c,s.realMem (d.branchWeightBase+a.val*d.root.B+c.val)=pairWeight f (branch a) (branch c)) :
    ∃ count t, Exec p i SKRestrictedCandidateExecution.program s count t ∧ count≤SKRestrictedCandidateExecution.operationBound d ∧
      t.realReg 310=(SKChargedTrialExecution.trial q branch outside χ f d.retained
        (SKExtractionCell.accepted d.ghost)).value ∧
      SKRestrictedArrays.Represents d.base
        (SKChargedExecution.evaluate q branch outside χ f) t.realMem ∧
      (∀address,address<d.root.arena → t.realMem address=s.realMem address) ∧
      (∀address,address<d.metadataBase → t.natMem address=s.natMem address) ∧
      (∀r,500≤r → t.natReg r=s.natReg r) ∧ (∀r,500≤r → t.realReg r=s.realReg r) := by
  obtain ⟨c1,a,he1,bc1,ha,hp,hn,hm,han,har⟩ :=
    SKCandidatePrimitives.program_exec p i d q branch outside χ f s hs hl hq
  have hqa : ∀x,a.natMem (d.chargeBase+x.val)=q x := by intro x; rw [hn]; exact hq x
  have hwa : ∀x y,a.realMem (d.branchWeightBase+x.val*d.root.B+y.val)=pairWeight f (branch x) (branch y) := by
    intro x y
    rw [hm]
    · exact hw x y
    · have hx := x.isLt; have hy := y.isLt; have hfit := d.branchWeightFit
      nlinarith
  obtain ⟨c2,t,he2,bc2,hv,hcoeff,htm,htn,htnr,htrr⟩ := backend_exec p i d hK q branch f
    (SKChargedExecution.primitives q branch outside χ f).coeff a ha hqa hwa hp
  refine ⟨c1+c2,t,Exec.seq he1 he2,by dsimp [SKRestrictedCandidateExecution.operationBound]; omega,?_,?_,?_,?_,?_,?_⟩
  · simpa only [SKChargedTrialExecution.trial,SKChargedAlgebraExecution.evaluator_value,
      SKChargedPrimitiveExecution.primitives_value] using hv
  · simpa only [SKChargedExecution.evaluate,SKDenseExecution.evaluator_correct,
      SKChargedTrialExecution.directList] using hcoeff
  · intro address haddress; exact (htm address haddress).trans (hm address haddress)
  · intro address haddress; rw [htn address haddress,hn]
  · intro r hr; exact (htnr r hr).trans (han r hr)
  · intro r hr; exact (htrr r hr).trans (har r hr)
end Manuscript.SKCandidateCoefficientOutput
