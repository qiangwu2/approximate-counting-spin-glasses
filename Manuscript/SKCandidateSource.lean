import Manuscript.SKCandidateMatrices
import Manuscript.SKGeneratedLabelMemory
import Manuscript.SKCandidateLayout

noncomputable section
namespace Manuscript.SKCandidateSource
open RestrictedMachine RestrictedMaskBridge SKGeneratedLabels SpinGlass

def paletteCode : List Instruction := [.nconst 201 2,.nmul 201 201 512]
def program : Program := .seq (code paletteCode)
  (.seq RestrictedCandidateLabelPreparation.program SKCandidateMatrices.program)

/-- The source layout is determined by input dimensions and the generated
ascending branch/complement lists. All its addresses are computed by the program. -/
def layout {N : ℕ} (s : State) (A : Finset (Fin N)) : SKCandidateLayout.Layout where
  root := {
    N := outsideCount A
    K := 2*s.natReg 512
    B := branchCount A
    colorBase := s.natReg 533
    weightBase := 2*s.natReg 501
    branchBase := 2*s.natReg 501+outsideCount A*outsideCount A
    arena := 2*s.natReg 501+outsideCount A*outsideCount A+
      branchCount A*outsideCount A+branchCount A*branchCount A
    weightFit := by omega
    branchFit := by omega }
  chargeBase := s.natReg 532
  branchWeightBase := 2*s.natReg 501+outsideCount A*outsideCount A+branchCount A*outsideCount A
  metadataBase := s.natReg 533+s.natReg 500+1
  ghost := ghost A
  retained := s.natReg 512
  branchWeightFit := by rfl

def rawColor {N : ℕ} (s : State) (input : Inputs) (A : Finset (Fin N))
    (hL : 0<s.natReg 512) (j : Fin (outsideCount A)) : Fin (2*s.natReg 512) :=
  ⟨input.nat (s.natReg 522+(outsideVertex A j).val)%(2*s.natReg 512),
    Nat.mod_lt _ (by omega)⟩

structure PhysicalData {N M : ℕ} (order : Fin M≃Model.Edge N {2})
    (a : ℕ→ℝ) (beta h : ℝ) (J : Model.Edge N {2}→ℝ) (s : State) : Prop where
  size : s.natReg 500=N
  count : s.natReg 501=M
  mean : s.realReg 504=Real.tanh h
  edges : ∀i:Fin M,s.natMem i.val=encode (order i).val
  weights : ∀i:Fin M,s.realMem (2*i.val)=Real.tanh (Model.coefficient N {2} a beta J (order i))

def operationBound {N : ℕ} (s : State) (A : Finset (Fin N)) :=
  112*N+75+(outsideCount A*outsideCount A+branchCount A*outsideCount A+branchCount A*branchCount A)*
    (18*N+34*s.natReg 501+96)+111

structure Ready {N : ℕ} (s : State) (input : Inputs) (A : Finset (Fin N))
    (hL : 0<s.natReg 512) (f : Finset (Option (Fin N))→ℝ) (t : State) : Prop where
  roots : SKRootCache.InputsReady (layout s A).root (rawColor s input A hL)
    (fun x y=>SKFastEvaluator.pairWeight f (outside A x) (outside A y))
    (fun x y=>SKFastEvaluator.pairWeight f (branch A x) (outside A y)) t
  shape : SKCandidateLayout.Inputs (layout s A) t
  charges : ∀i:Fin (branchCount A),t.natMem ((layout s A).chargeBase+i.val)=
    (if branch A i=none then 0 else 1)
  direct : ∀i j:Fin (branchCount A),
    t.realMem ((layout s A).branchWeightBase+i.val*branchCount A+j.val)=
      SKFastEvaluator.pairWeight f (branch A i) (branch A j)
  physicalNat : ∀i,i<s.natReg 530 → t.natMem i=s.natMem i
  physicalReal : ∀i,i<2*s.natReg 501 → t.realMem i=s.realMem i
  natFrame : ∀r,500≤r → r<540 ∨ 550≤r → t.natReg r=s.natReg r
  realFrame : ∀r,500≤r → t.realReg r=s.realReg r

theorem program_exec {N M : ℕ} (params : Parameters) (input : Inputs)
    (order : Fin M≃Model.Edge N {2}) (aCoeff : ℕ→ℝ) (beta h : ℝ)
    (J : Model.Edge N {2}→ℝ) (s : State) (A : Finset (Fin N))
    (hL : 0<s.natReg 512) (hA : s.natReg 520=encode A)
    (hphysical : PhysicalData order aCoeff beta h J s)
    (hmaskFit : M≤s.natReg 530) (hlayout : RestrictedCandidateLabelPreparation.Layout s) :
    ∃c t,Exec params input program s c t ∧ c≤operationBound s A ∧
      Ready s input A hL (SKAugmentFinset.edgeWeight h (SKGhostCoefficient.inputWeight N aCoeff beta J)) t := by
  let a := runCode params input paletteCode s
  have af (r : ℕ) (hr : r≠201) : a.natReg r=s.natReg r := by
    simp [a,paletteCode,runCode,step,hr]
  have ak : a.natReg 201=2*s.natReg 512 := by simp [a,paletteCode,runCode,step]
  have an : a.natMem=s.natMem := by simp [a,paletteCode,runCode,step]
  have am : a.realMem=s.realMem := by simp [a,paletteCode,runCode,step]
  have ar : a.realReg=s.realReg := by simp [a,paletteCode,runCode,step]
  have al : RestrictedCandidateLabelPreparation.Layout a := by
    constructor
    · simpa [a,paletteCode,runCode,step] using hlayout.branch_before
    · simpa [a,paletteCode,runCode,step] using hlayout.outside_before
    · simpa [a,paletteCode,runCode,step] using hlayout.charge_before
  obtain ⟨c1,b,he1,hb,bc1⟩ := RestrictedCandidateLabelPreparation.program_exec params input a al
  have bn (r : ℕ) (hr : 500≤r) (hw : r<540 ∨ 550≤r) : b.natReg r=s.natReg r :=
    (hb.nat_frame r hr hw).trans (af r (by omega))
  have bk : b.natReg 201=2*s.natReg 512 :=
    (RestrictedCandidateLabelPreparation.palette_frame he1).trans ak
  have lm := label_memory A input a b ((af 500 (by omega)).trans hphysical.size)
    ((af 520 (by omega)).trans hA) hb
  have bp : PhysicalData order aCoeff beta h J b := by
    refine ⟨(bn 500 (by omega) (by omega)).trans hphysical.size,
      (bn 501 (by omega) (by omega)).trans hphysical.count,?_,?_,?_⟩
    · rw [hb.real_frame,ar];exact hphysical.mean
    · intro i
      rw [hb.nat_below i.val (by rw [af 530 (by omega)];have:=i.isLt;omega),an]
      exact hphysical.edges i
    · intro i;rw [hb.real_memory,am];exact hphysical.weights i
  have bread (i : Fin (branchCount A)) :
      b.natMem (b.natReg 530+i.val)=branchNat A i := by
    rw [bn 530 (by omega) (by omega),←af 530 (by omega)];exact lm.branchRead i
  have uread (i : Fin (outsideCount A)) :
      b.natMem (b.natReg 531+i.val)=(outsideVertex A i).val := by
    rw [bn 531 (by omega) (by omega),←af 531 (by omega)];exact lm.outsideRead i
  obtain ⟨c2,t,he2,bc2,hrs,hn,hu,hbu,hbb,hf,htn,htr⟩ := SKCandidateMatrices.execution params input b
    (by intro j hj;rw [lm.branches] at hj;rw [bread ⟨j,hj⟩,bp.size];exact branchNat_le A ⟨j,hj⟩)
    (by intro j hj;rw [lm.outsideCount] at hj;rw [uread ⟨j,hj⟩,bp.size];exact Nat.le_of_lt (outsideVertex A ⟨j,hj⟩).isLt)
  rcases hrs with ⟨r200,r201,r204,r230,r207,r231,r232,r400,r401,r402,r403,r417⟩
  have pair (u v : ℕ) (hu : u≤N) (hv : v≤N) :=
    SKPhysicalPairCanonical.pairValue_eq order aCoeff beta h J b bp.size bp.count bp.mean bp.edges bp.weights u v hu hv
  have b501 : b.natReg 501=s.natReg 501 := bn 501 (by omega) (by omega)
  have b533 : b.natReg 533=s.natReg 533 := bn 533 (by omega) (by omega)
  refine ⟨5+(c1+c2),t,Exec.seq (exec_code params input paletteCode s) (Exec.seq he1 he2),?_,?_⟩
  · simp only [SKPhysicalMatrix.cost,lm.branches,lm.outsideCount,bp.size,b501] at bc2
    rw [af 500 (by omega),hphysical.size] at bc1
    have he : 18*N+34*s.natReg 501+91+5=18*N+34*s.natReg 501+96 := by omega
    rw [he] at bc2
    dsimp [operationBound]
    omega
  · constructor
    · refine ⟨r200.trans lm.outsideCount,r201.trans bk,?_,?_,r230.trans lm.branches,?_,?_,?_,?_,?_⟩
      · exact r204.trans (hb.color_base.trans (af 533 (by omega)))
      · simpa [SKCandidateMatrices.outsideBase,b501,layout] using r207
      · simpa [SKCandidateMatrices.branchBase,SKCandidateMatrices.outsideBase,b501,lm.outsideCount,layout] using r231
      · simpa [SKCandidateMatrices.arena,SKCandidateMatrices.directBase,SKCandidateMatrices.branchBase,
          SKCandidateMatrices.outsideBase,b501,lm.outsideCount,lm.branches,layout] using r232
      · intro j
        change t.natMem (s.natReg 533+j.val)=_
        rw [hn,←af 533 (by omega),lm.colorRead]
        simp [rawColor,ak,af 522 (by omega)]
      · intro i j
        have hv := hu i.val j.val (by rw [lm.outsideCount];exact i.isLt) (by rw [lm.outsideCount];exact j.isLt)
        rw [uread i,uread j,pair _ _ (Nat.le_of_lt (outsideVertex A i).isLt) (Nat.le_of_lt (outsideVertex A j).isLt),
          decode_outside,decode_outside] at hv
        simpa only [layout,SKCandidateMatrices.outsideBase,b501,lm.outsideCount] using hv
      · intro i j
        have hv := hbu i.val j.val (by rw [lm.branches];exact i.isLt) (by rw [lm.outsideCount];exact j.isLt)
        rw [bread i,uread j,pair _ _ (branchNat_le A i) (Nat.le_of_lt (outsideVertex A j).isLt),
          decode_branch,decode_outside] at hv
        simpa only [layout,SKCandidateMatrices.branchBase,SKCandidateMatrices.outsideBase,b501,lm.outsideCount] using hv
    · refine ⟨?_,?_,?_,?_,?_⟩
      · simpa [layout,bn 532 (by omega) (by omega)] using r400
      · simpa [layout,SKCandidateMatrices.directBase,SKCandidateMatrices.branchBase,
          SKCandidateMatrices.outsideBase,b501,lm.outsideCount,lm.branches] using r401
      · simpa [layout,b533,bn 500 (by omega) (by omega)] using r402
      · simpa [layout,lm.branches,branchCount,ghost] using r403
      · simpa [layout,bn 512 (by omega) (by omega)] using r417
    · intro i;change t.natMem (s.natReg 532+i.val)=_
      rw [hn,←af 532 (by omega)];exact lm.chargeRead i
    · intro i j
      have hv := hbb i.val j.val (by rw [lm.branches];exact i.isLt) (by rw [lm.branches];exact j.isLt)
      rw [bread i,bread j,pair _ _ (branchNat_le A i) (branchNat_le A j),decode_branch,decode_branch] at hv
      simpa only [layout,SKCandidateMatrices.directBase,SKCandidateMatrices.branchBase,
        SKCandidateMatrices.outsideBase,b501,lm.outsideCount,lm.branches] using hv
    · intro i hi;rw [hn,hb.nat_below i (by rw [af 530 (by omega)];exact hi),an]
    · intro i hi;rw [hf i (by rw [b501];exact hi),hb.real_memory,am]
    · intro r hr hw;rw [htn r hr,bn r hr hw]
    · intro r hr;rw [htr r (by omega),hb.real_frame,ar]

end Manuscript.SKCandidateSource
