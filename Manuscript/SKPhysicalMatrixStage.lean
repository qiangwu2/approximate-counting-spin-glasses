import Manuscript.SKPhysicalMatrixFrames

noncomputable section
namespace Manuscript.SKPhysicalMatrixStage
open RestrictedMachine

inductive Kind where
  | outside | branch | direct
  deriving DecidableEq

def rowLabelReg : Kind→ℕ | .outside=>531 | _=>530
def colLabelReg : Kind→ℕ | .direct=>530 | _=>531
def rowsReg : Kind→ℕ | .outside=>200 | _=>230
def colsReg : Kind→ℕ | .direct=>230 | _=>200
def outputReg : Kind→ℕ | .outside=>207 | .branch=>231 | .direct=>445

def setupCode (k : Kind) : List Instruction :=
  [.ncopy 420 (rowLabelReg k),.ncopy 421 (colLabelReg k),
   .ncopy 422 (rowsReg k),.ncopy 423 (colsReg k),.ncopy 424 (outputReg k)]
def program (k : Kind) : Program := .seq (code (setupCode k)) SKPhysicalMatrix.program

def StableNat (r : ℕ) : Prop := r<130 ∨ (132<r ∧ r<380) ∨ (396≤r ∧ r<420) ∨ 430<r

theorem execution (k : Kind) (params : Parameters) (input : Inputs) (s : State)
    (hfit : 2*s.natReg 501≤s.natReg (outputReg k))
    (hrow : ∀i,i<s.natReg (rowsReg k) →
      s.natMem (s.natReg (rowLabelReg k)+i)≤s.natReg 500)
    (hcol : ∀i,i<s.natReg (colsReg k) →
      s.natMem (s.natReg (colLabelReg k)+i)≤s.natReg 500) :
    ∃c t,Exec params input (program k) s c t ∧
      c≤s.natReg (rowsReg k)*s.natReg (colsReg k)*(SKPhysicalMatrix.cost s+5)+21 ∧
      (∀i j,i<s.natReg (rowsReg k) → j<s.natReg (colsReg k) →
        t.realMem (s.natReg (outputReg k)+i*s.natReg (colsReg k)+j)=
        SKPhysicalMatrix.pairValue s (s.natMem (s.natReg (rowLabelReg k)+i))
          (s.natMem (s.natReg (colLabelReg k)+j))) ∧
      t.natMem=s.natMem ∧
      (∀a,(a<s.natReg (outputReg k) ∨
        s.natReg (outputReg k)+s.natReg (rowsReg k)*s.natReg (colsReg k)≤a) →
        t.realMem a=s.realMem a) ∧
      (∀r,StableNat r → t.natReg r=s.natReg r) ∧
      (∀r,391≤r → t.realReg r=s.realReg r) := by
  let a := runCode params input (setupCode k) s
  have ha : a.natReg 420=s.natReg (rowLabelReg k) ∧
      a.natReg 421=s.natReg (colLabelReg k) ∧
      a.natReg 422=s.natReg (rowsReg k) ∧
      a.natReg 423=s.natReg (colsReg k) ∧
      a.natReg 424=s.natReg (outputReg k) := by
    cases k <;> simp [a,setupCode,runCode,step,rowLabelReg,colLabelReg,rowsReg,colsReg,outputReg]
  have am : a.realMem=s.realMem := by simp [a,setupCode,runCode,step]
  have an : a.natMem=s.natMem := by simp [a,setupCode,runCode,step]
  have a500 : a.natReg 500=s.natReg 500 := by simp [a,setupCode,runCode,step]
  have a501 : a.natReg 501=s.natReg 501 := by simp [a,setupCode,runCode,step]
  have arv : a.realReg=s.realReg := by simp [a,setupCode,runCode,step]
  obtain ⟨c,t,he,hb,hi⟩ := SKPhysicalMatrix.execution params input a
    (by rw [a501,ha.2.2.2.2]; exact hfit)
    (by simpa only [ha.1,ha.2.2.1,an,a500] using hrow)
    (by simpa only [ha.2.1,ha.2.2.2.1,an,a500] using hcol)
  have hsetup : codeCost (setupCode k)=10 := by simp [setupCode,codeCost,instrCost]
  have hpre := exec_code params input (setupCode k) s
  rw [hsetup] at hpre
  refine ⟨10+c,t,Exec.seq hpre he,?_,?_,hi.natMem.trans an,?_,?_,?_⟩
  · simp only [ha.2.2.1,ha.2.2.2.1,SKPhysicalMatrix.cost,a500,a501] at hb
    simp only [SKPhysicalMatrix.cost]
    omega
  · intro i j hir hjc
    have hv := SKPhysicalMatrix.computed_at a t hi i j
      (by rw [ha.2.2.1]; exact hir) (by rw [ha.2.2.2.1]; exact hjc)
    rw [ha.2.2.2.2,ha.2.2.2.1,ha.1,ha.2.1,an] at hv
    rw [hv]
    apply SKPhysicalMatrix.pairValue_congr a s a500 a501 an
    · rw [arv]
    · intro q _; rw [am]
  · intro address haway
    rw [hi.frame address,am]
    simpa only [ha.2.2.2.2,ha.2.2.1,ha.2.2.2.1] using haway
  · intro r hr
    rw [SKPhysicalMatrix.natReg_frame params input a t c r he hr]
    have h420 : r≠420 := by simp only [StableNat] at hr; omega
    have h421 : r≠421 := by simp only [StableNat] at hr; omega
    have h422 : r≠422 := by simp only [StableNat] at hr; omega
    have h423 : r≠423 := by simp only [StableNat] at hr; omega
    have h424 : r≠424 := by simp only [StableNat] at hr; omega
    simp [a,setupCode,runCode,step,h420,h421,h422,h423,h424]
  · intro r hr
    rw [SKPhysicalMatrix.realReg_frame params input a t c r he hr,arv]

end Manuscript.SKPhysicalMatrixStage
