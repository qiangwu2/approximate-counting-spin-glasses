import Manuscript.SKPrimitivePath
import Manuscript.SKIndexSpecifications

/-! The primitive return/cycle thresholds and normalization factors are
computed from the runtime color mask, not supplied as real constants. -/
noncomputable section
namespace Manuscript.SKPrimitiveNormalize
open RestrictedMachine IndexGeneration SKBasisEncoding SKIndexSpecifications

def cardSetup : List Instruction := [.ncopy 120 252, .ncopy 121 252, .ncopy 123 201]
def testCode (minimum : ℕ) : List Instruction := [.nconst 260 minimum, .nle 261 260 122]
def divideCode (byCard : Bool) : List Instruction :=
  if byCard then [.rconst 1 2, .natToReal 2 122, .rmul 1 1 2, .rdiv 0 0 1]
  else [.rconst 1 2, .rdiv 0 0 1]
def program (minimum : ℕ) (byCard : Bool) : Program :=
  .seq (code cardSetup) (.seq overlapProgram
    (.seq (code (testCode minimum))
      (.branch 261 (code (divideCode byCard)) (code [.rconst 0 0]))))

theorem normalize_realized {K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (S : Finset (Fin K)) (minimum : ℕ) (byCard : Bool)
    (hK : s.natReg 201=K) (hS : s.natReg 252=(maskEquiv K S).val) :
    ∃ count t, Exec params input (program minimum byCard) s count t ∧
      count ≤ 29*K+33 ∧
      t.realReg 0=(if minimum≤S.card then
        s.realReg 0/(if byCard then 2*S.card else 2) else 0) ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let a := runCode params input cardSetup s
  obtain ⟨co,b,ho,bc,hv⟩ := overlap_execution params input a
  have hc : b.natReg 122=S.card := by
    simpa [a,cardSetup,runCode,step,hK,hS,overlapFold_self] using hv
  have hr : b.realReg 0=s.realReg 0 := by
    have hframe : b.realReg 0=a.realReg 0 := by
      apply ho.realReg_frame
      simp [overlapProgram,overlapInit,overlapBody,code,Program.All,Instruction.realDestination]
    simpa [a,cardSetup,runCode,step] using hframe
  have hm : b.realMem=s.realMem := by
    simpa [a,cardSetup,runCode,step] using (overlap_memory_frame params input a b co ho).1
  have hn : b.natMem=s.natMem := by
    simpa [a,cardSetup,runCode,step] using (overlap_memory_frame params input a b co ho).2
  have bco : co≤29*K+7 := by simpa [a,cardSetup,runCode,step,hK] using bc
  let d := runCode params input (testCode minimum) b
  have hd : d.natReg 261=if minimum≤S.card then 1 else 0 := by
    simp [d,testCode,runCode,step,hc]
  by_cases hmin : minimum≤S.card
  · have hflag : d.natReg 261 ≠ 0 := by rw [hd]; simp [hmin]
    let t := runCode params input (divideCode byCard) d
    refine ⟨6+(co+(5+(codeCost (divideCode byCard)+3))),t,?_,?_,?_,?_,?_⟩
    · exact Exec.seq (exec_code params input cardSetup s) (Exec.seq ho
        (Exec.seq (exec_code params input (testCode minimum) b)
          (Exec.branchNonzero hflag (exec_code params input (divideCode byCard) d))))
    · have hh : codeCost (divideCode byCard)≤12 := by cases byCard <;> norm_num [divideCode,codeCost,instrCost]
      omega
    · cases byCard <;> simp [t,d,divideCode,testCode,runCode,step,hc,hr,hmin]
    · cases byCard <;> simp [t,d,divideCode,testCode,runCode,step,hm]
    · cases byCard <;> simp [t,d,divideCode,testCode,runCode,step,hn]
  · have hflag : d.natReg 261=0 := by rw [hd]; simp [hmin]
    let t := runCode params input [.rconst 0 0] d
    refine ⟨6+(co+(5+(1+3))),t,?_,by omega,?_,?_,?_⟩
    · exact Exec.seq (exec_code params input cardSetup s) (Exec.seq ho
        (Exec.seq (exec_code params input (testCode minimum) b)
          (Exec.branchZero hflag (exec_code params input [.rconst 0 0] d))))
    · simp [t,d,testCode,runCode,step,hmin]
    · simp [t,d,testCode,runCode,step,hm]
    · simp [t,d,testCode,runCode,step,hn]

end Manuscript.SKPrimitiveNormalize
