import Manuscript.RestrictedParameters
import Manuscript.RestrictedHighFrames

noncomputable section
namespace Manuscript.RestrictedHigherControl
open RestrictedMachine RestrictedControl RestrictedParameters

def setup : List Instruction := [.ncopy 200 500,.rcopy 200 508,.rcopy 201 500,.rcopy 202 504]
def finish : List Instruction := [.ncopy 510 201]
def program (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) : Program :=
  .seq (code setup) (.seq (higherProgram (controlBase pmax)
    (manuscriptHigherDesign pmax P a B rho pmin).threshold) (code finish))

theorem program_exec (input : Inputs) (s : State) (pmax : ℕ) (P : Finset ℕ)
    (a : ℕ → ℝ) (B rho pmin : ℝ) :
    ∃ count t, Exec (higher pmax P a B rho pmin) input (program pmax P a B rho pmin) s count t ∧
      count ≤ 78*s.natReg 500+230 ∧
      t.natReg 510=(HigherOrderExecution.control (s.natReg 500) pmax P a B rho pmin
        (s.realReg 500) (s.realReg 508) (s.realReg 504)).cutoff ∧
      (∀ r, 500 ≤ r → r ≠ 510 → t.natReg r=s.natReg r) ∧
      (∀ r, 500 ≤ r → t.realReg r=s.realReg r) ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let params := higher pmax P a B rho pmin
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 8 u := exec_code _ _ _ _
  obtain ⟨c,v,hv,hc,hval,hrm,hnm⟩ := higher_control_execution input u (controlBase pmax)
    (background pmax a (LogApprox.constant P a B rho) (LogApprox.exponent P a B)) pmax P a B rho pmin
  have vn (r : ℕ) (hr : 500 ≤ r) : v.natReg r=s.natReg r := by
    apply (hv.natReg_frame (RestrictedHighFrames.higher _ _ r (by omega)).1).trans
    exact hu.natReg_frame (by simp [setup,code,Program.All,Instruction.natDestination]; omega)
  have vr (r : ℕ) (hr : 500 ≤ r) : v.realReg r=s.realReg r := by
    apply (hv.realReg_frame (RestrictedHighFrames.higher _ _ r (by omega)).2).trans
    exact hu.realReg_frame (by simp [setup,code,Program.All,Instruction.realDestination]; omega)
  let t := runCode params input finish v
  have ht : Exec params input (code finish) v 2 t := exec_code _ _ _ _
  refine ⟨8+(c+2),t,Exec.seq hu (Exec.seq hv ht),?_,?_,?_,?_,hrm,hnm⟩
  · have un : u.natReg 200=s.natReg 500 := by simp [u,setup,runCode,step]
    rw [un] at hc; omega
  · simpa [t,finish,u,setup,runCode,step] using hval
  · intro r hr h510; simp [t,finish,runCode,step,h510,vn r hr]
  · intro r hr; exact vr r hr

end Manuscript.RestrictedHigherControl
