import Manuscript.RestrictedScalars

noncomputable section
namespace Manuscript.RestrictedSKFinish
open RestrictedMachine

def setup : List Instruction := [.rcopy 0 600,.rcopy 1 572]
def program : Program := .seq (code setup) RestrictedScalars.finish

theorem program_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ count t,Exec params input program s count t ∧ count≤19 ∧
      t.realReg 3=SpinGlass.logOutput (s.realReg 600) (s.realReg 572) := by
  let ready:=runCode params input setup s
  obtain ⟨c,t,he,hc,hv,_,_⟩:=RestrictedScalars.finish_exec params input ready
  refine ⟨4+c,t,Exec.seq (exec_code params input setup s) he,by omega,?_⟩
  simpa [ready,setup,runCode,step] using hv

end Manuscript.RestrictedSKFinish
