import Manuscript.RestrictedLayerSemantics

noncomputable section
namespace Manuscript.RestrictedSupportProgram
open RestrictedMachine RestrictedLocalSum RestrictedHigherLayer RestrictedLayerSemantics

def suffixCode : List Instruction := [.radd 330 330 311,.nadd 311 311 331]
def body : RestrictedRecursiveMachine.Program 2 :=
  .seq RestrictedLayerProgram.program (.base (code suffixCode))
def initCode : List Instruction :=
  [.rconst 330 0,.nconst 311 0,.nconst 331 1,.nadd 330 310 331]
def program : RestrictedRecursiveMachine.Program 2 :=
  .seq (.base (code initCode)) (.repeat 330 body)

def totalValue (d : Data) (k : ℕ) : ℕ → ℕ → ℝ
  | _,0 => 0
  | i,m+1 => RestrictedLayerSemantics.value d k i+totalValue d k (i+1) m

def totalCost (d : Data) (k : ℕ) : ℕ → ℕ → ℕ
  | _,0 => 0
  | i,m+1 => RestrictedLayerSemantics.cost d k i+13+totalCost d k (i+1) m

theorem body_realized (params : Parameters) (input : Inputs) (s : State)
    (h1 : s.natReg 331=1) (hspace : s.natReg 284+s.natReg 283≤s.natReg 312) :
    ∃ final, RestrictedRecursiveMachine.Exec table params input body s
        (RestrictedLayerSemantics.cost (core (data s)) (s.natReg 310) (s.natReg 311)+8) final ∧
      final.realReg 330=s.realReg 330+
        RestrictedLayerSemantics.value (core (data s)) (s.natReg 310) (s.natReg 311) ∧
      final.natReg 311=s.natReg 311+1 ∧ core (data final)=core (data s) ∧
      final.natReg 310=s.natReg 310 ∧ final.natReg 312=s.natReg 312 ∧ final.natReg 331=1 ∧
      (∀ r, 340≤r → final.natReg r=s.natReg r) ∧
      (∀ r, 340≤r → final.realReg r=s.realReg r) := by
  obtain ⟨mid,he,hv,hd,hn⟩ := RestrictedLayerSemantics.program_realized params input s hspace
  have h310 := hn 310 (by omega) (by omega) (by omega) (by omega) (by omega)
  have h311 := hn 311 (by omega) (by omega) (by omega) (by omega) (by omega)
  have h312 := hn 312 (by omega) (by omega) (by omega) (by omega) (by omega)
  have h331 := RestrictedLayerProgram.nat_frame he (r:=331) (by omega)
  have h330 := RestrictedLayerProgram.real_frame he (r:=330) (by omega)
  let final := runCode params input suffixCode mid
  refine ⟨final,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := RestrictedRecursiveMachine.Exec.seq he
      (RestrictedRecursiveMachine.Exec.base (exec_code params input suffixCode mid))
    simpa [body,suffixCode,codeCost,instrCost,final] using hh
  · simp [final,suffixCode,runCode,step,hv,h330]
  · simp [final,suffixCode,runCode,step,h311,h331,h1]
  · have hh : data final=data mid := by simp [final,suffixCode,runCode,step,data]
    rw [hh,hd]
  · simp [final,suffixCode,runCode,step,h310]
  · simp [final,suffixCode,runCode,step,h312]
  · simp [final,suffixCode,runCode,step,h331,h1]
  · intro r hr
    have hh := RestrictedLayerProgram.nat_frame he (r:=r) (by omega)
    simp [final,suffixCode,runCode,step,show r≠311 by omega,hh]
  · intro r hr
    have hh := RestrictedLayerProgram.real_frame he (r:=r) (by omega)
    simp [final,suffixCode,runCode,step,show r≠330 by omega,hh]

theorem body_repeats (params : Parameters) (input : Inputs) (m : ℕ) :
    ∀ s : State, s.natReg 331=1 → s.natReg 284+s.natReg 283≤s.natReg 312 →
    ∃ final, RestrictedRecursiveMachine.Repeats table params input body m s
        (totalCost (core (data s)) (s.natReg 310) (s.natReg 311) m+3) final ∧
      final.realReg 330=s.realReg 330+totalValue (core (data s)) (s.natReg 310) (s.natReg 311) m ∧
      core (data final)=core (data s) ∧
      final.natReg 310=s.natReg 310 ∧ final.natReg 312=s.natReg 312 ∧
      (∀ r, 340≤r → final.natReg r=s.natReg r) ∧
      (∀ r, 340≤r → final.realReg r=s.realReg r) := by
  induction m with
  | zero =>
      intro s h1 hs
      refine ⟨s,?_,by simp [totalValue],rfl,rfl,rfl,by intros; rfl,by intros; rfl⟩
      simpa [totalCost] using RestrictedRecursiveMachine.Repeats.zero
        (table:=table) (params:=params) (input:=input) body s
  | succ m ih =>
      intro s h1 hs
      obtain ⟨mid,he,hv,hi,hd,hk,hbase,h1',hn,hr⟩ := body_realized params input s h1 hs
      have hE : mid.natReg 284=s.natReg 284 := by
        have hh := congrArg Data.edgeBase hd; exact hh
      have hM : mid.natReg 283=s.natReg 283 := by
        have hh := congrArg Data.M hd; exact hh
      have hs' : mid.natReg 284+mid.natReg 283≤mid.natReg 312 := by rw [hE,hM,hbase]; exact hs
      obtain ⟨final,hf,hval,hdata,hk',hbase',hn',hr'⟩ := ih mid h1' hs'
      refine ⟨final,?_,?_,hdata.trans hd,hk'.trans hk,hbase'.trans hbase,?_,?_⟩
      · have hh := RestrictedRecursiveMachine.Repeats.succ he hf
        convert hh using 1
        rw [hd,hk,hi,totalCost]; omega
      · rw [hval,hv,hd,hk,hi,totalValue]; ring
      · intro r hlow; exact (hn' r hlow).trans (hn r hlow)
      · intro r hlow; exact (hr' r hlow).trans (hr r hlow)

/-- One fixed finite-procedure program computes every retained support
layer. Parent registers at least 340 survive the whole evaluation. -/
theorem program_realized (params : Parameters) (input : Inputs) (s : State)
    (hspace : s.natReg 284+s.natReg 283≤s.natReg 312) :
    ∃ final, RestrictedRecursiveMachine.Exec table params input program s
        (totalCost (core (data s)) (s.natReg 310) 0 (s.natReg 310+1)+12) final ∧
      final.realReg 330=totalValue (core (data s)) (s.natReg 310) 0 (s.natReg 310+1) ∧
      core (data final)=core (data s) ∧
      (∀ r, 340≤r → final.natReg r=s.natReg r) ∧
      (∀ r, 340≤r → final.realReg r=s.realReg r) := by
  let start := runCode params input initCode s
  have hs : start.natReg 284+start.natReg 283≤start.natReg 312 := by
    simpa [start,initCode,runCode,step] using hspace
  obtain ⟨final,he,hv,hd,hk,hbase,hn,hr⟩ := body_repeats params input (s.natReg 310+1) start
    (by simp [start,initCode,runCode,step]) hs
  have hdata : data start=data s := by simp [start,initCode,runCode,step,data]
  have hregs : start.natReg 310=s.natReg 310 ∧ start.natReg 311=0 ∧
      start.natReg 330=s.natReg 310+1 ∧ start.realReg 330=0 := by
    simp [start,initCode,runCode,step]
  have he' : RestrictedRecursiveMachine.Repeats table params input body (start.natReg 330) start
      (totalCost (core (data start)) (start.natReg 310) (start.natReg 311) (s.natReg 310+1)+3) final := by
    simpa [hregs.2.2.1] using he
  refine ⟨final,?_,?_,hd.trans (congrArg core hdata),?_,?_⟩
  · have hh := RestrictedRecursiveMachine.Exec.seq
      (RestrictedRecursiveMachine.Exec.base (exec_code params input initCode s))
      (RestrictedRecursiveMachine.Exec.repeat he')
    convert hh using 1
    · rfl
    · simp [initCode,codeCost,instrCost,hdata,hregs]
      omega
  · simpa [hdata,hregs] using hv
  · intro r hlow
    rw [hn r hlow]
    simp [start,initCode,runCode,step,show r≠311 by omega,show r≠330 by omega,show r≠331 by omega]
  · intro r hlow
    rw [hr r hlow]
    simp [start,initCode,runCode,step,show r≠330 by omega]

end Manuscript.RestrictedSupportProgram
