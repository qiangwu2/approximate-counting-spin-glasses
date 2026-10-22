import Manuscript.RestrictedLocalEvaluation
import Manuscript.RestrictedRecursiveRename
import Manuscript.RestrictedCoefficients

/-! Support-layer control uses the two fixed procedures already verified:
fixed-cardinality subsets and local spin masks. All scalar work is executed
by restricted programs, with persistent parameters and disjoint scratch RAM. -/
noncomputable section
namespace Manuscript.RestrictedHigherLayer
open RestrictedMachine RestrictedLocalSum

def subsetId : Fin 1 → Fin 2 := fun _ => 0
def cubeId : Fin 1 → Fin 2 := fun _ => 1
def table (id : Fin 2) : RestrictedRecursiveMachine.Procedure 2 :=
  if id=0 then RestrictedSubsets.procedure.rename subsetId else RestrictedCubes.procedure.rename cubeId

theorem subset_table (id : Fin 1) : table (subsetId id)=(RestrictedSubsets.table id).rename subsetId := by
  simp [table,subsetId,RestrictedSubsets.table]
theorem cube_table (id : Fin 1) : table (cubeId id)=(RestrictedCubes.table id).rename cubeId := by
  simp [table,cubeId,RestrictedCubes.table]

/-- The visible data retains only the immutable prefix before cube scratch;
its U field is reset because each support iteration supplies a new mask. -/
def visible (d : Data) : Data :=
  {d with U:=0, natMemory:=fun j => if j<d.spinBase then d.natMemory j else 0}

def withSupport (d : Data) (u : ℕ) : Data := {d with U:=u}

def localValue (d : Data) (u : ℕ) : ℝ :=
  ((RestrictedCubes.masks d.N u 0 1).map (term (withSupport d u))).sum

def localCost (d : Data) (u : ℕ) : ℕ := RestrictedLocalEvaluation.cost (withSupport d u)

theorem visible_generated (d : Data) (xs : List ℕ) :
    visible (RestrictedLocalEvaluation.generatedData d xs)=visible d := by
  simp only [visible,RestrictedLocalEvaluation.generatedData]
  congr 1
  funext j
  by_cases hj : j<d.spinBase
  · simp [hj,RestrictedSubsets.writeList_below _ _ _ _ hj]
  · simp [hj]

private theorem term_visible (d : Data) (T : ℕ) (hspace : d.edgeBase+d.M≤d.spinBase) :
    term (withSupport (visible d) d.U) T=term d T := by
  simp only [term,withSupport,visible]
  congr 1
  suffices ∀ (i m : ℕ), i+m≤d.M →
      RestrictedSpinTerm.edgeProduct d.N d.U T
        (fun j => if j<d.spinBase then d.natMemory j else 0)
        d.realMemory d.edgeBase d.weightBase i m =
      RestrictedSpinTerm.edgeProduct d.N d.U T d.natMemory d.realMemory d.edgeBase d.weightBase i m by
    exact this 0 d.M (by omega)
  intro i m
  induction m generalizing i with
  | zero => intros; rfl
  | succ m ih =>
      intro hi
      simp only [RestrictedSpinTerm.edgeProduct]
      rw [if_pos (show d.edgeBase+i<d.spinBase by omega),ih (i+1) (by omega)]

theorem localValue_visible (d : Data) (hspace : d.edgeBase+d.M≤d.spinBase) :
    ((RestrictedLocalEvaluation.masks d).map (term d)).sum=localValue (visible d) d.U := by
  unfold localValue RestrictedLocalEvaluation.masks
  congr 1
  apply List.map_congr_left
  intro T hT
  exact (term_visible d T hspace).symm

def prefixCode : List Instruction := [.nadd 316 312 314, .loadNat 280 316]
def suffixCode : List Instruction := [.rmul 312 310 300, .radd 311 311 312, .nadd 314 314 315]
def body : RestrictedRecursiveMachine.Program 2 :=
  .seq (.base (code prefixCode))
    (.seq (RestrictedLocalEvaluation.program.rename cubeId) (.base (code suffixCode)))

theorem body_realized (params : Parameters) (input : Inputs) (s : State)
    (h1 : s.natReg 315=1)
    (hspace : (data s).edgeBase+(data s).M≤(data s).spinBase) :
    let u := s.natMem (s.natReg 312+s.natReg 314)
    ∃ final, RestrictedRecursiveMachine.Exec table params input body s
        (localCost (visible (data s)) u+19) final ∧
      final.realReg 311=s.realReg 311+s.realReg 310*localValue (visible (data s)) u ∧
      final.natReg 314=s.natReg 314+1 ∧ visible (data final)=visible (data s) ∧
      (∀ r, 310≤r → r≠314 → r≠316 → final.natReg r=s.natReg r) ∧
      final.realReg 310=s.realReg 310 := by
  dsimp only
  let start := runCode params input prefixCode s
  have hs : (data start).edgeBase+(data start).M≤(data start).spinBase := by
    simpa [start,prefixCode,runCode,step,data] using hspace
  obtain ⟨mid,he,hv,hd,hn,hr⟩ := RestrictedLocalEvaluation.program_realized params input start hs
  have hex := he.rename cubeId table cube_table
  have hvisible : visible (data start)=visible (data s) := by
    simp [start,prefixCode,runCode,step,data,visible]
  have hvisibleMid : visible (data mid)=visible (data s) := by
    rw [hd,visible_generated,hvisible]
  have hcost : RestrictedLocalEvaluation.cost (data start)=
      localCost (visible (data s)) (s.natMem (s.natReg 312+s.natReg 314)) := by
    rfl
  have hv' : mid.realReg 300=localValue (visible (data s)) (s.natMem (s.natReg 312+s.natReg 314)) := by
    rw [hv,localValue_visible (data start) hs,hvisible]
    rfl
  have hn' (r : ℕ) (hr' : 310≤r) (hne : r≠316) : mid.natReg r=s.natReg r := by
    rw [hn r hr']
    simp [start,prefixCode,runCode,step,hne]
    omega
  have hr' (r : ℕ) (hr' : 310≤r) : mid.realReg r=s.realReg r := by
    simpa [start,prefixCode,runCode,step] using hr r hr'
  let final := runCode params input suffixCode mid
  refine ⟨final,?_,?_,?_,?_,?_,?_⟩
  · have hh := RestrictedRecursiveMachine.Exec.seq
      (RestrictedRecursiveMachine.Exec.base (exec_code params input prefixCode s))
      (RestrictedRecursiveMachine.Exec.seq hex
        (RestrictedRecursiveMachine.Exec.base (exec_code params input suffixCode mid)))
    convert hh using 1
    · rfl
    · simp [prefixCode,suffixCode,codeCost,instrCost,hcost]
      omega
  · simp [final,suffixCode,runCode,step,hr',hv']
  · simp [final,suffixCode,runCode,step,hn',h1]
  · have hdf : data final=data mid := by simp [final,suffixCode,runCode,step,data]
    rw [hdf,hvisibleMid]
  · intro r hlow h314 h316
    simp [final,suffixCode,runCode,step,hn',hlow,h314,h316]
  · simp [final,suffixCode,runCode,step,hr']

def sumSupports (d : Data) (a : ℝ) (base i : ℕ) : ℕ → ℝ
  | 0 => 0
  | m+1 => a*localValue d (d.natMemory (base+i))+sumSupports d a base (i+1) m

def workSupports (d : Data) (base i : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => localCost d (d.natMemory (base+i))+24+workSupports d base (i+1) m

theorem body_repeats (params : Parameters) (input : Inputs) (m : ℕ) :
    ∀ s : State, s.natReg 315=1 →
      (data s).edgeBase+(data s).M≤(data s).spinBase →
      s.natReg 312+s.natReg 314+m≤(data s).spinBase →
      ∃ final, RestrictedRecursiveMachine.Repeats table params input body m s
          (workSupports (visible (data s)) (s.natReg 312) (s.natReg 314) m+3) final ∧
        final.realReg 311=s.realReg 311+
          sumSupports (visible (data s)) (s.realReg 310) (s.natReg 312) (s.natReg 314) m ∧
        final.natReg 314=s.natReg 314+m ∧ visible (data final)=visible (data s) ∧
        (∀ r, 310≤r → r≠314 → r≠316 → final.natReg r=s.natReg r) ∧
        final.realReg 310=s.realReg 310 := by
  induction m with
  | zero =>
      intro s h1 hspace hbound
      refine ⟨s,?_,?_,by simp,rfl,by intros; rfl,rfl⟩
      · simpa [workSupports] using RestrictedRecursiveMachine.Repeats.zero
          (table := table) (params := params) (input := input) body s
      · simp [sumSupports]
  | succ m ih =>
      intro s h1 hspace hbound
      obtain ⟨mid,he,hv,hi,hd,hn,hr⟩ := body_realized params input s h1 hspace
      have hn312 := hn 312 (by omega) (by omega) (by omega)
      have hn315 := hn 315 (by omega) (by omega) (by omega)
      have hspin : (data mid).spinBase=(data s).spinBase := by
        have hh := congrArg Data.spinBase hd
        exact hh
      have hedge : (data mid).edgeBase=(data s).edgeBase := by
        have hh := congrArg Data.edgeBase hd
        exact hh
      have hM : (data mid).M=(data s).M := by
        have hh := congrArg Data.M hd
        exact hh
      have hspace' : (data mid).edgeBase+(data mid).M≤(data mid).spinBase := by
        rw [hspin,hedge,hM]; exact hspace
      have hbound' : mid.natReg 312+mid.natReg 314+m≤(data mid).spinBase := by
        rw [hn312,hi,hspin]; omega
      obtain ⟨final,hf,hval,hidx,hdata,hn',hr'⟩ := ih mid (hn315.trans h1) hspace' hbound'
      have hread : (visible (data s)).natMemory (s.natReg 312+s.natReg 314)=
          s.natMem (s.natReg 312+s.natReg 314) := by
        simp only [visible,data]
        exact if_pos (by dsimp only [data] at hbound; omega)
      refine ⟨final,?_,?_,?_,hdata.trans hd,?_,hr'.trans hr⟩
      · have hh := RestrictedRecursiveMachine.Repeats.succ he hf
        convert hh using 1
        rw [hd,hn312,hi,workSupports,hread]
        omega
      · rw [hval,hv,hd,hr,hn312,hi,sumSupports,hread]
        ring
      · omega
      · intro r hlow h314 h316
        exact (hn' r hlow h314 h316).trans (hn r hlow h314 h316)

end Manuscript.RestrictedHigherLayer
