import Manuscript.RestrictedLocalSum

/-! The local evaluator first generates the local cube in RAM and then runs
the actual spin-term summation. Generated entries are derived, never supplied
as an output or cost hypothesis. The scratch arena begins after edge masks. -/
noncomputable section
namespace Manuscript.RestrictedLocalEvaluation
open RestrictedMachine RestrictedLocalSum

private theorem edgeProduct_memory_ext (N U T : ℕ) (left right : ℕ → ℕ) (weight : ℕ → ℝ)
    (baseE baseW i m : ℕ)
    (h : ∀ j, i ≤ j → j < i + m → left (baseE+j)=right (baseE+j)) :
    RestrictedSpinTerm.edgeProduct N U T left weight baseE baseW i m =
      RestrictedSpinTerm.edgeProduct N U T right weight baseE baseW i m := by
  induction m generalizing i with
  | zero => rfl
  | succ m ih =>
      simp only [RestrictedSpinTerm.edgeProduct]
      rw [h i (by omega) (by omega),ih (i+1) (by intros; apply h <;> omega)]

def generatedData (d : Data) (xs : List ℕ) : Data :=
  {d with natMemory := RestrictedSubsets.writeList d.natMemory d.spinBase xs}

theorem term_generatedData (d : Data) (xs : List ℕ) (T : ℕ)
    (hspace : d.edgeBase+d.M≤d.spinBase) : term (generatedData d xs) T=term d T := by
  unfold term generatedData
  congr 1
  apply edgeProduct_memory_ext
  intro j hj hj'
  apply RestrictedSubsets.writeList_below
  dsimp at hj' ⊢
  omega

theorem sumValue_eq_list (d : Data) (xs : List ℕ) (i : ℕ)
    (h : ∀ (j : ℕ) (hj : j<xs.length), d.natMemory (d.spinBase+i+j)=xs[j]) :
    sumValue d i xs.length=(xs.map (term d)).sum := by
  induction xs generalizing i with
  | nil => simp [sumValue]
  | cons x xs ih =>
      have h0 : d.natMemory (d.spinBase+i)=x := by
        convert h 0 (by simp) using 1 <;> rfl
      simp only [List.length_cons,sumValue,List.map_cons,List.sum_cons,h0]
      congr 1
      apply ih
      intro j hj
      have hh := h (j+1) (by simpa using hj)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem generated_sum (d : Data) (xs : List ℕ) (hspace : d.edgeBase+d.M≤d.spinBase) :
    sumValue (generatedData d xs) 0 xs.length=(xs.map (term d)).sum := by
  rw [sumValue_eq_list]
  · congr 1
    apply List.map_congr_left
    intro T hT
    exact term_generatedData d xs T hspace
  · intro j hj
    simpa [generatedData] using RestrictedSubsets.writeList_get d.natMemory xs d.spinBase j hj

def prefixCode : List Instruction := [.ncopy 220 282, .ncopy 221 280, .ncopy 204 300]
def suffixCode : List Instruction := [.nsub 301 204 300]
def program : RestrictedRecursiveMachine.Program 1 :=
  .seq (.base (code prefixCode))
    (.seq RestrictedCubes.program (.seq (.base (code suffixCode)) (.base RestrictedLocalSum.program)))

def masks (d : Data) : List ℕ := RestrictedCubes.masks d.N d.U 0 1

def cost (d : Data) : ℕ := RestrictedCubes.work d.N d.U+23+
  (termCost d+20)*2^RestrictedCubes.supportSize d.N d.U

/-- Complete operational local average, with generated-cube cost included. -/
theorem program_realized (params : Parameters) (input : Inputs) (s : State)
    (hspace : (data s).edgeBase+(data s).M≤(data s).spinBase) :
    ∃ final, RestrictedRecursiveMachine.Exec RestrictedCubes.table params input program s (cost (data s)) final ∧
      final.realReg 300=((masks (data s)).map (term (data s))).sum ∧
      data final=generatedData (data s) (masks (data s)) ∧
      (∀ r, 310≤r → final.natReg r=s.natReg r) ∧
      (∀ r, 310≤r → final.realReg r=s.realReg r) := by
  let start := runCode params input prefixCode s
  let cubeStart := runCode params input RestrictedCubes.initCode start
  let xs := masks (data s)
  let cubeEnd := RestrictedSubsets.output cubeStart xs
  have hcube : RestrictedRecursiveMachine.Exec RestrictedCubes.table params input RestrictedCubes.program
      start (5+RestrictedCubes.work (data s).N (data s).U) cubeEnd := by
    simpa [start,prefixCode,runCode,step,cubeEnd,cubeStart,xs,masks,data] using
      RestrictedCubes.program_exact params input start
  let ready := runCode params input suffixCode cubeEnd
  have hd : data ready=generatedData (data s) xs := by
    simp [ready,suffixCode,cubeEnd,cubeStart,start,RestrictedCubes.initCode,prefixCode,
      runCode,step,data,generatedData,RestrictedSubsets.output]
  have hlength : ready.natReg 301=xs.length := by
    simp [ready,suffixCode,cubeEnd,cubeStart,start,RestrictedCubes.initCode,prefixCode,
      runCode,step,xs,masks,data]
  obtain ⟨final,hl,hvalue,hdata⟩ := RestrictedLocalSum.program_realized params input ready
  refine ⟨final,?_,?_,hdata.trans hd,?_,?_⟩
  · have he := RestrictedRecursiveMachine.Exec.seq
      (RestrictedRecursiveMachine.Exec.base (exec_code params input prefixCode s))
      (RestrictedRecursiveMachine.Exec.seq hcube
        (RestrictedRecursiveMachine.Exec.seq
          (RestrictedRecursiveMachine.Exec.base (exec_code params input suffixCode cubeEnd))
          (RestrictedRecursiveMachine.Exec.base hl)))
    convert he using 1
    · rfl
    · simp [cost,prefixCode,suffixCode,codeCost,instrCost,hd,hlength,generatedData,termCost,xs,masks]
      omega
  · rw [hd,hlength,generated_sum (data s) xs hspace] at hvalue
    exact hvalue
  · intro r hr
    rw [RestrictedLocalSum.nat_frame hl r hr]
    simp [ready,suffixCode,cubeEnd,cubeStart,start,RestrictedCubes.initCode,prefixCode,runCode,step]
    split_ifs <;> omega
  · intro r hr
    rw [RestrictedLocalSum.real_frame hl r hr]
    simp [ready,suffixCode,cubeEnd,cubeStart,start,RestrictedCubes.initCode,prefixCode,runCode,step]

theorem cost_bound (d : Data) :
    cost d ≤ (termCost d+67*(2*d.N+1)+20)*2^RestrictedCubes.supportSize d.N d.U+23 := by
  have h := RestrictedCubes.work_bound d.N d.U
  unfold cost
  nlinarith

end Manuscript.RestrictedLocalEvaluation
