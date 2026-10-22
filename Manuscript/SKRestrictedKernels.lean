import Manuscript.RestrictedMachine

/-!
Actual addressed arithmetic kernels for the SK tables.  Inputs to these stage
programs are registers and previously written RAM, not callable real-valued
expressions.  The frame conclusions allow the stages to be composed without
replacing a computed cache by an external oracle.
-/
noncomputable section
namespace Manuscript.SKRestrictedKernels
open RestrictedMachine
open scoped BigOperators

/-- Real 0 accumulates; natural 0/1 are read pointers, 2/3 their strides,
and 4 the iteration count.  Scratch real registers are 1,2,3. -/
def dotBody : List Instruction :=
  [.loadReal 1 0, .loadReal 2 1, .rmul 3 1 2, .radd 0 0 3,
   .nadd 0 0 2, .nadd 1 1 3]

def dotProgram : Program := .repeat 4 (code dotBody)

@[simp] theorem dotBody_cost : codeCost dotBody = 22 := by
  norm_num [dotBody, codeCost, instrCost]

def DotInvariant (s : State) (n : ℕ) (t : State) : Prop :=
  t.realMem = s.realMem ∧ t.natMem = s.natMem ∧
  t.natReg 0 = s.natReg 0+n*s.natReg 2 ∧
  t.natReg 1 = s.natReg 1+n*s.natReg 3 ∧
  (∀ r, r ≠ 0 → r ≠ 1 → t.natReg r = s.natReg r) ∧
  (∀ r, 4 ≤ r → t.realReg r = s.realReg r) ∧
  t.realReg 0 = s.realReg 0 + ∑ i ∈ Finset.range n,
    s.realMem (s.natReg 0+i*s.natReg 2)*
    s.realMem (s.natReg 1+i*s.natReg 3)

theorem dot_invariant_zero (s : State) : DotInvariant s 0 s := by
  simp [DotInvariant]

theorem dot_invariant_step (params : Parameters) (input : Inputs)
    {s t : State} {n : ℕ} (h : DotInvariant s n t) :
    DotInvariant s (n+1) (runCode params input dotBody t) := by
  rcases h with ⟨hm, hn, h0, h1, hnat, hreal, hv⟩
  have h2 := hnat 2 (by decide) (by decide)
  have h3 := hnat 3 (by decide) (by decide)
  simp only [DotInvariant, dotBody, runCode, step,
    writeNatReg_realMem, writeRealReg_realMem, writeNatReg_natMem,
    writeRealReg_natMem, writeNatReg_natReg, writeRealReg_natReg,
    writeNatReg_realReg, writeRealReg_realReg]
  norm_num only
  simp only [ite_true, ite_false]
  refine ⟨hm, hn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0, h2]; ring
  · rw [h1, h3]; ring
  · intro r hr0 hr1
    simp [hr0, hr1, hnat r hr0 hr1]
  · intro r hr
    have hr0 : r ≠ 0 := by omega
    have hr1 : r ≠ 1 := by omega
    have hr2 : r ≠ 2 := by omega
    have hr3 : r ≠ 3 := by omega
    simp [hr0, hr1, hr2, hr3, hreal r hr]
  · rw [hv, hm, h0, h1, Finset.sum_range_succ]
    ring

theorem dot_repeats (params : Parameters) (input : Inputs) (s : State)
    (n : ℕ) :
    ∃ t, Repeats params input (code dotBody) n s (27*n+3) t ∧
      DotInvariant s n t := by
  let F : ℕ → State := fun n => (runCode params input dotBody)^[n] s
  have hi : ∀ i, DotInvariant s i (F i) := by
    intro i
    induction i with
    | zero => exact dot_invariant_zero s
    | succ i ih =>
      simpa only [F, Function.iterate_succ_apply'] using dot_invariant_step params input ih
  refine ⟨F n, ?_, hi n⟩
  have h := repeats_of_steps params input (code dotBody) F (fun _ => 22) n ?_
  · convert h using 1 <;> simp [F] <;> omega
  · intro i _
    simpa only [dotBody_cost, F, Function.iterate_succ_apply'] using
      exec_code params input dotBody (F i)

/-- A runtime-length dot product, with every cache read, multiply, addition,
pointer update, and loop-control operation included. -/
theorem dot_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ t, Exec params input dotProgram s (27*s.natReg 4+5) t ∧
      DotInvariant s (s.natReg 4) t := by
  obtain ⟨t, he, ht⟩ := dot_repeats params input s (s.natReg 4)
  refine ⟨t, ?_, ht⟩
  simpa [dotProgram, Nat.add_assoc] using Exec.repeat he

/-- One accepted dense-algebra coordinate pair.  Natural 0,1,2 hold the
left, right and accumulator addresses, including the case of aliasing. -/
def accumulateBody : List Instruction :=
  [.loadReal 1 0, .loadReal 2 1, .loadReal 0 2, .rmul 3 1 2,
   .radd 0 0 3, .storeReal 2 0]

@[simp] theorem accumulateBody_cost : codeCost accumulateBody = 20 := by
  norm_num [accumulateBody, codeCost, instrCost]

theorem accumulate_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ t, Exec params input (code accumulateBody) s 20 t ∧
      t.realMem = Function.update s.realMem (s.natReg 2)
        (s.realMem (s.natReg 2)+s.realMem (s.natReg 0)*s.realMem (s.natReg 1)) ∧
      t.natMem = s.natMem ∧ t.natReg = s.natReg ∧
      (∀ r, 4 ≤ r → t.realReg r = s.realReg r) := by
  refine ⟨runCode params input accumulateBody s, ?_, ?_⟩
  · simpa using exec_code params input accumulateBody s
  · simp only [accumulateBody, runCode, step, writeRealMem,
      writeRealReg_realReg, writeRealReg_natReg, writeRealReg_realMem,
      writeRealReg_natMem]
    norm_num only
    simp only [ite_true, ite_false]
    refine ⟨trivial, trivial, trivial, ?_⟩
    intro r hr
    have hr0 : r ≠ 0 := by omega
    have hr1 : r ≠ 1 := by omega
    have hr2 : r ≠ 2 := by omega
    have hr3 : r ≠ 3 := by omega
    simp [hr0, hr1, hr2, hr3]

end Manuscript.SKRestrictedKernels
