import Manuscript.SKRestrictedKernels
import SpinGlass.SKDenseExecution

/-! Uniform consumption of computed SK multiplication metadata.  The metadata
RAM contains four natural words per pair: acceptance flag and three addressed
real operands.  This module proves actual branch/control and cache accesses;
the metadata must be constructed by a preceding natural-register program. -/
noncomputable section
namespace Manuscript.SKRestrictedScatter
open RestrictedMachine SKRestrictedKernels

/-- Natural 5 points to the next metadata record and natural 6 contains one. -/
def header : List Instruction :=
  [.loadNat 7 5, .nadd 5 5 6, .loadNat 0 5, .nadd 5 5 6,
   .loadNat 1 5, .nadd 5 5 6, .loadNat 2 5, .nadd 5 5 6]

def body : Program :=
  .seq (code header) (.branch 7 (code accumulateBody) .skip)

def program : Program := .repeat 4 body

def memoryStep (metadata : ℕ → ℕ) (p : ℕ) (memory : ℕ → ℝ) : ℕ → ℝ :=
  if metadata p = 0 then memory else
    Function.update memory (metadata (p+3))
      (memory (metadata (p+3))+memory (metadata (p+1))*memory (metadata (p+2)))

def memoryLoop (metadata : ℕ → ℕ) (p : ℕ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, memory => memory
  | n+1, memory => memoryStep metadata (p+4*n) (memoryLoop metadata p n memory)

def next (params : Parameters) (input : Inputs) (s : State) : State :=
  let t := runCode params input header s
  if t.natReg 7 = 0 then t else runCode params input accumulateBody t

@[simp] theorem header_cost : codeCost header = 28 := by
  norm_num [header, codeCost, instrCost]

theorem header_values (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 6 = 1) :
    let t := runCode params input header s
    t.realReg = s.realReg ∧ t.realMem = s.realMem ∧ t.natMem = s.natMem ∧
    t.natReg 7 = s.natMem (s.natReg 5) ∧
    t.natReg 0 = s.natMem (s.natReg 5+1) ∧
    t.natReg 1 = s.natMem (s.natReg 5+2) ∧
    t.natReg 2 = s.natMem (s.natReg 5+3) ∧
    t.natReg 5 = s.natReg 5+4 ∧
    (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → r ≠ 7 → t.natReg r = s.natReg r) := by
  simp only [header, runCode, step, writeNatReg_realReg,
    writeNatReg_realMem, writeNatReg_natMem, writeNatReg_natReg]
  norm_num
  simp only [hone, Nat.add_assoc]
  norm_num
  intro r h0 h1 h2 h5 h7
  simp [h0, h1, h2, h5, h7]

theorem next_exec (params : Parameters) (input : Inputs) (s : State) :
    Exec params input body s
      (if (runCode params input header s).natReg 7 = 0 then 31 else 51)
      (next params input s) := by
  have hh : Exec params input (code header) s 28 (runCode params input header s) := by
    simpa using exec_code params input header s
  by_cases hz : (runCode params input header s).natReg 7 = 0
  · simpa [body, next, hz] using Exec.seq hh
      (Exec.branchZero (yes := code accumulateBody) hz (Exec.skip _))
  · have ha : Exec params input (code accumulateBody) (runCode params input header s) 20
        (runCode params input accumulateBody (runCode params input header s)) := by
      simpa using exec_code params input accumulateBody (runCode params input header s)
    simpa [body, next, hz] using Exec.seq hh
      (Exec.branchNonzero (no := .skip) hz ha)

theorem next_values (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 6 = 1) :
    let t := next params input s
    t.realMem = memoryStep s.natMem (s.natReg 5) s.realMem ∧
    t.natMem = s.natMem ∧ t.natReg 5 = s.natReg 5+4 ∧
    (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → r ≠ 7 → t.natReg r = s.natReg r) ∧
    (∀ r, 4 ≤ r → t.realReg r = s.realReg r) := by
  rcases header_values params input s hone with
    ⟨hr, hm, hn, h7, h0, h1, h2, h5, hf⟩
  dsimp only
  dsimp only [next]
  by_cases hz : (runCode params input header s).natReg 7 = 0
  · simp only [hz, ite_true]
    have hz' : s.natMem (s.natReg 5) = 0 := by simpa [h7] using hz
    exact ⟨by simp [memoryStep, hz', hm], hn, h5, hf, fun r _ => congrFun hr r⟩
  · simp only [hz, ite_false]
    have hz' : s.natMem (s.natReg 5) ≠ 0 := by simpa [h7] using hz
    simp only [accumulateBody, runCode, step, writeRealMem,
      writeRealReg_realReg, writeRealReg_realMem, writeRealReg_natReg,
      writeRealReg_natMem]
    norm_num
    simp only [hm, hn, h0, h1, h2, h5]
    refine ⟨by simp [memoryStep, hz'], trivial, trivial, hf, ?_⟩
    intro r hr4
    have hr0 : r ≠ 0 := by omega
    have hr1 : r ≠ 1 := by omega
    have hr2 : r ≠ 2 := by omega
    have hr3 : r ≠ 3 := by omega
    simp [hr0, hr1, hr2, hr3, hr]

def Invariant (s : State) (n : ℕ) (t : State) : Prop :=
  t.realMem = memoryLoop s.natMem (s.natReg 5) n s.realMem ∧
  t.natMem = s.natMem ∧ t.natReg 5 = s.natReg 5+4*n ∧
  (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → r ≠ 7 → t.natReg r = s.natReg r) ∧
  (∀ r, 4 ≤ r → t.realReg r = s.realReg r)

theorem invariant_step (params : Parameters) (input : Inputs) {s t : State} {n : ℕ}
    (hone : s.natReg 6 = 1) (h : Invariant s n t) :
    Invariant s (n+1) (next params input t) := by
  rcases h with ⟨hm, hn, hp, hnat, hreal⟩
  have htone : t.natReg 6 = 1 := by rw [hnat 6 (by decide) (by decide) (by decide) (by decide) (by decide), hone]
  rcases next_values params input t htone with ⟨hm', hn', hp', hnat', hreal'⟩
  refine ⟨?_, hn'.trans hn, ?_, ?_, ?_⟩
  · rw [hm', hm, hn, hp]; rfl
  · rw [hp', hp]; omega
  · intro r h0 h1 h2 h5 h7
    exact (hnat' r h0 h1 h2 h5 h7).trans (hnat r h0 h1 h2 h5 h7)
  · intro r hr
    exact (hreal' r hr).trans (hreal r hr)

/-- A fixed program executes a runtime number of metadata records. Its cost
includes rejected pairs, four addressed metadata reads, pointer advances,
branching, all scalar/cache operations, and bounded-loop control. -/
theorem program_realized (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 6 = 1) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 56*s.natReg 4+5 ∧ Invariant s (s.natReg 4) t := by
  let F : ℕ → State := fun n => (next params input)^[n] s
  let cost : ℕ → ℕ := fun n =>
    if (runCode params input header (F n)).natReg 7 = 0 then 31 else 51
  have hi : ∀ n, Invariant s n (F n) := by
    intro n
    induction n with
    | zero => simp [Invariant, F, memoryLoop]
    | succ n ih =>
      simpa only [F, Function.iterate_succ_apply'] using invariant_step params input hone ih
  have he := repeats_of_steps params input body F cost (s.natReg 4) (by
    intro i _
    simpa only [cost, F, Function.iterate_succ_apply'] using next_exec params input (F i))
  have hb : (∑ i ∈ Finset.range (s.natReg 4), cost i) ≤ 51*s.natReg 4 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range (s.natReg 4), 51 := by
        apply Finset.sum_le_sum; intro i _; dsimp [cost]; split <;> omega
      _ = _ := by simp [Nat.mul_comm]
  refine ⟨(∑ i ∈ Finset.range (s.natReg 4), cost i)+5*s.natReg 4+3+2,
    F (s.natReg 4), ?_, ?_, hi _⟩
  · exact Exec.repeat he
  · omega

end Manuscript.SKRestrictedScatter
