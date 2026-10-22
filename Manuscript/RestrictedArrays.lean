import Manuscript.RestrictedLoops
import Manuscript.RestrictedFrames

/-! Uniform array arithmetic used by the SK coefficient calculation. Every
read, write, pointer advance and loop test belongs to the restricted machine. -/
noncomputable section
namespace Manuscript.RestrictedArrays
open RestrictedMachine

inductive Operation where
  | add | mul | scale | copy | fill
  deriving DecidableEq

def Operation.eval (op : Operation) (scalar x y : ℝ) : ℝ :=
  match op with
  | .add => x+y
  | .mul => x*y
  | .scale => scalar*x
  | .copy => x
  | .fill => scalar

def arithmetic : Operation → List Instruction
  | .add => [.radd 2 0 1]
  | .mul => [.rmul 2 0 1]
  | .scale => [.rmul 2 4 0]
  | .copy => [.rcopy 2 0]
  | .fill => [.rcopy 2 4]

/-- Natural registers 10,11,12 are the two source pointers and destination.
Register 13 contains one, register 14 is the length, and real register 4 is
used by scalar multiplication. -/
def bodyCode (op : Operation) : List Instruction :=
  [.loadReal 0 10, .loadReal 1 11] ++ arithmetic op ++
  [.storeReal 12 2, .nadd 10 10 13, .nadd 11 11 13, .nadd 12 12 13]

def program (op : Operation) : Program := .repeat 14 (code (bodyCode op))

def memoryStep (op : Operation) (scalar : ℝ) (a b c : ℕ)
    (memory : ℕ → ℝ) : ℕ → ℝ :=
  Function.update memory c (op.eval scalar (memory a) (memory b))

def memoryLoop (op : Operation) (scalar : ℝ) (a b c : ℕ) : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, memory => memory
  | n+1, memory => memoryStep op scalar (a+n) (b+n) (c+n)
      (memoryLoop op scalar a b c n memory)

theorem body_cost (op : Operation) : codeCost (bodyCode op) ≤ 25 := by
  cases op <;> norm_num [bodyCode, arithmetic, codeCost, instrCost]

theorem body_values (op : Operation) (params : Parameters) (input : Inputs)
    (s : State) (hone : s.natReg 13 = 1) :
    let t := runCode params input (bodyCode op) s
    t.realMem = memoryStep op (s.realReg 4) (s.natReg 10) (s.natReg 11)
      (s.natReg 12) s.realMem ∧
    t.natMem = s.natMem ∧
    t.natReg 10 = s.natReg 10+1 ∧
    t.natReg 11 = s.natReg 11+1 ∧
    t.natReg 12 = s.natReg 12+1 ∧
    (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → t.natReg r = s.natReg r) ∧
    (∀ r, 3 ≤ r → t.realReg r = s.realReg r) := by
  cases op <;>
    simp only [bodyCode, arithmetic, List.cons_append, List.nil_append, runCode, step,
      writeRealReg_realReg, writeRealReg_realMem, writeRealReg_natMem,
      writeRealReg_natReg, writeRealMem, writeNatReg_realReg,
      writeNatReg_realMem, writeNatReg_natMem, writeNatReg_natReg] <;>
    norm_num <;> simp only [hone, memoryStep, Operation.eval] <;>
    simp only [true_and]
  all_goals refine ⟨?_, ?_⟩
  all_goals
    first
    | (intro r h10 h11 h12; simp [h10, h11, h12])
    | (intro r hr; have h0 : r ≠ 0 := by omega
       have h1 : r ≠ 1 := by omega
       have h2 : r ≠ 2 := by omega
       simp [h0, h1, h2])

def Invariant (op : Operation) (s : State) (n : ℕ) (t : State) : Prop :=
  t.realMem = memoryLoop op (s.realReg 4) (s.natReg 10) (s.natReg 11)
      (s.natReg 12) n s.realMem ∧
  t.natMem = s.natMem ∧
  t.natReg 10 = s.natReg 10+n ∧
  t.natReg 11 = s.natReg 11+n ∧
  t.natReg 12 = s.natReg 12+n ∧
  (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → t.natReg r = s.natReg r) ∧
  (∀ r, 3 ≤ r → t.realReg r = s.realReg r)

theorem invariant_step (op : Operation) (params : Parameters) (input : Inputs)
    {s t : State} {n : ℕ} (hone : s.natReg 13 = 1) (h : Invariant op s n t) :
    Invariant op s (n+1) (runCode params input (bodyCode op) t) := by
  rcases h with ⟨hm, hn, h10, h11, h12, hf, hrf⟩
  have hton : t.natReg 13 = 1 := by rw [hf 13 (by decide) (by decide) (by decide), hone]
  rcases body_values op params input t hton with ⟨hm', hn', h10', h11', h12', hf', hrf'⟩
  refine ⟨?_, hn'.trans hn, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm', hm, h10, h11, h12, hrf 4 (by decide)]; rfl
  · omega
  · omega
  · omega
  · intro r ha hb hc; exact (hf' r ha hb hc).trans (hf r ha hb hc)
  · intro r hr; exact (hrf' r hr).trans (hrf r hr)

theorem program_exec (op : Operation) (params : Parameters) (input : Inputs)
    (s : State) (hone : s.natReg 13 = 1) :
    ∃ count t, Exec params input (program op) s count t ∧
      count ≤ 30*s.natReg 14+5 ∧ Invariant op s (s.natReg 14) t := by
  let F : ℕ → State := fun n => (runCode params input (bodyCode op))^[n] s
  have hi : ∀ n, Invariant op s n (F n) := by
    intro n
    induction n with
    | zero => simp [Invariant, F, memoryLoop]
    | succ n ih =>
      simpa only [F, Function.iterate_succ_apply'] using invariant_step op params input hone ih
  have he := repeats_of_steps params input (code (bodyCode op)) F
      (fun _ => codeCost (bodyCode op)) (s.natReg 14) (by
        intro i _
        simpa only [F, Function.iterate_succ_apply'] using
          exec_code params input (bodyCode op) (F i))
  refine ⟨(∑ _i ∈ Finset.range (s.natReg 14), codeCost (bodyCode op))+
      5*s.natReg 14+3+2, F (s.natReg 14), Exec.repeat he, ?_, hi _⟩
  have hb := Nat.mul_le_mul_left (s.natReg 14) (body_cost op)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at *
  omega

/-- Writes to earlier output cells cannot alter a later source cell. This
allows disjoint blocks and also in-place pointwise array operations. -/
theorem loop_frame (op : Operation) (scalar : ℝ) (a b c n address : ℕ)
    (memory : ℕ → ℝ) (h : ∀ j, j < n → address ≠ c+j) :
    memoryLoop op scalar a b c n memory address = memory address := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [memoryLoop, memoryStep, Function.update_of_ne (h n (by omega))]
    exact ih (fun j hj => h j (by omega))

theorem loop_values (op : Operation) (scalar : ℝ) (a b c n : ℕ)
    (memory : ℕ → ℝ)
    (hs : ∀ i j, i < n → j < i → a+i ≠ c+j ∧ b+i ≠ c+j) :
    ∀ i, i < n → memoryLoop op scalar a b c n memory (c+i) =
      op.eval scalar (memory (a+i)) (memory (b+i)) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    by_cases hin : i=n
    · subst i
      simp only [memoryLoop, memoryStep, Function.update_self]
      rw [loop_frame op scalar a b c n (a+n) memory
        (fun j hj => (hs n j (by omega) hj).1)]
      rw [loop_frame op scalar a b c n (b+n) memory
        (fun j hj => (hs n j (by omega) hj).2)]
    · rw [memoryLoop, memoryStep, Function.update_of_ne (by omega : c+i ≠ c+n)]
      exact ih (fun i j hi hj => hs i j (by omega) hj) i (by omega)

theorem pointwise_realized (op : Operation) (params : Parameters) (input : Inputs)
    (s : State) (hone : s.natReg 13 = 1)
    (hs : ∀ i j, i < s.natReg 14 → j < i →
      s.natReg 10+i ≠ s.natReg 12+j ∧ s.natReg 11+i ≠ s.natReg 12+j) :
    ∃ count t, Exec params input (program op) s count t ∧
      count ≤ 30*s.natReg 14+5 ∧ Invariant op s (s.natReg 14) t ∧
      (∀ i, i < s.natReg 14 → t.realMem (s.natReg 12+i) =
        op.eval (s.realReg 4) (s.realMem (s.natReg 10+i)) (s.realMem (s.natReg 11+i))) := by
  obtain ⟨count,t,he,hc,hi⟩ := program_exec op params input s hone
  exact ⟨count,t,he,hc,hi,by rw [hi.1]; exact loop_values op _ _ _ _ _ _ hs⟩

end Manuscript.RestrictedArrays
