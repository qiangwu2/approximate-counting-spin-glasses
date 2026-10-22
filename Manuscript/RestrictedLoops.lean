import Manuscript.RestrictedMachine

noncomputable section
namespace Manuscript.RestrictedMachine

/-- Mathematical description of successive states, not an instruction. -/
def iterateState (next : State → State) : ℕ → State → State
  | 0, s => s
  | n+1, s => iterateState next n (next s)

/-- A bounded-loop proof from actual executions of its fixed body. In
particular `next` is not available to the machine as an oracle: each use must
be realized by `body` with the displayed primitive cost. -/
theorem repeats_bounded (p : Parameters) (i : Inputs) (body : Program)
    (next : State → State) (B : ℕ)
    (bodyRuns : ∀ s, ∃ c, Exec p i body s c (next s) ∧ c ≤ B)
    (n : ℕ) (s : State) :
    ∃ c, Repeats p i body n s c (iterateState next n s) ∧ c ≤ n*(B+5)+3 := by
  induction n generalizing s with
  | zero => exact ⟨3, Repeats.zero body s, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc, bc⟩ := bodyRuns s
    obtain ⟨d, hd, bd⟩ := ih (next s)
    refine ⟨c+d+5, Repeats.succ hc hd, ?_⟩
    calc
      c+d+5 ≤ B+(n*(B+5)+3)+5 := Nat.add_le_add_right (Nat.add_le_add bc bd) 5
      _ = (n+1)*(B+5)+3 := by rw [Nat.add_mul]; omega

theorem repeats_invariant_bounded (p : Parameters) (i : Inputs) (body : Program)
    (next : State → State) (B : ℕ) (P : State → Prop)
    (bodyRuns : ∀ s, P s → ∃ c, Exec p i body s c (next s) ∧ c ≤ B ∧ P (next s))
    (n : ℕ) (s : State) (hs : P s) :
    ∃ c, Repeats p i body n s c (iterateState next n s) ∧
      c ≤ n*(B+5)+3 ∧ P (iterateState next n s) := by
  induction n generalizing s with
  | zero => exact ⟨3, Repeats.zero body s, by simp, hs⟩
  | succ n ih =>
    obtain ⟨c, hc, bc, hp⟩ := bodyRuns s hs
    obtain ⟨d, hd, bd, hp'⟩ := ih (next s) hp
    refine ⟨c+d+5, Repeats.succ hc hd, ?_, hp'⟩
    calc
      c+d+5 ≤ B+(n*(B+5)+3)+5 := Nat.add_le_add_right (Nat.add_le_add bc bd) 5
      _ = (n+1)*(B+5)+3 := by rw [Nat.add_mul]; omega

end Manuscript.RestrictedMachine
