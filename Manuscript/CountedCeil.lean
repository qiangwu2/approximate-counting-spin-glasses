import Manuscript.InputPreparation

/-! Natural ceilings computed by comparisons and increments, with no ceiling
oracle. The mathematical ceiling appears only in the termination/cost proof. -/
noncomputable section
namespace Manuscript.CountedCeil

structure Result where
  value : ℕ
  operations : ℕ

/-- Start at the supplied integer and increment until the real target is reached. -/
def scan (x : ℝ) (n : ℕ) : Result :=
  if x ≤ (n : ℝ) then ⟨n,1⟩ else
    let tail := scan x (n+1)
    ⟨tail.value,tail.operations+2⟩
termination_by Nat.ceil x-n
decreasing_by
  have hn : n < Nat.ceil x := Nat.lt_ceil.mpr (lt_of_not_ge (by assumption))
  omega

theorem scan_spec (x : ℝ) (n : ℕ) (hn : n ≤ Nat.ceil x) :
    (scan x n).value = Nat.ceil x ∧ (scan x n).operations = 2*(Nat.ceil x-n)+1 := by
  generalize hm : Nat.ceil x-n = m
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    rw [scan]
    split_ifs with hx
    · have hc : Nat.ceil x ≤ n := Nat.ceil_le.mpr hx
      have heq : n = Nat.ceil x := by omega
      have hm0 : m = 0 := by omega
      simp [heq,hm0]
    · have hnc : n < Nat.ceil x := Nat.lt_ceil.mpr (lt_of_not_ge hx)
      obtain ⟨hv,ho⟩ := ih (Nat.ceil x-(n+1)) (by omega) (n+1) (by omega) rfl
      dsimp only
      rw [hv,ho]
      constructor
      · rfl
      · omega

def ceiling (x : ℝ) : Result := scan x 0

@[simp] theorem ceiling_value (x : ℝ) : (ceiling x).value = Nat.ceil x :=
  (scan_spec x 0 (Nat.zero_le _)).1

@[simp] theorem ceiling_operations (x : ℝ) :
    (ceiling x).operations = 2*Nat.ceil x+1 := by
  simpa only [ceiling,Nat.sub_zero] using (scan_spec x 0 (Nat.zero_le _)).2

end Manuscript.CountedCeil
