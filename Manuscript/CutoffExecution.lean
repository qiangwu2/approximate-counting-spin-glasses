import Manuscript.Cutoffs
import Manuscript.InputPreparation

/-! Counted execution of the actual logarithmic first-crossing scan. -/

noncomputable section
namespace Manuscript.CutoffExecution
open SpinGlass.ArithmeticEvaluation Manuscript.InputPreparation

def phiComputation (kap A : ℝ) (N m : ℕ) : Computation :=
  mul (mul (literal kap) (literal m))
    (logarithm (divide (literal N) (mul (literal A) (literal m))))

@[simp] theorem phiComputation_value (kap A : ℝ) (N m : ℕ) :
    (phiComputation kap A N m).value = SpinGlass.CutoffTail.phi kap A N m := rfl

@[simp] theorem phiComputation_operations (kap A : ℝ) (N m : ℕ) :
    (phiComputation kap A N m).operations = 5 := rfl

structure SearchResult where
  found : Option ℕ
  operations : ℕ

/-- Each false comparison advances the current index by one. Loop control,
comparison and index arithmetic are included in the counter. -/
def scan (kap A : ℝ) (N : ℕ) (Lambda : ℝ) (start : ℕ) : ℕ → SearchResult
  | 0 => ⟨none, 1⟩
  | fuel + 1 =>
    let score := phiComputation kap A N start
    if Lambda ≤ score.value then ⟨some start, score.operations + 2⟩ else
      let rest := scan kap A N Lambda (start + 1) fuel
      ⟨rest.found, score.operations + 3 + rest.operations⟩

theorem scan_found (kap A : ℝ) (N : ℕ) (Lambda : ℝ) (start fuel : ℕ) :
    (scan kap A N Lambda start fuel).found =
      (SpinGlass.BoundedSearch.scan (fun m => decide (Lambda ≤ SpinGlass.CutoffTail.phi kap A N m))
        start fuel).found := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    simp only [scan, SpinGlass.BoundedSearch.scan, phiComputation_value, decide_eq_true_eq]
    split_ifs <;> simp [ih]

theorem scan_operations (kap A : ℝ) (N : ℕ) (Lambda : ℝ) (start fuel : ℕ) :
    (scan kap A N Lambda start fuel).operations ≤ 8 * fuel + 1 := by
  induction fuel generalizing start with
  | zero => simp [scan]
  | succ fuel ih =>
    simp only [scan, phiComputation_operations]
    split_ifs
    · dsimp only
      omega
    · dsimp only
      have h := ih (start + 1)
      omega

structure FloorResult where
  value : ℕ
  operations : ℕ

/-- Compute the largest admissible integer by a bounded descending scan.
Thus the loop bound does not require an uncharged floor oracle. -/
def boundedFloor (r : ℝ) : ℕ → FloorResult
  | 0 => ⟨0, 1⟩
  | n + 1 => if (n + 1 : ℝ) ≤ r then ⟨n + 1, 1⟩ else
      let rest := boundedFloor r n
      ⟨rest.value, rest.operations + 2⟩

theorem boundedFloor_value {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    (boundedFloor r n).value = min n (Nat.floor r) := by
  induction n with
  | zero => simp [boundedFloor]
  | succ n ih =>
    by_cases hn : (n + 1 : ℝ) ≤ r
    · have hn' : n+1 ≤ Nat.floor r := Nat.le_floor (by exact_mod_cast hn)
      simp [boundedFloor,hn,Nat.min_eq_left hn']
    · have hn' : Nat.floor r ≤ n := by
        have hh : ¬n+1 ≤ Nat.floor r := by
          intro h
          exact hn (by exact_mod_cast (Nat.le_floor_iff hr).mp h)
        omega
      simp [boundedFloor,hn,ih,Nat.min_eq_right hn',Nat.min_eq_right (by omega : Nat.floor r ≤ n+1)]

theorem boundedFloor_operations (r : ℝ) (n : ℕ) :
    (boundedFloor r n).operations ≤ 2*n+1 := by
  induction n with
  | zero => simp [boundedFloor]
  | succ n ih => simp only [boundedFloor]; split_ifs <;> dsimp only <;> omega

def cutoffSearch (kapMin kap A : ℝ) (N : ℕ) (Lambda : ℝ) : SearchResult :=
  let floor := boundedFloor (Cutoffs.gamma kapMin A * N) N
  let result := scan kap A N Lambda 1 floor.value
  ⟨result.found, floor.operations + result.operations + 1⟩

theorem gamma_floor_bound (kapMin A : ℝ) (N : ℕ) (hA : 0 < A) :
    Nat.floor (Cutoffs.gamma kapMin A * N) ≤ N := by
  have hg := Cutoffs.gamma_pos (kapMin := kapMin) hA
  have hfloor := Nat.floor_le (show 0 ≤ Cutoffs.gamma kapMin A * (N : ℝ) by positivity)
  have hgamma := mul_le_mul_of_nonneg_right (Cutoffs.gamma_le_one kapMin A)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hb : (Nat.floor (Cutoffs.gamma kapMin A * N) : ℝ) ≤ (N : ℝ) :=
    hfloor.trans (by simpa only [one_mul] using hgamma)
  exact_mod_cast hb

theorem cutoffSearch_found (kapMin kap A : ℝ) (N : ℕ) (Lambda : ℝ) (hA : 0 < A) :
    (cutoffSearch kapMin kap A N Lambda).found = (Cutoffs.cutoffScan kapMin kap A N Lambda).found := by
  have hg := Cutoffs.gamma_pos (kapMin := kapMin) hA
  simp only [cutoffSearch,boundedFloor_value (show 0 ≤ Cutoffs.gamma kapMin A * (N : ℝ) by positivity),
    Nat.min_eq_right (gamma_floor_bound kapMin A N hA)]
  exact scan_found _ _ _ _ _ _

theorem cutoffSearch_operations {kapMin kap A Lambda : ℝ} {N : ℕ} (hA : 0 < A) :
    (cutoffSearch kapMin kap A N Lambda).operations ≤ 10 * N + 3 := by
  have hg := Cutoffs.gamma_pos (kapMin := kapMin) hA
  have hfloor := Nat.floor_le (show 0 ≤ Cutoffs.gamma kapMin A * (N : ℝ) by positivity)
  have hgamma := mul_le_mul_of_nonneg_right (Cutoffs.gamma_le_one kapMin A)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf : Nat.floor (Cutoffs.gamma kapMin A * N) ≤ N := by
    have hb : (Nat.floor (Cutoffs.gamma kapMin A * N) : ℝ) ≤ (N : ℝ) :=
      hfloor.trans (by simpa only [one_mul] using hgamma)
    exact_mod_cast hb
  unfold cutoffSearch
  dsimp only
  rw [boundedFloor_value (show 0 ≤ Cutoffs.gamma kapMin A * (N : ℝ) by positivity),Nat.min_eq_right hf]
  have hs := scan_operations kap A N Lambda 1 (Nat.floor (Cutoffs.gamma kapMin A*N))
  have hb := boundedFloor_operations (Cutoffs.gamma kapMin A*N) N
  omega

/-- The counted computation returns the same first omitted index certified in
Lemma 5.1, with a linear operation bound independent of the input array. -/
theorem cutoffSearch_correct {kapMin kap A c1 Lambda : ℝ} {N : ℕ}
    (hk : 0 < kapMin) (hkk : kapMin ≤ kap) (hA : 0 < A)
    (hN : 2 / Cutoffs.gamma kapMin A ≤ (N : ℝ)) (hLam : 0 < Lambda)
    (hsmall : Lambda < Cutoffs.nu kapMin A c1 * N) :
    ∃ m, (cutoffSearch kapMin kap A N Lambda).found = some m ∧
      1 ≤ m ∧ m ≤ Nat.floor (Cutoffs.gamma kapMin A * N) ∧
      Lambda ≤ SpinGlass.CutoffTail.phi kap A N m ∧
      (∀ j : ℕ, 1 ≤ j → j < m → SpinGlass.CutoffTail.phi kap A N j < Lambda) ∧
      (cutoffSearch kapMin kap A N Lambda).operations ≤ 10 * N + 3 := by
  obtain ⟨m, hfound, hm1, hmf, hm, hminimal⟩ := Cutoffs.cutoffScan_correct hk hkk hA hN hLam hsmall
  exact ⟨m, by rw [cutoffSearch_found _ _ _ _ _ hA]; exact hfound, hm1, hmf, hm, hminimal,
    cutoffSearch_operations hA⟩

end Manuscript.CutoffExecution
