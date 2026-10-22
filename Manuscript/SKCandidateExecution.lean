import Manuscript.SupportIndices
import Manuscript.SKChargedControlExecution

/-! Bounded-cardinality enumeration of candidate branch sets. -/
noncomputable section
namespace Manuscript.SKCandidateExecution
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Enumerate only the requested cardinalities, and unite the disjoint families.
This definition does not scan the full powerset. -/
def candidates (V : Type*) [Fintype V] [DecidableEq V] (D : ℕ) : Finset (Finset V) :=
  (Finset.range (min D (Fintype.card V) + 1)).biUnion
    (fun b => (Finset.univ : Finset V).powersetCard b)

@[simp] theorem mem_candidates (D : ℕ) (A : Finset V) :
    A ∈ candidates V D ↔ A.card ≤ D := by
  simp only [candidates, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
    Finset.subset_univ, true_and]
  constructor
  · rintro ⟨b, hb, rfl⟩
    omega
  · intro h
    exact ⟨A.card, by have := Finset.card_le_univ A; omega, rfl⟩

theorem candidates_eq_filter (D : ℕ) :
    candidates V D = (Finset.univ : Finset V).powerset.filter (fun A => A.card ≤ D) := by
  ext A
  simp

/-- Any scalar sum over the executed candidate enumeration equals the displayed
nested cardinality enumeration in Algorithm 3. -/
theorem sum_candidates {M : Type*} [AddCommMonoid M] (D : ℕ) (f : Finset V → M) :
    (∑ A ∈ candidates V D, f A) =
      ∑ b ∈ Finset.range (D + 1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b, f A := by
  rw [candidates_eq_filter]
  symm
  have h := Finset.sum_fiberwise_eq_sum_filter ((Finset.univ : Finset V).powerset)
    (Finset.range (D + 1)) Finset.card f
  simpa only [← Finset.powersetCard_eq_filter, Finset.mem_range, Nat.lt_succ_iff] using h

theorem sum_candidates_card (D : ℕ) (f : ℕ → ℕ) :
    (∑ A ∈ candidates V D, f A.card) =
      ∑ b ∈ Finset.range (D + 1), (Fintype.card V).choose b * f b := by
  rw [sum_candidates]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [Finset.sum_congr rfl (fun A hA => congrArg f (Finset.mem_powersetCard.mp hA).2)]
  simp

open SupportIndices Manuscript.SKChargedControlExecution

/-- The concrete generator runs only the admissible cardinality layers. -/
def candidateList (V : Type*) [Fintype V] [DecidableEq V] (D : ℕ) : List (Finset V) :=
  (Finset.range (min D (Fintype.card V)+1)).toList.flatMap
    (fun b => chosenFinsets b (Finset.univ : Finset V).toList)

@[simp] theorem candidateList_toFinset (D : ℕ) :
    (candidateList V D).toFinset = candidates V D := by
  ext A
  simp only [candidateList, List.mem_toFinset, List.mem_flatMap, Finset.mem_toList]
  simp_rw [← List.mem_toFinset,
    chosenFinsets_toFinset _ _ (Finset.univ : Finset V).nodup_toList, Finset.toList_toFinset]
  simp only [candidates, Finset.mem_biUnion]

theorem sum_flatMap {I M : Type*} [AddCommMonoid M] (xs : List I) (f : I → List M) :
    (xs.flatMap f).sum = (xs.map (fun i => (f i).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih]

/-- The concrete list and finite-set families have the same scalar folds. -/
theorem candidateList_sum {M : Type*} [AddCommMonoid M] (D : ℕ) (f : Finset V → M) :
    ((candidateList V D).map f).sum = ∑ A ∈ candidates V D, f A := by
  simp only [candidateList, List.map_flatMap, sum_flatMap]
  simp_rw [chosenFinsets_sum]
  rw [Finset.sum_map_toList]
  rw [← sum_candidates]
  congr 1
  ext A
  simp only [mem_candidates]
  have := Finset.card_le_univ A
  omega

/-- Generation work includes recursive pruning and append/map, as well as an
extra quadratic allowance per generated finite set for index conversion. -/
def candidateGenerationWork (N D : ℕ) : ℕ :=
  (min D N + 1) + ∑ b ∈ Finset.range (min D N+1),
    (chooseWork N b + (N+1)^2 * N.choose b)

theorem candidateGenerationWork_le (D L : ℕ) :
    candidateGenerationWork (Fintype.card V) D ≤
      visitControl (20 * (Fintype.card V+L+1)^2) (candidates V D).toList := by
  let N := Fintype.card V
  have hgen := bounded_choose_work (n := N) (cutoff := min D N) (Nat.min_le_right _ _)
  have hcount : (∑ b ∈ Finset.range (min D N+1), N.choose b) = (candidates V D).card := by
    have h := sum_candidates_card (V := V) (min D N) (fun _ => 1)
    have heq : candidates V (min D N) = candidates V D := by
      ext A
      simp only [mem_candidates]
      have := Finset.card_le_univ A
      dsimp [N] at *
      omega
    simpa only [heq, Finset.sum_const, nsmul_eq_mul, Nat.mul_one, Nat.cast_id, N] using h.symm
  have hsteps : min D N+1 ≤ ∑ b ∈ Finset.range (min D N+1), N.choose b := by
    calc
      _ = ∑ _b ∈ Finset.range (min D N+1), (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b hb => Nat.choose_pos (by have := Finset.mem_range.mp hb; omega))
  have hsize : (N+1)^2 ≤ (N+L+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hpos : 1 ≤ (N+L+1)^2 := Nat.succ_le_of_lt (by positivity)
  unfold candidateGenerationWork
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [visitControl_eq, Finset.length_toList]
  change _ ≤ 1 + (candidates V D).card * (20*(N+L+1)^2)
  rw [hcount] at hgen hsteps ⊢
  nlinarith


end Manuscript.SKCandidateExecution
