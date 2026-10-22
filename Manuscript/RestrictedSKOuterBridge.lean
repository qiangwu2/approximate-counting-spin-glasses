import Manuscript.RestrictedSKOuter
import Manuscript.SKGeneratedExecution
import Manuscript.RestrictedHigherLayer

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSKOuterBridge
open RestrictedMachine

theorem trial_sum (f : ℕ→ℕ→ℝ) (mask n i : ℕ) :
    RestrictedSKTrials.sum f mask n i=∑j∈Finset.range n,f mask (i+j) := by
  induction n generalizing i with
  | zero => simp [RestrictedSKTrials.sum]
  | succ n ih =>
      rw [RestrictedSKTrials.sum,Finset.sum_range_succ']
      simp [ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_comm]

theorem mask_value_list (f : ℕ→ℕ→ℝ) (R : ℕ) (masks : ℕ→ℕ) (i : ℕ) (xs : List ℕ)
    (h : ∀ j (hj : j<xs.length),masks (i+j)=xs[j]) :
    RestrictedSKMaskFold.value f R masks xs.length i=
      (xs.map (fun u=>RestrictedSKTrials.sum f u R 0/(R:ℝ))).sum := by
  induction xs generalizing i with
  | nil => simp [RestrictedSKMaskFold.value]
  | cons x xs ih =>
      have h0:=h 0 (by simp)
      simp only [Nat.add_zero,List.getElem_cons_zero] at h0
      simp only [List.length_cons,RestrictedSKMaskFold.value,List.map_cons,List.sum_cons]
      rw [h0,ih (i+1)]
      intro j hj
      convert h (j+1) (by simp;omega) using 1 <;> simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem mask_cost_list (bound : ℕ→ℕ) (R : ℕ) (masks : ℕ→ℕ) (i : ℕ) (xs : List ℕ)
    (h : ∀ j (hj : j<xs.length),masks (i+j)=xs[j]) :
    RestrictedSKMaskFold.cost bound R masks xs.length i=
      (xs.map (fun u=>R*(bound u+29)+35)).sum := by
  induction xs generalizing i with
  | nil => simp [RestrictedSKMaskFold.cost]
  | cons x xs ih =>
      have h0:=h 0 (by simp)
      simp only [Nat.add_zero,List.getElem_cons_zero] at h0
      simp only [List.length_cons,RestrictedSKMaskFold.cost,List.map_cons,List.sum_cons]
      rw [h0,ih (i+1)]
      intro j hj
      convert h (j+1) (by simp;omega) using 1 <;> simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem layer_value (f : ℕ→ℕ→ℝ) (N R b : ℕ) :
    RestrictedSKMaskFold.value f R (fun j=>(RestrictedSubsets.masks N b 0 1)[j]!) (N.choose b) 0=
      ∑A∈(Finset.univ : Finset (Fin N)).powersetCard b,
        (∑r∈Finset.range R,f (RestrictedMaskBridge.encode A) r)/(R:ℝ) := by
  have hh:=mask_value_list f R (fun j=>(RestrictedSubsets.masks N b 0 1)[j]!) 0
    (RestrictedSubsets.masks N b 0 1) (by intro j hj;simp [List.getElem?_eq_getElem hj])
  simpa [RestrictedMaskBridge.support_masks_sum,trial_sum] using hh

theorem layer_cost (bound : ℕ→ℕ) (N R b : ℕ) :
    RestrictedSKMaskFold.cost bound R (fun j=>(RestrictedSubsets.masks N b 0 1)[j]!) (N.choose b) 0=
      ∑A∈(Finset.univ : Finset (Fin N)).powersetCard b,
        (R*(bound (RestrictedMaskBridge.encode A)+29)+35) := by
  have hh:=mask_cost_list bound R (fun j=>(RestrictedSubsets.masks N b 0 1)[j]!) 0
    (RestrictedSubsets.masks N b 0 1) (by intro j hj;simp [List.getElem?_eq_getElem hj])
  simpa only [RestrictedSubsets.masks_length,RestrictedMaskBridge.support_masks_sum] using hh

theorem value_range (f : ℕ→ℕ→ℝ) (N R n b : ℕ) :
    RestrictedSKOuter.value f N R n b=
      ∑j∈Finset.range n,∑A∈(Finset.univ : Finset (Fin N)).powersetCard (b+j),
        (∑r∈Finset.range R,f (RestrictedMaskBridge.encode A) r)/(R:ℝ) := by
  induction n generalizing b with
  | zero => simp [RestrictedSKOuter.value]
  | succ n ih =>
      rw [RestrictedSKOuter.value,Finset.sum_range_succ',layer_value,ih]
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_comm]

theorem cost_range (bound : ℕ→ℕ) (N R n b : ℕ) :
    RestrictedSKOuter.cost bound N R n b=
      ∑j∈Finset.range n,(RestrictedSubsets.work N (b+j)+
        (∑A∈(Finset.univ : Finset (Fin N)).powersetCard (b+j),
          (R*(bound (RestrictedMaskBridge.encode A)+29)+35))+66) := by
  induction n generalizing b with
  | zero => simp [RestrictedSKOuter.cost]
  | succ n ih =>
      rw [RestrictedSKOuter.cost,Finset.sum_range_succ',layer_cost,ih]
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_comm]

theorem value_eq_estimator {N D L R : ℕ} (f : ℕ→ℕ→ℝ)
    (χ : SKColorEstimator.Colors (Fin N) L R) (mean : ℝ) (w : Finset (Fin N)→ℝ)
    (hf : ∀ (A : Finset (Fin N)) (r : Fin R),
      f (RestrictedMaskBridge.encode A) r.val=(SKGeneratedExecution.trial L A (χ A r) mean w).value) :
    RestrictedSKOuter.value f N R (D+1) 0=(SKGeneratedExecution.estimator D L R χ mean w).value := by
  rw [value_range]
  simp only [Nat.zero_add]
  simp only [SKGeneratedExecution.estimator,SpinGlass.ArithmeticEvaluation.sumList_value,
    List.map_map,Function.comp_def,SKCandidateExecution.candidateList_sum,SKCandidateExecution.sum_candidates]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro A hA
  simp only [SKGeneratedExecution.average,InputPreparation.divide,SpinGlass.ArithmeticEvaluation.literal,
    SpinGlass.ArithmeticEvaluation.sumFinset_value]
  congr 1
  rw [←Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun r _=>hf A r)

/-- The same fixed outer syntax executes in the shared two-procedure table
used by the exact higher/support branch. -/
def program (candidate : Program) : RestrictedRecursiveMachine.Program 2 :=
  (RestrictedSKOuter.program candidate).rename RestrictedHigherLayer.subsetId

theorem embed {params : Parameters} {input : Inputs} {candidate : Program} {s t : State} {count : ℕ}
    (he : RestrictedRecursiveMachine.Exec RestrictedSubsets.table params input
      (RestrictedSKOuter.program candidate) s count t) :
    RestrictedRecursiveMachine.Exec RestrictedHigherLayer.table params input (program candidate) s count t :=
  he.rename RestrictedHigherLayer.subsetId RestrictedHigherLayer.table RestrictedHigherLayer.subset_table

end Manuscript.RestrictedSKOuterBridge
