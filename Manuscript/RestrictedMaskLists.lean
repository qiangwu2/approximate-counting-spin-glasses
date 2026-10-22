import Manuscript.RestrictedMaskBridge

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedMaskBridge
open SupportIndices

theorem binaryPlaces_finRange (n b : ℕ) :
    RestrictedSubsets.binaryPlaces n b=(List.finRange n).map (fun v => b*2^v.val) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp [RestrictedSubsets.binaryPlaces,List.finRange_succ,List.map_map,ih,
      Function.comp_def,pow_succ,Nat.mul_assoc,Nat.mul_comm]

theorem chooseLists_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α→β) (k : ℕ) (xs : List α) :
    chooseLists k (xs.map f)=(chooseLists k xs).map (List.map f) := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      by_cases h : xs.length<k <;>
        simp [chooseLists,h,ih,List.map_map,Function.comp_def]

theorem encode_list_sum {N : ℕ} (xs : List (Fin N)) (hn : xs.Nodup) :
    encode xs.toFinset=(xs.map (fun v => 2^v.val)).sum := by
  rw [encode_sum,List.sum_toFinset _ hn]

theorem support_masks_chosen (N k : ℕ) :
    RestrictedSubsets.masks N k 0 1=(chosenFinsets k (List.finRange N)).map encode := by
  rw [RestrictedSubsets.masks_as_choices,binaryPlaces_finRange,chooseLists_map]
  simp only [Nat.zero_add,Nat.one_mul,List.map_map,chosenFinsets,chooseExecution_values,Function.comp_def]
  apply List.map_congr_left
  intro xs hxs
  have hsub : xs.Sublist (List.finRange N) :=
    (List.mem_sublistsLen.mp (by simpa [chooseLists_eq] using hxs)).1
  exact (encode_list_sum xs ((List.nodup_finRange N).sublist hsub)).symm

theorem support_masks_sum {R : Type*} [AddCommMonoid R] (N k : ℕ) (f : ℕ→R) :
    ((RestrictedSubsets.masks N k 0 1).map f).sum=
      ∑U∈(Finset.univ : Finset (Fin N)).powersetCard k,f (encode U) := by
  rw [support_masks_chosen,List.map_map]
  rw [←List.sum_toFinset _ (chosenFinsets_nodup k (List.finRange N) (List.nodup_finRange N)),
    chosenFinsets_toFinset k (List.finRange N) (List.nodup_finRange N),List.toFinset_finRange]
  rfl

theorem selectedPlaces_finRange (n u b : ℕ) :
    RestrictedCubes.selectedPlaces n u b=
      ((List.finRange n).filter (fun v => decide (u/2^v.val%2≠0))).map (fun v => b*2^v.val) := by
  induction n generalizing u b with
  | zero => rfl
  | succ n ih =>
    have hm : u%2=0 ∨ u%2=1 := by omega
    rcases hm with h | h <;>
      simp [RestrictedCubes.selectedPlaces,List.finRange_succ,List.filter_cons,List.filter_map,
        List.map_map,ih,Function.comp_def,h,pow_succ',Nat.div_div_eq_div_mul,
        Nat.mul_assoc,Nat.mul_comm]

def selectedVertices {N : ℕ} (U : Finset (Fin N)) : List (Fin N) :=
  (List.finRange N).filter (fun v => decide (v∈U))

theorem selectedVertices_nodup {N : ℕ} (U : Finset (Fin N)) : (selectedVertices U).Nodup :=
  (List.nodup_finRange N).filter _

@[simp] theorem selectedVertices_toFinset {N : ℕ} (U : Finset (Fin N)) :
    (selectedVertices U).toFinset=U := by
  ext v
  simp [selectedVertices]

theorem selectedPlaces_encoded {N : ℕ} (U : Finset (Fin N)) :
    RestrictedCubes.selectedPlaces N (encode U) 1=
      (selectedVertices U).map (fun v => 2^v.val) := by
  rw [selectedPlaces_finRange]
  simp only [encode_digit,Nat.one_mul]
  congr 2
  funext v
  by_cases hv : v∈U <;> simp [hv]

theorem supportSize_card {N : ℕ} (U : Finset (Fin N)) :
    RestrictedCubes.supportSize N (encode U)=U.card := by
  rw [←RestrictedCubes.selectedPlaces_length N (encode U) 1,selectedPlaces_encoded,List.length_map,
    ←List.toFinset_card_of_nodup (selectedVertices_nodup U),selectedVertices_toFinset]

theorem cube_masks_all {N : ℕ} (U : Finset (Fin N)) :
    RestrictedCubes.masks N (encode U) 0 1=(allFinsets (selectedVertices U)).map encode := by
  rw [RestrictedCubes.masks_as_subsets,selectedPlaces_encoded]
  simp only [allExecution_values,List.sublists'_map,List.map_map,Nat.zero_add,Function.comp_def,
    allFinsets]
  apply List.map_congr_left
  intro xs hxs
  have hsub : xs.Sublist (selectedVertices U) := List.mem_sublists'.mp hxs
  exact (encode_list_sum xs ((selectedVertices_nodup U).sublist hsub)).symm

theorem cube_masks_sum {R : Type*} [AddCommMonoid R] {N : ℕ} (U : Finset (Fin N)) (f : ℕ→R) :
    ((RestrictedCubes.masks N (encode U) 0 1).map f).sum=∑T∈U.powerset,f (encode T) := by
  rw [cube_masks_all,List.map_map,
    ←List.sum_toFinset _ (allFinsets_nodup (selectedVertices U) (selectedVertices_nodup U)),
    allFinsets_toFinset,selectedVertices_toFinset]
  rfl

/-- All subsets of U encode exactly the local Boolean spin assignments. -/
theorem powerset_spin_sum {R : Type*} [AddCommMonoid R] {N : ℕ}
    (U : Finset (Fin N)) (f : (U→Bool)→R) :
    (∑T∈U.powerset,f (fun v => spin T v.val))=∑σ:U→Bool,f σ := by
  classical
  apply Finset.sum_bij (fun T _ => fun v : U => spin T v.val)
  · intro T hT
    exact Finset.mem_univ _
  · intro T hT T' hT' heq
    have hTU := Finset.mem_powerset.mp hT
    have hT'U := Finset.mem_powerset.mp hT'
    ext v
    by_cases hv : v∈U
    · have h := congrFun heq ⟨v,hv⟩
      simpa [spin] using h
    · have ht : v∉T := fun ht => hv (hTU ht)
      have ht' : v∉T' := fun ht => hv (hT'U ht)
      simp [ht,ht']
  · intro σ hσ
    let T := U.filter (fun v => if hv : v∈U then σ ⟨v,hv⟩ else false)
    refine ⟨T,Finset.mem_powerset.mpr (Finset.filter_subset _ _),?_⟩
    funext v
    simp [spin,T,v.property]
  · intro T hT
    rfl

end Manuscript.RestrictedMaskBridge
