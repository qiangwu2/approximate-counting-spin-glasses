import Manuscript.SKBranchReindex

noncomputable section
namespace Manuscript.SKPairReindex
open scoped BigOperators

abbrev OrderedPair (b : ℕ) := {p : Fin b × Fin b // p.1 < p.2}

def ordered {b c : ℕ} (e : Fin b ≃ Fin c) (p : OrderedPair b) : OrderedPair c :=
  if h : e p.val.1 < e p.val.2 then ⟨(e p.val.1,e p.val.2),h⟩
  else ⟨(e p.val.2,e p.val.1),by
    have hn : e p.val.1 ≠ e p.val.2 := fun hh => (ne_of_lt p.property) (e.injective hh)
    exact lt_of_le_of_ne (le_of_not_gt h) hn.symm⟩

theorem ordered_inv {b c : ℕ} (e : Fin b ≃ Fin c) (p : OrderedPair b) :
    ordered e.symm (ordered e p)=p := by
  apply Subtype.ext
  have hp := p.property
  by_cases h : e p.val.1 < e p.val.2
  · simp [ordered,h,hp]
  · simp [ordered,h,hp,not_lt_of_ge (le_of_lt hp)]

def equiv {b c : ℕ} (e : Fin b ≃ Fin c) : OrderedPair b ≃ OrderedPair c where
  toFun := ordered e
  invFun := ordered e.symm
  left_inv := ordered_inv e
  right_inv := ordered_inv e.symm

theorem value_ordered {b c : ℕ} {R : Type*} (e : Fin b ≃ Fin c)
    (f : Fin c → Fin c → R) (hf : ∀ a d, a≠d → f a d=f d a) (p : OrderedPair b) :
    f (ordered e p).val.1 (ordered e p).val.2=f (e p.val.1) (e p.val.2) := by
  unfold ordered
  split_ifs with h
  · rfl
  · apply hf
    exact fun hh => (ne_of_lt p.property) (e.injective hh.symm)

theorem sum_pairs {b : ℕ} {R : Type*} [AddCommMonoid R] (f : Fin b → Fin b → R) :
    (∑ a, ∑ d, if a<d then f a d else 0)=∑ p : OrderedPair b, f p.val.1 p.val.2 := by
  change (∑ a, ∑ d, (fun p : Fin b × Fin b => if p.1<p.2 then f p.1 p.2 else 0) (a,d))=_
  rw [← Fintype.sum_prod_type (fun p : Fin b × Fin b => if p.1<p.2 then f p.1 p.2 else 0)]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) (fun p : Fin b × Fin b => f p.1 p.2)

theorem sum_reindex {b c : ℕ} {R : Type*} [AddCommMonoid R] (e : Fin b ≃ Fin c)
    (f : Fin c → Fin c → R) (hf : ∀ a d, a≠d → f a d=f d a) :
    (∑ a : Fin b, ∑ d : Fin b, if a<d then f (e a) (e d) else 0)=
      ∑ a : Fin c, ∑ d : Fin c, if a<d then f a d else 0 := by
  rw [sum_pairs,sum_pairs]
  apply Fintype.sum_equiv (equiv e)
  intro p
  exact (value_ordered e f hf p).symm

theorem prod_pairs {b : ℕ} {R : Type*} [CommMonoid R] (f : Fin b → Fin b → R) :
    (∏ p ∈ Manuscript.SKChargedExecution.directPairs b, f p.1 p.2)=
      ∏ p : OrderedPair b, f p.val.1 p.val.2 := by
  exact Finset.prod_subtype (Manuscript.SKChargedExecution.directPairs b)
    (by simp [Manuscript.SKChargedExecution.directPairs])
    (fun p : Fin b × Fin b => f p.1 p.2)

theorem prod_reindex {b c : ℕ} {R : Type*} [CommMonoid R] (e : Fin b ≃ Fin c)
    (f : Fin c → Fin c → R) (hf : ∀ a d, a≠d → f a d=f d a) :
    (∏ p ∈ Manuscript.SKChargedExecution.directPairs b, f (e p.1) (e p.2))=
      ∏ p ∈ Manuscript.SKChargedExecution.directPairs c, f p.1 p.2 := by
  rw [prod_pairs (fun a d => f (e a) (e d)),prod_pairs f]
  apply Fintype.prod_equiv (equiv e)
  intro p
  exact (value_ordered e f hf p).symm

end Manuscript.SKPairReindex
