import Manuscript.RestrictedPreparation

noncomputable section
namespace Manuscript.RestrictedPhysicalPreparation
open RestrictedMachine Model InputPreparation RestrictedInputEncoding

/-- The prepared cache represents the original physical interactions in the
order supplied by the raw coupling records. -/
theorem physical_cache {N M : ℕ} (hN : 0 < N) {P : Finset ℕ}
    (order : Fin M ≃ Edge N P) (beta h epsilon delta : ℝ) (J : Edge N P → ℝ)
    (tape : ℕ → ℕ) (a : ℕ → ℝ) (params : Parameters)
    (hparams : ∀ p∈P,params p=a p) (budgetBase : ℕ) (s : State)
    (hs : RestrictedPreparation.Ready params (encode order beta h epsilon delta J tape) budgetBase s) :
    (∀ j : Fin M, s.natMem j.val=RestrictedMaskBridge.encode (order j).val) ∧
    (∀ j : Fin M, s.realMem (2*j.val)=Real.tanh (coefficient N P a beta J (order j))) ∧
    s.realReg 510=logBase N P a beta h J := by
  let raw := encode order beta h epsilon delta J tape
  have htable (j : Fin M) := hs.2.2.1 j.val (by simpa only [nat_count] using j.isLt)
  have hm (j : Fin M) := hs.2.1 j.val (by simpa only [nat_count] using j.isLt)
  have hed (j : Fin M) := tableEdge_physical order beta h epsilon delta J tape a params hparams j
  refine ⟨?_,?_,?_⟩
  · intro j
    simpa only [nat_count,nat_mask] using hm j
  · intro j
    rw [(htable j).1,hed j,prepareEdge_weight hN]
    rfl
  · rw [hs.2.2.2]
    simp only [nat_size,nat_count]
    rw [(real_fields order beta h epsilon delta J tape).1,prepareField_logBase]
    unfold logBase
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
    apply Fintype.sum_equiv order
    intro j
    rw [hed j,prepareEdge_logCosh hN]
    rfl

end Manuscript.RestrictedPhysicalPreparation
