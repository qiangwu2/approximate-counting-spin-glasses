import Manuscript.RestrictedMaskLists
import Manuscript.RestrictedLocalSum

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedMaskBridge
open RestrictedMachine RestrictedMaskArithmetic RestrictedSpinTerm RestrictedLocalSum
open FieldExpansion SupportEvaluation SpinGlass.Expansion

theorem edgeProduct_range (N U T : ℕ) (incidence : ℕ→ℕ) (weight : ℕ→ℝ)
    (baseE baseW i m : ℕ) :
    edgeProduct N U T incidence weight baseE baseW i m =
      ∏j∈Finset.range m,(1+weight (baseW+2*(i+j))*character N (incidence (baseE+(i+j))) U T) := by
  induction m generalizing i with
  | zero => simp [edgeProduct]
  | succ m ih =>
    rw [edgeProduct,Finset.prod_range_succ']
    simp only [Nat.add_zero]
    rw [ih,mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [Nat.add_comm,Nat.add_left_comm]

theorem edgeProduct_encoded {N M : ℕ} (incidence : Fin M→Finset (Fin N))
    (w : Fin M→ℝ) (natMemory : ℕ→ℕ) (realMemory : ℕ→ℝ) (baseE baseW : ℕ)
    (hE : ∀ e : Fin M,natMemory (baseE+e.val)=encode (incidence e))
    (hW : ∀ e : Fin M,realMemory (baseW+2*e.val)=w e)
    (U T : Finset (Fin N)) :
    edgeProduct N (encode U) (encode T) natMemory realMemory baseE baseW 0 M=
      ∏e∈(Finset.univ : Finset (Fin M)).filter (fun e => incidence e⊆U),
        (1+w e*edgeCharacter incidence (spin T) e) := by
  rw [edgeProduct_range]
  simp only [Nat.zero_add]
  rw [←Fin.prod_univ_eq_prod_range,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro e he
  rw [hE,hW,character_edge]
  by_cases h : incidence e⊆U <;> simp [h]

theorem term_encoded (d : Data) (incidence : Fin d.M→Finset (Fin d.N))
    (w : Fin d.M→ℝ) (h : ℝ) (U T : Finset (Fin d.N))
    (hE : ∀ e : Fin d.M,d.natMemory (d.edgeBase+e.val)=encode (incidence e))
    (hW : ∀ e : Fin d.M,d.realMemory (d.weightBase+2*e.val)=w e)
    (hp : d.plus=spinWeight h false) (hm : d.minus=spinWeight h true) :
    term {d with U:=encode U} (encode T)=
      (∏v:U,spinWeight h (spin T v.val))*
        ∏e∈(Finset.univ : Finset (Fin d.M)).filter (fun e => incidence e⊆U),
          (1+w e*edgeCharacter (localIncidence incidence U) (fun v : U => spin T v.val) e) := by
  simp only [term]
  rw [hp,hm,field_spinWeight,edgeProduct_encoded incidence w d.natMemory d.realMemory d.edgeBase d.weightBase hE hW]
  rw [show (∏v:U,spinWeight h (spin T v.val)) = ∏v∈U,spinWeight h (spin T v) from
    Finset.prod_coe_sort U (fun v => spinWeight h (spin T v))]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  rw [edgeCharacter_restrict incidence U e (Finset.mem_filter.mp he).2 (spin T)]

/-- The actual generated mask list and actual digit-scan arithmetic give
exactly the paper's local biased spin average. Only physical cache/layout
equalities are premises, to be discharged by the input preparation stage. -/
theorem cube_terms_eq_localG (d : Data) (incidence : Fin d.M→Finset (Fin d.N))
    (w : Fin d.M→ℝ) (h : ℝ) (U : Finset (Fin d.N))
    (hE : ∀ e : Fin d.M,d.natMemory (d.edgeBase+e.val)=encode (incidence e))
    (hW : ∀ e : Fin d.M,d.realMemory (d.weightBase+2*e.val)=w e)
    (hp : d.plus=spinWeight h false) (hm : d.minus=spinWeight h true) :
    ((RestrictedCubes.masks d.N (encode U) 0 1).map (term {d with U:=encode U})).sum=
      localG incidence Finset.univ h w U := by
  rw [cube_masks_sum]
  simp_rw [term_encoded d incidence w h U _ hE hW hp hm]
  exact powerset_spin_sum U (fun σ =>
    (∏v:U,spinWeight h (σ v))*
      ∏e∈(Finset.univ : Finset (Fin d.M)).filter (fun e => incidence e⊆U),
        (1+w e*edgeCharacter (localIncidence incidence U) σ e))

end Manuscript.RestrictedMaskBridge
