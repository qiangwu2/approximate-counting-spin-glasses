import Manuscript.SKPrimitivePair
import Manuscript.SKPrimitiveCycleInsert

/-! Coefficient-level specifications of the actual primitive point writes. -/
noncomputable section
namespace Manuscript.SKPrimitiveTerms
open RestrictedMachine SKBasisEncoding
open SpinGlass SKCoefficient SKFastEvaluator SKCountedExecution
open SKChargedPrimitiveExecution
open scoped BigOperators

def pairTerm {V : Type*} [DecidableEq V] {N b K : ℕ}
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (a c : Fin b) (S : Finset (Fin K)) : Coefficients b K :=
  if SKPrimitivePair.valid a c S then
    (insertMonomial (SKPrimitivePair.charge q a c S) S (pathDegrees a c)
      (SKPrimitivePair.scalar branch outside f cache a c S)).coeff else 0

def cycleTerm {V : Type*} [DecidableEq V] {N b K : ℕ}
    (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (S : Finset (Fin K)) : Coefficients b K :=
  if 3≤S.card then (insertMonomial S.card S (fun _ => 0) (cachedCycle outside f cache S).value).coeff else 0

theorem pair_memory {V : Type*} [DecidableEq V] {N b K : ℕ}
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (a c : Fin b) (S : Finset (Fin K))
    (base : ℕ) (memory out : ℕ → ℝ) (old : Coefficients b K)
    (hm : ∀ y,memory (base+encode y)=old y)
    (hv : out=if SKPrimitivePair.valid a c S ∧ SKPrimitivePair.charge q a c S≤K then
      Function.update memory (SKPrimitivePair.insertionAddress q a c S base)
        (memory (SKPrimitivePair.insertionAddress q a c S base)+SKPrimitivePair.scalar branch outside f cache a c S)
      else memory) :
    (∀ y,out (base+encode y)=old y+pairTerm q branch outside f cache a c S y) ∧
    (∀ address,address<base → out address=memory address) := by
  by_cases hvalid : SKPrimitivePair.valid a c S <;> by_cases hcut : SKPrimitivePair.charge q a c S≤K
  · let z : Basis b K := (⟨SKPrimitivePair.charge q a c S,Nat.lt_succ_of_le hcut⟩,S,pathDegrees a c)
    have ha : SKPrimitivePair.insertionAddress q a c S base=base+encode z := by
      rw [encode_formula]; simp [SKPrimitivePair.insertionAddress,z,Nat.add_assoc]
    rw [if_pos ⟨hvalid,hcut⟩,ha] at hv
    constructor
    · intro y
      by_cases hy : y=z
      · subst y
        simp [hv,hm,pairTerm,hvalid,insertMonomial,hcut,SKRing.monomial,SKCoefficient.single,z]
      · have hi : encode y≠encode z := fun hh => hy (encode_injective b K hh)
        simp [hv,Function.update,hi,hy,hm,pairTerm,hvalid,insertMonomial,hcut,SKRing.monomial,SKCoefficient.single,z,Ne.symm hy]
    · intro address hlt
      have hn : address≠base+encode z := by omega
      simp [hv,Function.update,hn]
  all_goals constructor
  all_goals first
    | (intro y; simp [hv,hvalid,hcut,pairTerm,insertMonomial,SKRing.coeff_zero,hm])
    | (intro address hlt; simp [hv,hvalid,hcut])

theorem cycle_memory {V : Type*} [DecidableEq V] {N b K : ℕ}
    (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (S : Finset (Fin K))
    (base : ℕ) (memory out : ℕ → ℝ) (old : Coefficients b K)
    (hm : ∀ y,memory (base+encode y)=old y)
    (hv : out=if 3≤S.card then
      Function.update memory (SKPrimitiveCycleInsert.insertionAddress b base S)
        (memory (SKPrimitiveCycleInsert.insertionAddress b base S)+(cachedCycle outside f cache S).value)
      else memory) :
    (∀ y,out (base+encode y)=old y+cycleTerm outside f cache S y) ∧
    (∀ address,address<base → out address=memory address) := by
  have hcut : S.card≤K := by simpa using Finset.card_le_univ S
  by_cases hvalid : 3≤S.card
  · let z : Basis b K := (⟨S.card,Nat.lt_succ_of_le hcut⟩,S,fun _ => 0)
    have hz : (degreeEquiv b (fun _ => (0:CappedDegree))).val=0 := by simp [degree_formula]
    have ha : SKPrimitiveCycleInsert.insertionAddress b base S=base+encode z := by
      rw [encode_formula]; simp [SKPrimitiveCycleInsert.insertionAddress,z,hz]
    rw [if_pos hvalid,ha] at hv
    constructor
    · intro y
      by_cases hy : y=z
      · subst y
        simp [hv,hm,cycleTerm,hvalid,insertMonomial,hcut,SKRing.monomial,SKCoefficient.single,z]
      · have hi : encode y≠encode z := fun hh => hy (encode_injective b K hh)
        simp [hv,Function.update,hi,hy,hm,cycleTerm,hvalid,insertMonomial,hcut,SKRing.monomial,SKCoefficient.single,z,Ne.symm hy]
    · intro address hlt
      have hn : address≠base+encode z := by omega
      simp [hv,Function.update,hn]
  · constructor
    · intro y; simp [hv,hvalid,cycleTerm,hm]
    · intro address hlt; simp [hv,hvalid]

theorem pairTerm_eq {V : Type*} [DecidableEq V] {N b K : ℕ}
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (a c : Fin b) (S : Finset (Fin K)) :
    pairTerm q branch outside f cache a c S=
      instructionValue (primitiveInstruction q branch outside f cache (Sum.inr (Sum.inl (a,c,S))))+
      if a=c then instructionValue (primitiveInstruction q branch outside f cache (Sum.inr (Sum.inr (a,S)))) else 0 := by
  by_cases heq : a=c
  · subst c
    by_cases hcard : 2≤S.card <;> by_cases hcut : S.card-1+q a+q a≤K <;>
      simp [pairTerm,SKPrimitivePair.valid,SKPrimitivePair.charge,SKPrimitivePair.scalar,primitiveInstruction,
        hcard,hcut,insertInstruction_value,noInstruction_value,insertMonomial]
  · by_cases hlt : a<c
    · have hle : a≤c := le_of_lt hlt
      by_cases hcard : 1≤S.card <;> by_cases hcut : S.card-1+q a+q c≤K <;>
        simp [pairTerm,SKPrimitivePair.valid,SKPrimitivePair.charge,SKPrimitivePair.scalar,heq,hlt,hle,primitiveInstruction,
          hcard,hcut,insertInstruction_value,noInstruction_value,insertMonomial]
    · have hle : ¬a≤c := by omega
      simp [pairTerm,SKPrimitivePair.valid,heq,hle,primitiveInstruction,hlt,noInstruction_value]

theorem total_eq {V : Type*} [DecidableEq V] {N b K : ℕ}
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) :
    (∑ a,∑ c,∑ S,pairTerm q branch outside f cache a c S)+
      (∑ S,cycleTerm outside f cache S)=
      (assemble (primitiveInstruction q branch outside f cache)).value := by
  rw [assemble_value]
  simp only [PrimitiveKey,Fintype.sum_sum_type,Fintype.sum_prod_type,pairTerm_eq,Finset.sum_add_distrib]
  have hc (S : Finset (Fin K)) : cycleTerm outside f cache S=
      instructionValue (primitiveInstruction q branch outside f cache (Sum.inl S)) := by
    by_cases h : 3≤S.card <;> simp [cycleTerm,primitiveInstruction,h,insertInstruction_value,noInstruction_value]
  simp_rw [hc]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
  have hd (a : Fin b) (v : Coefficients b K) : (∑ c : Fin b,if a=c then v else 0)=v := by simp [eq_comm]
  simp_rw [hd]
  abel
end Manuscript.SKPrimitiveTerms
