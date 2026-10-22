import Manuscript.SKChargedExecution

noncomputable section
namespace Manuscript.SKBranchReindex
open SpinGlass SKCoefficient
open scoped BigOperators

def coordinate {b c K : ℕ} (e : Fin b ≃ Fin c) : Basis c K ≃ Basis b K where
  toFun x := (x.1,x.2.1,fun i => x.2.2 (e i))
  invFun x := (x.1,x.2.1,fun i => x.2.2 (e.symm i))
  left_inv x := by ext i <;> simp
  right_inv x := by ext i <;> simp

theorem coordinate_symm {b c K : ℕ} (e : Fin b ≃ Fin c) :
    (coordinate (K:=K) e).symm=coordinate e.symm := rfl

def pull {b c K : ℕ} (e : Fin b ≃ Fin c) (f : Coefficients c K) : Coefficients b K :=
  fun x => f ((coordinate e).symm x)

theorem compatibility {b c K : ℕ} (e : Fin b ≃ Fin c) (x y : Basis c K) :
    compatible (coordinate e x) (coordinate e y) ↔ compatible x y := Iff.rfl

theorem combine_map {b c K : ℕ} (e : Fin b ≃ Fin c) (x y : Basis c K)
    (h : compatible x y) :
    combine (coordinate e x) (coordinate e y) h=coordinate e (combine x y h) := rfl

theorem contribution_map {b c K : ℕ} (e : Fin b ≃ Fin c) (x y z : Basis c K)
    (a d : ℝ) :
    pairContribution (coordinate e x) (coordinate e y) (coordinate e z) a d=
      pairContribution x y z a d := by
  unfold pairContribution basisMul
  by_cases h : compatible x y
  · have hh := (compatibility e x y).mpr h
    rw [dif_pos hh,dif_pos h,combine_map]
    simp only [Option.some.injEq,(coordinate e).injective.eq_iff]
  · have hh : ¬compatible (coordinate e x) (coordinate e y) := fun hh => h ((compatibility e x y).mp hh)
    rw [dif_neg hh,dif_neg h]
    simp

theorem pull_mul {b c K : ℕ} (e : Fin b ≃ Fin c) (f g : Coefficients c K) :
    pull e (mul f g)=mul (pull e f) (pull e g) := by
  funext z
  obtain ⟨z,rfl⟩ := (coordinate e).surjective z
  simp only [pull,Equiv.symm_apply_apply,mul]
  apply Fintype.sum_equiv (coordinate e)
  intro x
  apply Fintype.sum_equiv (coordinate e)
  intro y
  simp only [Equiv.symm_apply_apply]
  exact (contribution_map e x y z _ _).symm

def ringEquiv {b c K : ℕ} (e : Fin b ≃ Fin c) : SKRing.Element c K ≃+* SKRing.Element b K where
  toFun f := ⟨pull e f.coeff⟩
  invFun f := ⟨pull e.symm f.coeff⟩
  left_inv f := by
    apply SKRing.ext
    funext x
    simp [pull,coordinate]
  right_inv f := by
    apply SKRing.ext
    funext x
    simp [pull,coordinate]
  map_mul' f g := SKRing.ext (pull_mul e f.coeff g.coeff)
  map_add' f g := rfl

@[simp] theorem ringEquiv_coeff {b c K : ℕ} (e : Fin b ≃ Fin c) (f : SKRing.Element c K) :
    (ringEquiv e f).coeff=pull e f.coeff := rfl

theorem single_map {b c K : ℕ} (e : Fin b ≃ Fin c) (x : Basis c K) (a : ℝ) :
    pull e (single x a)=single (coordinate e x) a := by
  funext y
  obtain ⟨y,rfl⟩ := (coordinate e).surjective y
  simp [pull,single,(coordinate e).injective.eq_iff]

theorem monomial_map {b c K : ℕ} (e : Fin b ≃ Fin c) (x : Basis c K) (a : ℝ) :
    ringEquiv e (SKRing.monomial x a)=SKRing.monomial (coordinate e x) a :=
  SKRing.ext (single_map e x a)

theorem insertMonomial_map {b c K : ℕ} (e : Fin b ≃ Fin c)
    (k : ℕ) (S : Finset (Fin K)) (d : Fin c → CappedDegree) (a : ℝ) :
    ringEquiv e (SKFastEvaluator.insertMonomial k S d a)=
      SKFastEvaluator.insertMonomial k S (d ∘ e) a := by
  unfold SKFastEvaluator.insertMonomial
  split_ifs
  · exact monomial_map e _ a
  · exact map_zero (ringEquiv e)

theorem pathDegrees_map {b c : ℕ} (e : Fin b ≃ Fin c) (a d : Fin b) :
    SKFastEvaluator.pathDegrees (e a) (e d) ∘ e=SKFastEvaluator.pathDegrees a d := by
  funext i
  simp [SKFastEvaluator.pathDegrees,e.injective.eq_iff]

end Manuscript.SKBranchReindex
