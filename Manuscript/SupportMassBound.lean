import Manuscript.SupportMassWeights

/-! The complete mixed weak-field growing-support graphical mass estimate. -/
noncomputable section
open scoped BigOperators

namespace Manuscript.SupportMassBound
open Manuscript.FieldExpansion Manuscript.SupportEvaluation
open Manuscript.SupportMassCounting Manuscript.SupportMassWeights

/-- The fixed coefficient sum in Lemma 3.1 (`c_p = beta0² a_p²`). -/
def intensity (P : Finset ℕ) (c : ℕ → ℝ) : ℝ := ∑ p ∈ P, c p / p.factorial

/-- The manuscript's constant `C₀`. -/
def massConstant (P : Finset ℕ) (c : ℕ → ℝ) (rho : ℝ) : ℝ :=
  Real.exp (1 + intensity P c) * rho ^ 2

theorem normalization_identity {N v : ℕ} (hN : 0 < N) (hv : 0 < v)
    (rho kappa A : ℝ) :
    (Real.exp 1 * (N : ℝ) / v)^v *
      (rho ^ (2*v) * ((v : ℝ)/N)^((kappa+1)*(v : ℝ))) *
        Real.exp ((v : ℝ)*A) =
      (Real.exp (1+A)*rho^2)^v * ((v : ℝ)/N)^(kappa*(v : ℝ)) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have ht : 0 < (v : ℝ)/N := div_pos hvR hNR
  rw [pow_mul, Real.rpow_mul ht.le, Real.rpow_natCast,
    Real.exp_nat_mul, Real.rpow_mul ht.le, Real.rpow_natCast]
  rw [Real.rpow_add ht, Real.rpow_one, Real.exp_add]
  rw [← mul_pow, ← mul_pow, ← mul_pow, ← mul_pow]
  congr 1
  field_simp
  <;> ring

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- Lemma 3.1, proved for any finite injective array of mixed interactions.
All counting and degree/field estimates are discharged inside this theorem. -/
theorem supportMass_bound (incidence : E → Finset V) (edges : Finset E)
    (hinj : Set.InjOn incidence edges) (P : Finset ℕ)
    (hP : ∀ e ∈ edges, (incidence e).card ∈ P)
    (pmin : ℝ) (hpmin : 3 ≤ pmin)
    (horders : ∀ p ∈ P, pmin ≤ (p : ℝ))
    (N v : ℕ) (hcard : Fintype.card V = N) (hv : 0 < v) (hvN : v ≤ N)
    (h rho alpha : ℝ) (hrho : 1 ≤ rho) (ha : (1 : ℝ)/4 ≤ alpha)
    (hfield : |Real.tanh h| ≤ rho * (N : ℝ)^(-alpha))
    (c : ℕ → ℝ) (hc : ∀ p ∈ P, 0 ≤ c p)
    (r : E → ℝ) (hr : ∀ e ∈ edges, 0 ≤ r e)
    (hrc : ∀ e ∈ edges, r e ≤ c (incidence e).card / (N : ℝ)^((incidence e).card-1)) :
    supportMass incidence edges h r v ≤
      (massConstant P c rho)^v *
        ((v : ℝ)/N)^(SupportExponent.kappa pmin alpha * (v : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le hv hvN
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have ht : 0 < (v : ℝ)/N := div_pos hvR hNR
  have ht1 : (v : ℝ)/N ≤ 1 := (div_le_one hNR).mpr (by exact_mod_cast hvN)
  have hp : ∀ p ∈ P, 0 < p := by
    intro p hpP
    have hh := horders p hpP
    have : (0 : ℝ) < p := by linarith
    exact_mod_cast this
  let q : E → ℝ := fun e => c (incidence e).card / (v : ℝ)^((incidence e).card-1)
  let K : ℝ := rho^(2*v) * ((v : ℝ)/N)^((SupportExponent.kappa pmin alpha+1)*(v : ℝ))
  have hq : ∀ e ∈ edges, 0 ≤ q e := by
    intro e he
    exact div_nonneg (hc _ (hP e he)) (by positivity)
  have hfield' := weak_field_to_ratio hN hv h rho alpha (by linarith) (by linarith) hfield
  have hpoint : ∀ Γ ∈ supportFamily incidence edges v,
      Real.tanh h ^ (2*(boundary incidence Γ).card) * ∏ e ∈ Γ, r e ≤ K * ∏ e ∈ Γ, q e := by
    intro Γ hΓ
    obtain ⟨hΓsub, hΓv⟩ := Finset.mem_filter.mp hΓ
    have hsub : Γ ⊆ edges := Finset.mem_powerset.mp hΓsub
    have hh := graph_weight_le incidence Γ h rho ((v : ℝ)/N) pmin alpha hrho ht ht1
      (by linarith) (by linarith) (fun e he => horders _ (hP e (hsub he))) hfield'
      r q (fun e he => hr e (hsub he)) (fun e he => hq e (hsub he)) (by
        intro e he
        apply (hrc e (hsub he)).trans_eq
        exact edge_scale_identity hN hv (hp _ (hP e (hsub he))) _)
    simpa only [hΓv, K] using hh
  have hstart := support_sum_le_generating_product incidence edges v
    (fun Γ => Real.tanh h ^ (2*(boundary incidence Γ).card) * ∏ e ∈ Γ, r e)
    q hq K ((v : ℝ)*intensity P c) (by dsimp [K]; positivity) hpoint (by
      intro S hS
      exact induced_scale_sum_le incidence edges hinj P hP hp S v
        (Finset.mem_powersetCard.mp hS).2 hv c hc)
  rw [hcard] at hstart
  have hchoose := SpinGlass.SupportScalar.binomial_upper_bound N v
  calc
    _ ≤ (N.choose v : ℝ) * K * Real.exp ((v : ℝ)*intensity P c) := hstart
    _ ≤ (Real.exp 1 * (N : ℝ)/v)^v * K * Real.exp ((v : ℝ)*intensity P c) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right hchoose (by dsimp [K]; positivity)
    _ = _ := normalization_identity hN hv rho (SupportExponent.kappa pmin alpha) (intensity P c)

/-- The physical mixed-edge array automatically has the injectivity and active-order data. -/
theorem physical_supportMass_bound (N v : ℕ) (P : Finset ℕ)
    (pmin : ℝ) (hpmin : 3 ≤ pmin) (horders : ∀ p ∈ P, pmin ≤ (p : ℝ))
    (hv : 0 < v) (hvN : v ≤ N)
    (h rho alpha : ℝ) (hrho : 1 ≤ rho) (ha : (1 : ℝ)/4 ≤ alpha)
    (hfield : |Real.tanh h| ≤ rho*(N : ℝ)^(-alpha))
    (c : ℕ → ℝ) (hc : ∀ p ∈ P, 0 ≤ c p)
    (r : Model.Edge N P → ℝ) (hr : ∀ e, 0 ≤ r e)
    (hrc : ∀ e, r e ≤ c e.val.card / (N : ℝ)^(e.val.card-1)) :
    supportMass Subtype.val Finset.univ h r v ≤
      (massConstant P c rho)^v *
        ((v : ℝ)/N)^(SupportExponent.kappa pmin alpha*(v : ℝ)) := by
  apply supportMass_bound Subtype.val Finset.univ
    (fun e _ f _ hef => Subtype.ext hef) P (fun e _ => Model.edge_order_mem e)
    pmin hpmin horders N v (Fintype.card_fin N) hv hvN h rho alpha hrho ha hfield c hc r
    (fun e _ => hr e) (fun e _ => hrc e)

end Manuscript.SupportMassBound
