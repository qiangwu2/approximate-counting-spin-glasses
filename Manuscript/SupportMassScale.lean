import Manuscript.SupportMassBound
import SpinGlass.CutoffTail

/-! The fixed support scale and exponential form used by the common cutoff search. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SupportMassScale
open Manuscript.SupportMassBound Manuscript.SupportMassCounting

def supportScale (P : Finset ℕ) (c : ℕ → ℝ) (rho pmin : ℝ) : ℝ :=
  (massConstant P c rho) ^ (1 / SupportExponent.kappaMin pmin)

theorem intensity_nonneg (P : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ p ∈ P, 0 ≤ c p) : 0 ≤ intensity P c :=
  Finset.sum_nonneg fun p hp => div_nonneg (hc p hp) (by positivity)

theorem one_le_massConstant (P : Finset ℕ) (c : ℕ → ℝ) (rho : ℝ)
    (hc : ∀ p ∈ P, 0 ≤ c p) (hrho : 1 ≤ rho) : 1 ≤ massConstant P c rho := by
  have hA := intensity_nonneg P c hc
  have he : 1 ≤ Real.exp (1 + intensity P c) := Real.one_le_exp_iff.mpr (by linarith)
  have hr : (1 : ℝ) ≤ rho^2 := by nlinarith
  exact one_le_mul_of_one_le_of_one_le he hr

theorem supportScale_pos (P : Finset ℕ) (c : ℕ → ℝ) (rho pmin : ℝ)
    (hc : ∀ p ∈ P, 0 ≤ c p) (hrho : 1 ≤ rho) : 0 < supportScale P c rho pmin := by
  apply Real.rpow_pos_of_pos
  linarith [one_le_massConstant P c rho hc hrho]

theorem one_le_supportScale (P : Finset ℕ) (c : ℕ → ℝ) (rho pmin : ℝ)
    (hc : ∀ p ∈ P, 0 ≤ c p) (hrho : 1 ≤ rho) (hpmin : 3 ≤ pmin) :
    1 ≤ supportScale P c rho pmin := by
  apply Real.one_le_rpow (one_le_massConstant P c rho hc hrho)
  exact div_nonneg zero_le_one (SupportExponent.kappaMin_pos pmin hpmin).le

theorem massConstant_le_supportScale_rpow (P : Finset ℕ) (c : ℕ → ℝ)
    (rho pmin alpha : ℝ) (hc : ∀ p ∈ P, 0 ≤ c p) (hrho : 1 ≤ rho)
    (hpmin : 3 ≤ pmin) (ha : (1 : ℝ)/4 ≤ alpha) :
    massConstant P c rho ≤ (supportScale P c rho pmin) ^ (SupportExponent.kappa pmin alpha) := by
  have hk := SupportExponent.kappaMin_pos pmin hpmin
  have hkk := SupportExponent.kappa_ge_kappaMin pmin alpha hpmin ha
  have hC := one_le_massConstant P c rho hc hrho
  unfold supportScale
  rw [← Real.rpow_mul (by linarith : 0 ≤ massConstant P c rho)]
  calc
    massConstant P c rho = (massConstant P c rho)^(1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hC (by
      have hi : (1 : ℝ) ≤ SupportExponent.kappa pmin alpha / SupportExponent.kappaMin pmin :=
        (le_div_iff₀ hk).2 (by simpa using hkk)
      simpa [div_eq_mul_inv, mul_comm] using hi)

/-- The constant `Cstar` depends only on the fixed minimum exponent. -/
theorem bound_le_scaled_power (P : Finset ℕ) (c : ℕ → ℝ)
    (rho pmin alpha t : ℝ) (v : ℕ)
    (hc : ∀ p ∈ P, 0 ≤ c p) (hrho : 1 ≤ rho) (hpmin : 3 ≤ pmin)
    (ha : (1 : ℝ)/4 ≤ alpha) (ht : 0 ≤ t) :
    (massConstant P c rho)^v * t^(SupportExponent.kappa pmin alpha*(v : ℝ)) ≤
      (supportScale P c rho pmin * t)^(SupportExponent.kappa pmin alpha*(v : ℝ)) := by
  have hC0 : 0 ≤ massConstant P c rho :=
    zero_le_one.trans (one_le_massConstant P c rho hc hrho)
  have hA0 := (supportScale_pos P c rho pmin hc hrho).le
  have hh := pow_le_pow_left₀ hC0 (massConstant_le_supportScale_rpow
    P c rho pmin alpha hc hrho hpmin ha) v
  have heq : ((supportScale P c rho pmin) ^ SupportExponent.kappa pmin alpha)^v =
      (supportScale P c rho pmin) ^ (SupportExponent.kappa pmin alpha*(v : ℝ)) := by
    rw [Real.rpow_mul hA0, Real.rpow_natCast]
  rw [heq] at hh
  rw [Real.mul_rpow hA0 ht]
  exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg ht _)

theorem scaled_power_eq_exp {N v : ℕ} (hN : 0 < N) (hv : 0 < v)
    {A kap : ℝ} (hA : 0 < A) :
    (A*((v : ℝ)/N))^(kap*(v : ℝ)) =
      Real.exp (-SpinGlass.CutoffTail.phi kap A N v) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  rw [Real.log_mul hA.ne' (div_pos hvR hNR).ne', Real.log_div hvR.ne' hNR.ne']
  unfold SpinGlass.CutoffTail.phi
  rw [Real.log_div hNR.ne' (mul_pos hA hvR).ne', Real.log_mul hA.ne' hvR.ne']
  ring

/-- Lemma 3.1 in the exact exponential form used by Lemma 5.1. -/
theorem supportMass_bound_exp {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (incidence : E → Finset V) (edges : Finset E)
    (hinj : Set.InjOn incidence edges) (P : Finset ℕ)
    (hP : ∀ e ∈ edges, (incidence e).card ∈ P)
    (pmin : ℝ) (hpmin : 3 ≤ pmin) (horders : ∀ p ∈ P, pmin ≤ (p : ℝ))
    (N v : ℕ) (hcard : Fintype.card V = N) (hv : 0 < v) (hvN : v ≤ N)
    (h rho alpha : ℝ) (hrho : 1 ≤ rho) (ha : (1 : ℝ)/4 ≤ alpha)
    (hfield : |Real.tanh h| ≤ rho*(N : ℝ)^(-alpha))
    (c : ℕ → ℝ) (hc : ∀ p ∈ P, 0 ≤ c p)
    (r : E → ℝ) (hr : ∀ e ∈ edges, 0 ≤ r e)
    (hrc : ∀ e ∈ edges, r e ≤ c (incidence e).card / (N : ℝ)^((incidence e).card-1)) :
    supportMass incidence edges h r v ≤ Real.exp
      (-SpinGlass.CutoffTail.phi (SupportExponent.kappa pmin alpha)
        (supportScale P c rho pmin) N v) := by
  have hm := supportMass_bound incidence edges hinj P hP pmin hpmin horders
    N v hcard hv hvN h rho alpha hrho ha hfield c hc r hr hrc
  have hscaled := bound_le_scaled_power P c rho pmin alpha ((v : ℝ)/N) v
    hc hrho hpmin ha (by positivity)
  apply (hm.trans hscaled).trans_eq
  exact scaled_power_eq_exp (lt_of_lt_of_le hv hvN) hv (supportScale_pos P c rho pmin hc hrho)

end Manuscript.SupportMassScale
