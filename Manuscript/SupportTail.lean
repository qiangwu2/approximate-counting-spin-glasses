import Manuscript.SupportMassScale
import Manuscript.UniformGraphMass

/-! Actual higher-order support tails, split into local decay and the edge tail. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SupportTail
open Manuscript.FieldExpansion Manuscript.SupportEvaluation Manuscript.SupportDegrees
open Manuscript.SupportMassCounting Manuscript.SupportMassBound Manuscript.SupportMassScale
open Manuscript.UniformGraphMass

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

def supportTail (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (r : E → ℝ) (k : ℕ) : ℝ :=
  graphMass incidence (edges.powerset.filter (fun Γ => k < (support incidence Γ).card)) h r

theorem supportTail_split (incidence : E → Finset V) (edges : Finset E)
    (h : ℝ) (r : E → ℝ) (k K : ℕ) (hkK : k ≤ K) :
    supportTail incidence edges h r k =
      (∑ v ∈ Finset.Ico (k+1) (K+1), supportMass incidence edges h r v) +
        supportTail incidence edges h r K := by
  have hf := Finset.sum_fiberwise_eq_sum_filter edges.powerset (Finset.Ico (k+1) (K+1))
    (fun Γ => (support incidence Γ).card)
    (fun Γ => Real.tanh h ^ (2*(boundary incidence Γ).card) * ∏ e ∈ Γ, r e)
  change (∑ v ∈ Finset.Ico (k+1) (K+1), supportMass incidence edges h r v) = _ at hf
  rw [hf]
  unfold supportTail graphMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  simp only [Finset.mem_Ico]
  by_cases hk : k < (support incidence Γ).card
  · by_cases hK : K < (support incidence Γ).card
    · have hn : ¬(k+1 ≤ (support incidence Γ).card ∧ (support incidence Γ).card < K+1) := by omega
      simp [hk, hK, hn]
    · have hi : k+1 ≤ (support incidence Γ).card ∧ (support incidence Γ).card < K+1 := by omega
      simp [hk, hK, hi]
  · have hK : ¬K < (support incidence Γ).card := by omega
    have hn : ¬(k+1 ≤ (support incidence Γ).card ∧ (support incidence Γ).card < K+1) := by omega
    simp [hk, hK, hn]

/-- Every used vertex belongs to some edge, and each edge has at most `pmax` vertices. -/
theorem support_card_le_max_order_mul (incidence : E → Finset V) (Γ : Finset E)
    (pmax : ℕ) (hmax : ∀ e ∈ Γ, (incidence e).card ≤ pmax) :
    (support incidence Γ).card ≤ pmax * Γ.card := by
  apply (support_card_le_totalDegree incidence Γ).trans
  unfold totalDegree
  calc
    _ ≤ ∑ _e ∈ Γ, pmax := Finset.sum_le_sum hmax
    _ = _ := by simp [Nat.mul_comm]

theorem geometric_tail_eq_exp {q gamma : ℝ} (hq : 0 < q) (pmax N : ℕ) :
    q ^ (gamma*(N : ℝ)/(pmax : ℝ)) =
      Real.exp (-(gamma/(pmax : ℝ)*Real.log (1/q))*(N : ℝ)) := by
  rw [Real.rpow_def_of_pos hq, one_div, Real.log_inv]
  congr 1
  ring

/-- The large-support contribution is controlled by the actual comparison mass. -/
theorem large_support_tail (incidence : E → Finset V) (edges : Finset E)
    (pmax N : ℕ) (hpmax : 0 < pmax) (hmax : ∀ e ∈ edges, (incidence e).card ≤ pmax)
    (h : ℝ) (r z : E → ℝ) {q gamma C : ℝ}
    (hr : ∀ e, 0 ≤ r e) (hz : ∀ e, 0 ≤ z e) (hq : 0 < q) (hq1 : q ≤ 1)
    (hgamma : 0 ≤ gamma) (hrq : ∀ e, r e ≤ q*z e)
    (hC : graphMass incidence edges.powerset h z ≤ C) :
    supportTail incidence edges h r (Nat.floor (gamma*N)) ≤
      C * Real.exp (-(gamma/(pmax : ℝ)*Real.log (1/q))*(N : ℝ)) := by
  have hpR : (0 : ℝ) < pmax := by exact_mod_cast hpmax
  have hγN : 0 ≤ gamma*(N : ℝ) := by positivity
  have ht : 0 ≤ gamma*(N : ℝ)/(pmax : ℝ) := by positivity
  have hsub : edges.powerset.filter (fun Γ => Nat.floor (gamma*N) < (support incidence Γ).card) ⊆
      edges.powerset.filter (fun Γ => gamma*(N : ℝ)/(pmax : ℝ) < (Γ.card : ℝ)) := by
    intro Γ hΓ
    obtain ⟨hG, hsupp⟩ := Finset.mem_filter.mp hΓ
    have hsup : gamma*(N : ℝ) < (support incidence Γ).card := (Nat.floor_lt hγN).mp hsupp
    have hd := support_card_le_max_order_mul incidence Γ pmax
      (fun e he => hmax e ((Finset.mem_powerset.mp hG) he))
    have hdr : ((support incidence Γ).card : ℝ) ≤ (pmax : ℝ)*Γ.card := by exact_mod_cast hd
    apply Finset.mem_filter.mpr
    refine ⟨hG, (div_lt_iff₀ hpR).mpr ?_⟩
    nlinarith
  have hcompare : supportTail incidence edges h r (Nat.floor (gamma*N)) ≤
      graphMass incidence (edges.powerset.filter
        (fun Γ => gamma*(N : ℝ)/(pmax : ℝ) < (Γ.card : ℝ))) h r := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Γ hΓ hn =>
      mul_nonneg (fieldFactor_nonneg incidence Γ h) (Finset.prod_nonneg (fun e he => hr e)))
  have hedge := finite_geometric_tail_real incidence edges.powerset h r z hr hz hq hq1 hrq ht hC
  have hh := hcompare.trans (hedge.1.trans hedge.2)
  rw [geometric_tail_eq_exp hq pmax N] at hh
  exact hh

/-- The complete support truncation bound; its local mass estimate is proved
inside the theorem. The global comparison mass is the common analytic input. -/
theorem support_truncation_tail (incidence : E → Finset V) (edges : Finset E)
    (hinj : Set.InjOn incidence edges) (P : Finset ℕ)
    (hP : ∀ e ∈ edges, (incidence e).card ∈ P)
    (pmin : ℝ) (hpmin : 3 ≤ pmin) (horders : ∀ p ∈ P, pmin ≤ (p : ℝ))
    (pmax N cutoff : ℕ) (hpmax : 0 < pmax) (hcard : Fintype.card V = N)
    (hmax : ∀ e ∈ edges, (incidence e).card ≤ pmax)
    (h rho alpha : ℝ) (hrho : 1 ≤ rho) (ha : (1 : ℝ)/4 ≤ alpha)
    (hfield : |Real.tanh h| ≤ rho*(N : ℝ)^(-alpha))
    (c : ℕ → ℝ) (hc : ∀ p ∈ P, 0 ≤ c p) (r z : E → ℝ)
    (hr : ∀ e, 0 ≤ r e) (hz : ∀ e, 0 ≤ z e)
    (hrc : ∀ e ∈ edges, r e ≤ c (incidence e).card / (N : ℝ)^((incidence e).card-1))
    {q gamma C : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hrq : ∀ e, r e ≤ q*z e)
    (hC : graphMass incidence edges.powerset h z ≤ C)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hgap : 2 ≤ SupportExponent.kappa pmin alpha *
      (Real.log (1/(supportScale P c rho pmin*gamma))-1))
    (hcut : cutoff < Nat.floor (gamma*N)) :
    supportTail incidence edges h r cutoff ≤
      2 * Real.exp (-SpinGlass.CutoffTail.phi (SupportExponent.kappa pmin alpha)
        (supportScale P c rho pmin) N (cutoff+1)) +
      C * Real.exp (-(gamma/(pmax : ℝ)*Real.log (1/q))*(N : ℝ)) := by
  have hN : 0 < N := by
    by_contra hn
    have : N = 0 := by omega
    simp [this] at hcut
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfloor : (Nat.floor (gamma*N) : ℝ) ≤ gamma*N := Nat.floor_le (by positivity)
  have hsmall : (∑ v ∈ Finset.Ico (cutoff+1) (Nat.floor (gamma*N)+1),
      supportMass incidence edges h r v) ≤
      2 * Real.exp (-SpinGlass.CutoffTail.phi (SupportExponent.kappa pmin alpha)
        (supportScale P c rho pmin) N (cutoff+1)) := by
    calc
      _ ≤ ∑ v ∈ Finset.Ico (cutoff+1) (Nat.floor (gamma*N)+1),
          Real.exp (-SpinGlass.CutoffTail.phi (SupportExponent.kappa pmin alpha)
            (supportScale P c rho pmin) N v) := by
        apply Finset.sum_le_sum
        intro v hv
        have hvi := Finset.mem_Ico.mp hv
        have hvpos : 0 < v := by omega
        have hvle : (v : ℝ) ≤ gamma*N := by
          have hvK : (v : ℝ) ≤ (Nat.floor (gamma*N) : ℝ) := by
            exact_mod_cast (show v ≤ Nat.floor (gamma*N) by omega)
          exact hvK.trans hfloor
        have hvN : v ≤ N := by
          have hgN := mul_le_mul_of_nonneg_right hgamma1 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
          have hvr : (v : ℝ) ≤ N := by nlinarith
          exact_mod_cast hvr
        exact supportMass_bound_exp incidence edges hinj P hP pmin hpmin horders N v hcard
          hvpos hvN h rho alpha hrho ha hfield c hc r (fun e _ => hr e) hrc
      _ ≤ _ := by
        simpa only [Nat.cast_add, Nat.cast_one] using SpinGlass.CutoffTail.phi_tail
          (SupportExponent.kappa_pos pmin alpha hpmin ha).le
          (supportScale_pos P c rho pmin hc hrho) hNR hgamma hgap
          (m := cutoff+1) (by omega) hfloor
  rw [supportTail_split incidence edges h r cutoff (Nat.floor (gamma*N)) hcut.le]
  exact add_le_add hsmall (large_support_tail incidence edges pmax N hpmax hmax h r z
    hr hz hq hq1 hgamma.le hrq hC)

end Manuscript.SupportTail
