import Manuscript.HigherOrderAlgorithm
import Manuscript.InputIndices
import SpinGlass.PolynomialRuntime

/-! Uniform polynomial cost of the actual higher-order support computation. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.HigherOrderCost
open Manuscript.HigherOrderAlgorithm Manuscript.HigherOrderTail
open Manuscript.Model Manuscript.MixedThreshold Manuscript.SupportExponent
open SpinGlass.ArithmeticEvaluation Manuscript.UniformMixedMass

/-- A fixed growth rate independent of the supplied field and system size. -/
def growth (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) : ℝ :=
  max 0 (max (Cutoffs.workConstant (kappaMin pmin) (scale P a B rho pmin) 2)
    (Real.log 2/Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax)))

def amplitude (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) : ℝ :=
  60*(P.card+1)*((2 : ℝ)^(Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin))+1)

theorem scale_ge_one (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) (hpmin : 3 ≤ pmin) :
    1 ≤ scale P a B rho pmin :=
  SupportMassScale.one_le_supportScale P (edgeIntensity a B) (max 1 rho) pmin
    (fun p hp => by unfold edgeIntensity; positivity) (le_max_left _ _) hpmin

theorem layerConstant_physical {N pmax : ℕ} (hN : 0 < N) (P : Finset ℕ)
    (hmax : ∀ p ∈ P, p ≤ pmax) :
    SupportExecution.layerConstant N (Fintype.card (Edge N P)) ≤
      60*(P.card+1)*(N+1)^(pmax+2) := by
  have hc := InputIndices.card_edges_le hN P hmax
  have hp : N^pmax ≤ (N+1)^pmax := Nat.pow_le_pow_left (by omega) _
  have hp1 : 1 ≤ (N+1)^pmax := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.mul_le_mul_left P.card hp
  have hc1 : Fintype.card (Edge N P)+1 ≤ (P.card+1)*(N+1)^pmax := by nlinarith
  unfold SupportExecution.layerConstant
  rw [pow_add]
  nlinarith [Nat.mul_le_mul_right (60*(N+1)^2) hc1]

theorem exact_cube_bound {N N0 : ℕ} {nu Lambda g : ℝ}
    (hnu : 0 < nu) (hLam : 0 ≤ Lambda) (hg : 0 ≤ g)
    (hgr : Real.log 2/nu ≤ g) (hex : N < N0 ∨ nu*N ≤ Lambda) :
    (2 : ℝ)^N ≤ ((2 : ℝ)^N0+1)*Real.exp (g*Lambda) := by
  have he : 1 ≤ Real.exp (g*Lambda) := Real.one_le_exp_iff.mpr (mul_nonneg hg hLam)
  rcases hex with hN | hN
  · have hp : (2 : ℝ)^N ≤ (2 : ℝ)^N0 := pow_le_pow_right₀ (by norm_num) hN.le
    have hn : 0 ≤ (2 : ℝ)^N0 := by positivity
    nlinarith
  · have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left hN (div_nonneg hl hnu.le)
    have hcancel : (Real.log 2/nu)*(nu*(N : ℝ)) = (N : ℝ)*Real.log 2 := by field_simp
    rw [hcancel] at hmul
    have hbound := hmul.trans (mul_le_mul_of_nonneg_right hgr hLam)
    have hpow : (2 : ℝ)^N = Real.exp ((N : ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]
    rw [hpow]
    exact (Real.exp_le_exp.mpr hbound).trans
      (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N0]))

/-- Actual first-crossing properties, for reuse in the runtime proof. -/
theorem selected_spec (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    {B rho pmin h u : ℝ} (hpmin : 3 ≤ pmin)
    (hC : 0 ≤ massConstant P a (betaPlus P a B^2) rho)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ))) (hu : 0 < u) (hu1 : u < 1)
    (hex : ¬ exactBranch N pmax P a B rho pmin u) :
    1 ≤ selectedSize N P a B rho pmin h u ∧
      selectedSize N P a B rho pmin h u ≤
        Nat.floor (Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin)*N) ∧
      ∀ j : ℕ, 1 ≤ j → j < selectedSize N P a B rho pmin h u →
        SpinGlass.CutoffTail.phi (HigherFieldExponent.selectedKappa N (max 1 rho) pmin h)
          (scale P a B rho pmin) N j < budget P a B rho u := by
  have hN0 : Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin) ≤ N :=
    Nat.le_of_not_gt (fun hn => hex (Or.inl hn))
  have hsmall : budget P a B rho u <
    Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax)*N :=
    lt_of_not_ge (fun hl => hex (Or.inr hl))
  have hN4 := (Cutoffs.sizeThreshold_ge_four _ _ _).trans hN0
  have hNs : 2/Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin) ≤ (N : ℝ) :=
    (Cutoffs.sizeThreshold_ge_scale _ _ _).trans (by exact_mod_cast hN0)
  have hf : |h| ≤ max 1 rho*(N : ℝ)^(-(1/4 : ℝ)) :=
    hfield.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  have hkap := HigherFieldExponent.selectedKappa_ge_min N hN4 (le_max_left 1 rho) hpmin hf
  have hLam : 0 < budget P a B rho u :=
    SpinGlass.AlgorithmBudgets.logBudget_pos (by unfold errorConstant; linarith) hu hu1
  obtain ⟨m,hm,hm1,hmrange,hmPhi,hmfirst⟩ := Cutoffs.cutoffScan_correct
    (kappaMin_pos pmin hpmin) hkap (scale_pos P a B rho pmin) hNs hLam hsmall
  simpa only [selectedSize,hm,Option.getD_some] using And.intro hm1 (And.intro hmrange hmfirst)

/-- Both the exact and truncated branches satisfy one fixed exponential-budget
bound. All finite-support and local-spin loops are the counted implementations. -/
theorem run_envelope (N : ℕ) (hN : 0 < N) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p)
    (pmin : ℝ) (hpmin : 3 ≤ pmin) (horders : ∀ p ∈ P, pmin ≤ (p : ℝ))
    (pmax : ℕ) (hmax : ∀ p ∈ P, p ≤ pmax)
    {B rho beta h u : ℝ} (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ))) (hu : 0 < u) (hu1 : u < 1)
    (J : Edge N P → ℝ) :
    ((run N pmax P a B rho pmin beta h u J).operations : ℝ) ≤
      amplitude pmax P a B rho pmin * ((N : ℝ)+1)^(pmax+3)*
        Real.exp (growth pmax P a B rho pmin*budget P a B rho u) := by
  classical
  have hp : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have hh := hpmin.trans (horders p hp)
    have h3 : 3 ≤ p := by exact_mod_cast hh
    omega
  have hpmax : 0 < pmax := by
    obtain ⟨p,hpP⟩ := hP
    have := hp p hpP
    have := hmax p hpP
    omega
  have hC : 0 ≤ massConstant P a (betaPlus P a B^2) rho :=
    zero_le_one.trans (massConstant_ge_one P a hP ha hp
      (betaPlus_sq_range P a hP ha hp hB hBT).1.le
      (betaPlus_sq_range P a hP ha hp hB hBT).2)
  have hLam : 0 < budget P a B rho u :=
    SpinGlass.AlgorithmBudgets.logBudget_pos (by unfold errorConstant; linarith) hu hu1
  have hg : 0 ≤ growth pmax P a B rho pmin := le_max_left _ _
  have hCt : Cutoffs.workConstant (kappaMin pmin) (scale P a B rho pmin) 2 ≤
      growth pmax P a B rho pmin := (le_max_left _ _).trans (le_max_right _ _)
  have hgr : Real.log 2/Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax) ≤
      growth pmax P a B rho pmin := (le_max_right _ _).trans (le_max_right _ _)
  have hlocal : (SupportExecution.layerConstant N (Fintype.card (Edge N P)) : ℝ) ≤
      60*(P.card+1)*((N : ℝ)+1)^(pmax+2) := by exact_mod_cast layerConstant_physical hN P hmax
  have hNs : (1 : ℝ) ≤ (N : ℝ)+1 := by linarith [Nat.cast_nonneg N (α := ℝ)]
  have hsize : ((N : ℝ)+1)^(pmax+2) ≤ ((N : ℝ)+1)^(pmax+3) :=
    pow_le_pow_right₀ hNs (by omega)
  have hfactor : (1 : ℝ) ≤ 2^(Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin))+1 := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin))]
  by_cases hex : exactBranch N pmax P a B rho pmin u
  · have hcost := SupportExecution.local_cost (Subtype.val : Edge N P → Finset (Fin N)) Finset.univ
      (FieldExpansion.spinWeight h) (fun e => SpinGlass.Disorder.weight (DisorderOrthogonality.physicalScale N P a beta e) (J e)) Finset.univ
    have hcost' : ((run N pmax P a B rho pmin beta h u J).operations : ℝ) ≤
        (SupportExecution.layerConstant N (Fintype.card (Edge N P)) : ℝ)*(2 : ℝ)^N := by
      unfold run evaluator selectedCutoff
      rw [if_pos hex,SupportExecution.supportSum,if_neg (by simp)]
      have hc : SupportExecution.localConstant N (Fintype.card (Edge N P)) ≤
          SupportExecution.layerConstant N (Fintype.card (Edge N P)) := by
        unfold SupportExecution.localConstant SupportExecution.layerConstant
        nlinarith
      simp only [Finset.card_univ,Fintype.card_fin] at hcost
      exact_mod_cast hcost.trans (Nat.mul_le_mul_right _ hc)
    have hnu := Cutoffs.nu_pos (kappaMin_pos pmin hpmin) (scale_pos P a B rho pmin)
      (c1_pos P a (rho := rho) (pmin := pmin) hB hBT hpmax)
    have htwo := exact_cube_bound hnu hLam.le hg hgr hex
    calc
      _ ≤ (60*(P.card+1)*((N : ℝ)+1)^(pmax+2))*
        (((2 : ℝ)^Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin)+1)*
          Real.exp (growth pmax P a B rho pmin*budget P a B rho u)) := by
        exact hcost'.trans (mul_le_mul hlocal htwo (by positivity) (by positivity))
      _ ≤ _ := by
        unfold amplitude
        have hh := mul_le_mul_of_nonneg_left hsize
          (show 0 ≤ 60*(P.card+1)*
            ((2 : ℝ)^Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin)+1)*
            Real.exp (growth pmax P a B rho pmin*budget P a B rho u) by positivity)
        simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  · obtain ⟨hm1,hmrange,hmfirst⟩ := selected_spec N pmax P a hpmin hC hfield hu hu1 hex
    have hfloor : Nat.floor (Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin)*N) ≤ N := by
      have hf := Nat.floor_le (show 0 ≤ Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin)*(N : ℝ) by
        exact mul_nonneg (Cutoffs.gamma_pos (scale_pos P a B rho pmin)).le (Nat.cast_nonneg N))
      have hb := mul_le_mul_of_nonneg_right (Cutoffs.gamma_le_one (kappaMin pmin) (scale P a B rho pmin)) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      exact_mod_cast (hf.trans (by simpa using hb) : (Nat.floor (Cutoffs.gamma (kappaMin pmin) (scale P a B rho pmin)*N) : ℝ) ≤ N)
    have hk : selectedSize N P a B rho pmin h u-1 < N := by omega
    have hN4 : 4 ≤ N := (Cutoffs.sizeThreshold_ge_four _ _ _).trans
      (Nat.le_of_not_gt (fun hn => hex (Or.inl hn)))
    have hf : |h| ≤ max 1 rho*(N : ℝ)^(-(1/4 : ℝ)) :=
      hfield.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    have hkap := HigherFieldExponent.selectedKappa_ge_min N hN4 (le_max_left 1 rho) hpmin hf
    have hbin := Cutoffs.selected_binomial_cost (kappaMin_pos pmin hpmin) hkap (scale_ge_one P a B rho pmin hpmin)
      (by norm_num : (1 : ℝ) ≤ 2) hN hLam.le hmrange hmfirst
    have hcost := SupportExecution.truncated_cost (Subtype.val : Edge N P → Finset (Fin N)) Finset.univ
      (FieldExpansion.spinWeight h) (fun e => SpinGlass.Disorder.weight (DisorderOrthogonality.physicalScale N P a beta e) (J e))
      (show selectedSize N P a B rho pmin h u-1 ≤ Fintype.card (Fin N) by simpa using hk.le)
    have hmstep : selectedSize N P a B rho pmin h u-1+1=selectedSize N P a B rho pmin h u := by omega
    simp only [Finset.card_univ,Fintype.card_fin,hmstep] at hcost
    have hcost' : ((run N pmax P a B rho pmin beta h u J).operations : ℝ) ≤
        (SupportExecution.layerConstant N (Fintype.card (Edge N P)) : ℝ)*
          (∑ j ∈ Finset.range (selectedSize N P a B rho pmin h u), (N.choose j : ℝ)*(2 : ℝ)^j) := by
      unfold run evaluator selectedCutoff
      rw [if_neg hex,SupportExecution.supportSum,if_pos (by simpa using hk)]
      exact_mod_cast hcost
    have hge := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCt hLam.le)
    calc
      _ ≤ (60*(P.card+1)*((N : ℝ)+1)^(pmax+2))*
          (((N : ℝ)+1)*Real.exp (growth pmax P a B rho pmin*budget P a B rho u)) := by
        exact hcost'.trans (mul_le_mul hlocal (hbin.trans (mul_le_mul_of_nonneg_left hge (by positivity)))
          (by positivity) (by positivity))
      _ ≤ _ := by
        unfold amplitude
        have hh := mul_le_mul_of_nonneg_left hfactor
          (show 0 ≤ 60*(P.card+1)*((N : ℝ)+1)^(pmax+2)*((N : ℝ)+1)*
            Real.exp (growth pmax P a B rho pmin*budget P a B rho u) by positivity)
        simp only [mul_one] at hh
        simpa only [pow_add,pow_succ,pow_zero,mul_one,mul_assoc,mul_left_comm,mul_comm] using hh

end Manuscript.HigherOrderCost
