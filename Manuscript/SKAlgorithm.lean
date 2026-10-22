import Manuscript.SKPhysicalModel
import Manuscript.SKColorTotalError
import Manuscript.HigherOrderAlgorithm
import Manuscript.LogApprox

/-! Algorithm 4's SK cutoffs and unconditional total mean-square estimate. -/

noncomputable section
open scoped BigOperators
namespace Manuscript.SKAlgorithm
open MeasureTheory SpinGlass.Disorder
open Manuscript.Model Manuscript.MixedThreshold
open SpinGlass.AlgorithmBudgets

def scale (B rho : ℝ) : ℝ := max 1 (SKBranching.branchConstant B (rho^2))
def q (a : ℕ → ℝ) (B : ℝ) : ℝ := theta {2} a B ^ 2
def c1 (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  (3*Cutoffs.gamma 1 (scale B rho)/2)*Real.log (1/q a B)
def errorConstant (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  8*(2*SKBranching.massConstant B (rho^2)+3*LogApprox.constant {2} a B rho)
def budget (a : ℕ → ℝ) (B rho u : ℝ) : ℝ := logBudget (errorConstant a B rho) u
def exactBranch (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ) : Prop :=
  N < Cutoffs.sizeThreshold 2 1 (scale B rho) ∨
    Cutoffs.nu 1 (scale B rho) (c1 a B rho)*N ≤ budget a B rho u
def selectedSize (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ) : ℕ :=
  (Cutoffs.cutoffScan 1 1 (scale B rho) N (budget a B rho u)).found.getD 1
def branchCutoff (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ) : ℕ := selectedSize N a B rho u-1
def edgeLimit (a : ℕ → ℝ) (B rho u : ℝ) : ℕ := edgeCutoff (q a B) (budget a B rho u)
def trials (a : ℕ → ℝ) (B rho u : ℝ) : ℕ := colorTrials (2*edgeLimit a B rho u) (budget a B rho u)
abbrev Colors (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ) :=
  SKColorEstimator.Colors (Fin N) (edgeLimit a B rho u) (trials a B rho u)
def colorLaw (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ) : Measure (Colors N a B rho u) :=
  SKColorEstimator.colorLaw (Fin N) (edgeLimit a B rho u) (trials a B rho u)

def run (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (χ : Colors N a B rho u) (J : Edge N {2} → ℝ) : ℝ := by
  classical
  exact if exactBranch N a B rho u then (HigherOrderTail.evaluator N {2} a beta h N J).value
    else SKColorEstimator.estimator Subtype.val Finset.univ (branchCutoff N a B rho u)
      (edgeLimit a B rho u) (trials a B rho u) h
      (DisorderOrthogonality.physicalScale N {2} a beta) χ J

theorem scale_pos (B rho : ℝ) : 0 < scale B rho := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
theorem scale_ge_one (B rho : ℝ) : 1 ≤ scale B rho := le_max_left _ _
theorem q_range (a : ℕ → ℝ) (ha : a 2 = 1) {B : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    0 < q a B ∧ q a B < 1 := by
  have ht := theta_range {2} a hB (by simpa only [betaF_sk a ha] using hB1)
  unfold q
  constructor
  · exact sq_pos_of_pos ht.1
  · nlinarith [ht.1,ht.2]

theorem constant_ge_one (a : ℕ → ℝ) (ha : a 2 = 1) {B rho : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    1 ≤ LogApprox.constant {2} a B rho :=
  LogApprox.constant_ge_one {2} a (by simp) (by simpa [ha]) (by simp) hB
    (by simpa only [betaF_sk a ha] using hB1)

theorem errorConstant_ge_one (a : ℕ → ℝ) (ha : a 2 = 1) {B rho : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    1 ≤ errorConstant a B rho := by
  have hc := constant_ge_one a ha (rho := rho) hB hB1
  have hb := SKBranching.massConstant_nonneg (F := rho^2) hB.le hB1
  unfold errorConstant
  linarith

theorem budget_pos (a : ℕ → ℝ) (ha : a 2 = 1) {B rho u : ℝ}
    (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1) : 0 < budget a B rho u :=
  logBudget_pos (errorConstant_ge_one a ha hB hB1) hu hu1

theorem edgeLimit_pos (a : ℕ → ℝ) (ha : a 2 = 1) {B rho u : ℝ}
    (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1) : 0 < edgeLimit a B rho u :=
  edgeCutoff_pos (q_range a ha hB hB1).1 (q_range a ha hB hB1).2 (budget_pos a ha hB hB1 hu hu1)

theorem trials_pos (a : ℕ → ℝ) (B rho u : ℝ) : 0 < trials a B rho u := colorTrials_pos _ _

theorem c1_pos (a : ℕ → ℝ) (ha : a 2 = 1) {B rho : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    0 < c1 a B rho := by
  have hg := Cutoffs.gamma_pos (kapMin := (1 : ℝ)) (scale_pos B rho)
  have hl := log_inv_pos (q_range a ha hB hB1).1 (q_range a ha hB hB1).2
  unfold c1
  positivity

theorem large_branch_factor (a : ℕ → ℝ) (ha : a 2 = 1) {B rho : ℝ}
    (hB : 0 < B) (hB1 : B < 1) (N : ℕ) :
    q a B ^ (3*Cutoffs.gamma 1 (scale B rho)*N/2) = Real.exp (-c1 a B rho*N) := by
  rw [Real.rpow_def_of_pos (q_range a ha hB hB1).1]
  unfold c1
  simp only [one_div,Real.log_inv]
  congr 1
  ring

theorem normalized_eq (N : ℕ) (a : ℕ → ℝ) (beta h : ℝ) (J : Edge N {2} → ℝ) :
    Model.normalizedPartition N {2} a beta h J =
      FieldExpansion.normalizedPartition Subtype.val Finset.univ h
        (fun e => DisorderOrthogonality.physicalScale N {2} a beta e*J e) := by
  rw [Model.normalizedPartition_eq_fieldNormalized]
  congr 1
  funext e
  exact DisorderOrthogonality.coefficient_eq_physicalScale N {2} a beta J e

theorem run_exact (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (hex : exactBranch N a B rho u) (χ : Colors N a B rho u) (J : Edge N {2} → ℝ) :
    run N a B rho beta h u χ J = Model.normalizedPartition N {2} a beta h J := by
  simp only [run,if_pos hex,HigherOrderTail.evaluator_value,HigherOrderAlgorithm.full_retained]

theorem partition_error_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (N : ℕ) (a : ℕ → ℝ) (ha : a 2 = 1) {B rho beta h u : ℝ}
    (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1) :
    Integrable (fun χJ : Colors N a B rho u × (Edge N {2} → ℝ) =>
      (run N a B rho beta h u χJ.1 χJ.2-Model.normalizedPartition N {2} a beta h χJ.2)^2)
      ((colorLaw N a B rho u).prod (iidLaw μ)) := by
  classical
  by_cases hex : exactBranch N a B rho u
  · simp_rw [run_exact N a B rho beta h u hex,sub_self,zero_pow (by decide : (2:ℕ)≠0)]
    exact integrable_zero _ _ _
  · simp_rw [run,if_neg hex,normalized_eq]
    exact SKColorEstimator.partition_error_integrable μ Subtype.val Finset.univ _
      (edgeLimit_pos a ha hB hB1 hu hu1) h _

/-- Both sources of SK approximation error are bounded on the actual joint
space of uniform coloring trials and the original iid physical disorder. -/
theorem mse_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℝ) (ha : a 2 = 1)
    {beta B h rho u : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B)
    (hB : 0 < B) (hB1 : B < 1)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ))) (hu : 0 < u) (hu1 : u < 1) :
    (∫ χJ : Colors N a B rho u × (Edge N {2} → ℝ),
      (run N a B rho beta h u χJ.1 χJ.2-Model.normalizedPartition N {2} a beta h χJ.2)^2
      ∂(colorLaw N a B rho u).prod (iidLaw μ)) ≤ u := by
  classical
  have hL := edgeLimit_pos a ha (rho := rho) hB hB1 hu hu1
  have hR := trials_pos a B rho u
  letI : Nonempty (Fin (2*edgeLimit a B rho u)) := ⟨⟨0,by omega⟩⟩
  have hLam := budget_pos a ha (rho := rho) hB hB1 hu hu1
  have hBT : B < betaF {2} a := by simpa only [betaF_sk a ha] using hB1
  have hC := constant_ge_one a ha (rho := rho) hB hB1
  have hCB := SKBranching.massConstant_nonneg (F := rho^2) hB.le hB1
  by_cases hex : exactBranch N a B rho u
  · simp_rw [run_exact N a B rho beta h u hex,sub_self,zero_pow (by decide : (2:ℕ)≠0),integral_zero]
    exact hu.le
  have hN0 : Cutoffs.sizeThreshold 2 1 (scale B rho) ≤ N :=
    Nat.le_of_not_gt (fun hn => hex (Or.inl hn))
  have hsmall : budget a B rho u < Cutoffs.nu 1 (scale B rho) (c1 a B rho)*N :=
    lt_of_not_ge (fun hh => hex (Or.inr hh))
  have hNs : 2/Cutoffs.gamma 1 (scale B rho) ≤ (N : ℝ) :=
    (Cutoffs.sizeThreshold_ge_scale _ _ _).trans (by exact_mod_cast hN0)
  obtain ⟨m,hm,hm1,hmrange,hmPhi,hmfirst⟩ := Cutoffs.cutoffScan_correct
    (by norm_num : (0 : ℝ)<1) (le_refl (1 : ℝ)) (scale_pos B rho) hNs hLam hsmall
  have hselected : selectedSize N a B rho u = m := by simp only [selectedSize,hm,Option.getD_some]
  have hD : branchCutoff N a B rho u = m-1 := by simp only [branchCutoff,hselected]
  have hcut : branchCutoff N a B rho u < Nat.floor (Cutoffs.gamma 1 (scale B rho)*N) := by omega
  have hp : ∀ e ∈ (Finset.univ : Finset (Edge N {2})), e.val.card = 2 := by
    intro e he
    simpa using edge_order_mem e
  have hcol := SKColorEstimator.partition_mse_le μ hμ Subtype.val Finset.univ
    (branchCutoff N a B rho u) hL hR hp h (DisorderOrthogonality.physicalScale N {2} a beta)
  simp_rw [← normalized_eq] at hcol
  rw [SKPhysicalModel.omitted_mass_eq μ hμ] at hcol
  have hmass := UniformPhysicalMass.physical_graphical_mass μ hunit N {2} a
    (by simp) (by simpa [ha]) (by simp) (by simpa using hN) hbeta hbetaB hB hBT hfield
  have hmass' : (∑ Γ ∈ (Finset.univ : Finset (Edge N {2})).powerset,
      SKColorEstimator.graphMass μ Subtype.val h (DisorderOrthogonality.physicalScale N {2} a beta) Γ) ≤
      LogApprox.constant {2} a B rho := hmass
  have htrial : Real.exp (2*(edgeLimit a B rho u : ℝ))/(trials a B rho u : ℝ) ≤
      Real.exp (-budget a B rho u) := by
    simpa only [trials,Nat.cast_mul,Nat.cast_ofNat] using colorTrials_error (2*edgeLimit a B rho u) (budget a B rho u)
  have hcolor : (Real.exp (2*(edgeLimit a B rho u : ℝ))/(trials a B rho u : ℝ))*
      (∑ Γ ∈ (Finset.univ : Finset (Edge N {2})).powerset,
        SKColorEstimator.graphMass μ Subtype.val h (DisorderOrthogonality.physicalScale N {2} a beta) Γ) ≤
      LogApprox.constant {2} a B rho*Real.exp (-budget a B rho u) := by
    calc
      _ ≤ (Real.exp (2*(edgeLimit a B rho u : ℝ))/(trials a B rho u : ℝ))*LogApprox.constant {2} a B rho :=
        mul_le_mul_of_nonneg_left hmass' (by positivity)
      _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right htrial (by linarith : 0 ≤ LogApprox.constant {2} a B rho)
  have ht := SKPhysicalModel.truncation_mse μ hμ hunit hN a ha hbeta hbetaB hB
    (betaPlus_range {2} a hB hBT).2.1
    (by simpa only [betaF_sk a ha] using (betaPlus_range {2} a hB hBT).2.2)
    hfield (scale_pos B rho) (le_max_right _ _) (Cutoffs.gamma_pos (scale_pos B rho))
    (by simpa only [one_mul] using Cutoffs.gamma_gap (by norm_num : (0:ℝ)<1) (scale_pos B rho))
    (L := edgeLimit a B rho u) hcut
  rw [SKPhysicalModel.massConstant_eq a ha] at ht
  change (∫ J : Edge N {2} → ℝ,
      (Model.normalizedPartition N {2} a beta h J-SKPhysicalModel.truncation N (branchCutoff N a B rho u) (edgeLimit a B rho u) a beta h J)^2 ∂iidLaw μ) ≤
    LogApprox.constant {2} a B rho*q a B^(edgeLimit a B rho u+1)+
      2*SKBranching.massConstant B (rho^2)*Real.exp (-SpinGlass.CutoffTail.phi 1 (scale B rho) N (branchCutoff N a B rho u+1))+
      LogApprox.constant {2} a B rho*q a B^(3*Cutoffs.gamma 1 (scale B rho)*N/2) at ht
  have hstep : branchCutoff N a B rho u+1=m := by omega
  have hstepR : (branchCutoff N a B rho u : ℝ)+1=(m : ℝ) := by exact_mod_cast hstep
  rw [hstepR,large_branch_factor a ha hB hB1 N] at ht
  have herr := Cutoffs.selected_error_bounds hsmall.le hmPhi
  have hedge := edgeCutoff_error (q_range a ha hB hB1).1 (q_range a ha hB hB1).2 hLam.le
  have htail : (∫ J : Edge N {2} → ℝ,
      (Model.normalizedPartition N {2} a beta h J-SKPhysicalModel.truncation N (branchCutoff N a B rho u) (edgeLimit a B rho u) a beta h J)^2 ∂iidLaw μ) ≤
    LogApprox.constant {2} a B rho*Real.exp (-budget a B rho u)+
      2*SKBranching.massConstant B (rho^2)*Real.exp (-budget a B rho u)+
      LogApprox.constant {2} a B rho*Real.exp (-4*budget a B rho u) := by
    apply ht.trans
    exact add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hedge (by linarith : 0 ≤ LogApprox.constant {2} a B rho))
        (mul_le_mul_of_nonneg_left herr.1 (by positivity)))
      (mul_le_mul_of_nonneg_left herr.2 (by linarith : 0 ≤ LogApprox.constant {2} a B rho))
  have hfinal := sk_error_budget (by linarith : 0 < LogApprox.constant {2} a B rho)
    hCB hu hu1 (errorConstant_ge_one a ha hB hB1)
  simp only [run,if_neg hex]
  apply hcol.trans
  have hh := add_le_add hcolor htail
  apply hh.trans
  calc
    _ = LogApprox.constant {2} a B rho*Real.exp (-budget a B rho u)+
      2*SKBranching.massConstant B (rho^2)*Real.exp (-budget a B rho u)+
      LogApprox.constant {2} a B rho*Real.exp (-4*budget a B rho u)+
      LogApprox.constant {2} a B rho*Real.exp (-budget a B rho u) := by ring
    _ ≤ u := hfinal

end Manuscript.SKAlgorithm
