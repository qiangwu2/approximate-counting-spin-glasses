import Manuscript.SKControl
import Manuscript.HigherOrderCost

/-! Fixed-budget envelopes for the actual SK trial and retained-support factors. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKRuntime
open SpinGlass.AlgorithmBudgets

def sizeConstant (q nu : ℝ) : ℝ := 4+2*nu/Real.log (1/q)
def colorConstant : ℝ := 2*Real.exp (2+Real.log 16)
def colorGrowth (q c : ℝ) : ℝ := 1+(2+Real.log 16)/Real.log (1/q)+c

/-- The exact choice R=ceil(exp(2L+Lambda)) contributes only fixed exponential
budget dependence, including the complete 16^L state-space factor. -/
theorem color_factor {q Lambda c : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hLam : 0 ≤ Lambda) :
    (colorTrials (2*edgeCutoff q Lambda) Lambda : ℝ)*
      (16 : ℝ)^(edgeCutoff q Lambda)*Real.exp (c*Lambda) ≤
        colorConstant*Real.exp (colorGrowth q c*Lambda) := by
  have hL := edgeCutoff_le hq hq1 hLam
  have hR := colorTrials_le (2*edgeCutoff q Lambda) hLam
  have hlog : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hp : (16 : ℝ)^(edgeCutoff q Lambda) =
      Real.exp ((edgeCutoff q Lambda : ℝ)*Real.log 16) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<16)]
  calc
    _ ≤ (2*Real.exp (2*(edgeCutoff q Lambda : ℝ)+Lambda))*
        (16 : ℝ)^(edgeCutoff q Lambda)*Real.exp (c*Lambda) := by
      gcongr
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hR
    _ = 2*Real.exp ((2+Real.log 16)*(edgeCutoff q Lambda : ℝ)+(1+c)*Lambda) := by
      rw [hp]
      simp only [mul_assoc,←Real.exp_add]
      congr 2
      ring
    _ ≤ 2*Real.exp ((2+Real.log 16)*(Lambda/Real.log (1/q)+1)+(1+c)*Lambda) := by gcongr
    _ = _ := by
      unfold colorConstant colorGrowth
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring

theorem size_factor {q Lambda nu : ℝ} {N : ℕ} (hq : 0 < q) (hq1 : q < 1)
    (hLam : 0 ≤ Lambda) (hnu : 0 ≤ nu) (hsmall : Lambda ≤ nu*N) :
    (N : ℝ)+2*edgeCutoff q Lambda+2 ≤ sizeConstant q nu*((N : ℝ)+1) := by
  have hL := edgeCutoff_le hq hq1 hLam
  have hd := log_inv_pos hq hq1
  have hh := div_le_div_of_nonneg_right hsmall hd.le
  have heq : nu*(N : ℝ)/Real.log (1/q) = (nu/Real.log (1/q))*N := by ring
  rw [heq] at hh
  have hn : 0 ≤ nu/Real.log (1/q) := div_nonneg hnu hd.le
  unfold sizeConstant
  rw [show 2*nu/Real.log (1/q) = 2*(nu/Real.log (1/q)) by ring]
  nlinarith [Nat.cast_nonneg N (α := ℝ)]

/-- The complete prospective SK work expression has one fixed budget envelope. -/
theorem trial_work_factor {q Lambda nu c : ℝ} {N D : ℕ}
    (hq : 0 < q) (hq1 : q < 1) (hLam : 0 ≤ Lambda) (hnu : 0 ≤ nu)
    (hsmall : Lambda ≤ nu*N)
    (hsets : (∑ b ∈ Finset.range (D+1), (N.choose b : ℝ)*(36 : ℝ)^b) ≤
      ((N : ℝ)+1)*Real.exp (c*Lambda)) :
    (colorTrials (2*edgeCutoff q Lambda) Lambda : ℝ)*
      ((N : ℝ)+2*edgeCutoff q Lambda+2)^6*(16 : ℝ)^(edgeCutoff q Lambda)*
        (∑ b ∈ Finset.range (D+1), (N.choose b : ℝ)*(36 : ℝ)^(b+1)) ≤
      (36*sizeConstant q nu^6*colorConstant)*((N : ℝ)+1)^7*
        Real.exp (colorGrowth q c*Lambda) := by
  have hs := size_factor (N := N) hq hq1 hLam hnu hsmall
  have hc := color_factor (c := c) hq hq1 hLam
  have hshift : (∑ b ∈ Finset.range (D+1), (N.choose b : ℝ)*(36 : ℝ)^(b+1)) =
      36*(∑ b ∈ Finset.range (D+1), (N.choose b : ℝ)*(36 : ℝ)^b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [pow_succ]
    ring
  have hsize0 : 0 ≤ sizeConstant q nu := by
    unfold sizeConstant
    positivity [log_inv_pos hq hq1]
  rw [hshift]
  calc
    _ ≤ (colorTrials (2*edgeCutoff q Lambda) Lambda : ℝ)*
        ((N : ℝ)+2*edgeCutoff q Lambda+2)^6*(16 : ℝ)^(edgeCutoff q Lambda)*
          (36*(((N : ℝ)+1)*Real.exp (c*Lambda))) := by gcongr
    _ = 36*((N : ℝ)+2*edgeCutoff q Lambda+2)^6*((N : ℝ)+1)*
        ((colorTrials (2*edgeCutoff q Lambda) Lambda : ℝ)*(16 : ℝ)^(edgeCutoff q Lambda)*Real.exp (c*Lambda)) := by ring
    _ ≤ 36*(sizeConstant q nu*((N : ℝ)+1))^6*((N : ℝ)+1)*
        (colorConstant*Real.exp (colorGrowth q c*Lambda)) := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Fixed design parameters in the SK branch. -/
def rate (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  Cutoffs.nu 1 (SKAlgorithm.scale B rho) (SKAlgorithm.c1 a B rho)
def workGrowth (B rho : ℝ) : ℝ := Cutoffs.workConstant 1 (SKAlgorithm.scale B rho) 36

theorem selected_spec (N : ℕ) (a : ℕ → ℝ) (ha : a 2 = 1) {B rho u : ℝ}
    (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1)
    (hex : ¬ SKAlgorithm.exactBranch N a B rho u) :
    1 ≤ SKAlgorithm.selectedSize N a B rho u ∧
      SKAlgorithm.selectedSize N a B rho u ≤ Nat.floor (Cutoffs.gamma 1 (SKAlgorithm.scale B rho)*N) ∧
      (∀ j : ℕ, 1 ≤ j → j < SKAlgorithm.selectedSize N a B rho u →
        SpinGlass.CutoffTail.phi 1 (SKAlgorithm.scale B rho) N j < SKAlgorithm.budget a B rho u) := by
  have hN0 : Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho) ≤ N :=
    Nat.le_of_not_gt (fun hn => hex (Or.inl hn))
  have hsmall : SKAlgorithm.budget a B rho u < rate a B rho*N :=
    lt_of_not_ge (fun hl => hex (Or.inr hl))
  have hNs : 2/Cutoffs.gamma 1 (SKAlgorithm.scale B rho) ≤ (N : ℝ) :=
    (Cutoffs.sizeThreshold_ge_scale _ _ _).trans (by exact_mod_cast hN0)
  obtain ⟨m,hm,hm1,hmrange,hmPhi,hmfirst⟩ := Cutoffs.cutoffScan_correct
    (by norm_num : (0 : ℝ)<1) (le_refl (1 : ℝ)) (SKAlgorithm.scale_pos B rho) hNs
    (SKAlgorithm.budget_pos a ha hB hB1 hu hu1) hsmall
  simpa only [SKAlgorithm.selectedSize,hm,Option.getD_some] using And.intro hm1 (And.intro hmrange hmfirst)

def trialAmplitude (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  36*sizeConstant (SKAlgorithm.q a B) (rate a B rho)^6*colorConstant

def trialGrowth (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  colorGrowth (SKAlgorithm.q a B) (workGrowth B rho)

/-- The actual chosen SK cutoffs discharge every retained-set and accuracy
hypothesis in the work-factor estimate. -/
theorem selected_trial_work (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ) (ha : a 2 = 1)
    {B rho u : ℝ} (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1)
    (hex : ¬ SKAlgorithm.exactBranch N a B rho u) :
    (SKAlgorithm.trials a B rho u : ℝ)*
      ((N : ℝ)+2*SKAlgorithm.edgeLimit a B rho u+2)^6*
      (16 : ℝ)^(SKAlgorithm.edgeLimit a B rho u)*
        (∑ b ∈ Finset.range (SKAlgorithm.branchCutoff N a B rho u+1),
          (N.choose b : ℝ)*(36 : ℝ)^(b+1)) ≤
      trialAmplitude a B rho*((N : ℝ)+1)^7*
        Real.exp (trialGrowth a B rho*SKAlgorithm.budget a B rho u) := by
  obtain ⟨hm1,hmrange,hmfirst⟩ := selected_spec N a ha hB hB1 hu hu1 hex
  have hLam := SKAlgorithm.budget_pos a ha (rho := rho) hB hB1 hu hu1
  have hnu : 0 < rate a B rho := Cutoffs.nu_pos (by norm_num : (0 : ℝ)<1)
    (SKAlgorithm.scale_pos B rho) (SKAlgorithm.c1_pos a ha hB hB1)
  have hsmall : SKAlgorithm.budget a B rho u ≤ rate a B rho*N :=
    (lt_of_not_ge (fun hl => hex (Or.inr hl))).le
  have hsets := Cutoffs.selected_binomial_cost (by norm_num : (0 : ℝ)<1) (le_refl (1 : ℝ))
    (SKAlgorithm.scale_ge_one B rho) (by norm_num : (1 : ℝ) ≤ 36) hN hLam.le hmrange hmfirst
  have hstep : SKAlgorithm.branchCutoff N a B rho u+1 = SKAlgorithm.selectedSize N a B rho u := by
    unfold SKAlgorithm.branchCutoff
    omega
  have hh := trial_work_factor (q := SKAlgorithm.q a B) (nu := rate a B rho)
    (D := SKAlgorithm.branchCutoff N a B rho u) (c := workGrowth B rho)
    (SKAlgorithm.q_range a ha hB hB1).1 (SKAlgorithm.q_range a ha hB hB1).2
    hLam.le hnu.le hsmall (by simpa only [hstep,workGrowth] using hsets)
  exact hh

end Manuscript.SKRuntime
