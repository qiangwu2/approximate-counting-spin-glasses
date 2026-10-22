import Manuscript.SKRuntime
import Manuscript.InputPreparation

/-! Elementary cost absorption for the counted SK control and trials. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKCostBounds

def workFactor (N D L R : ℕ) : ℝ :=
  (R : ℝ)*((N : ℝ)+2*L+2)^6*(16 : ℝ)^L*
    (∑ b ∈ Finset.range (D+1), (N.choose b : ℝ)*(36 : ℝ)^(b+1))

theorem setFactor_ge_one (N D : ℕ) :
    (1 : ℝ) ≤ ∑ b ∈ Finset.range (D+1), (N.choose b : ℝ)*(36 : ℝ)^(b+1) := by
  have hh := Finset.single_le_sum (fun b hb =>
    show 0 ≤ (N.choose b : ℝ)*(36 : ℝ)^(b+1) by positivity)
    (show 0 ∈ Finset.range (D+1) by simp)
  norm_num only [Nat.choose_zero_right,Nat.cast_one,zero_add,pow_one,one_mul] at hh
  linarith

/-- The trial envelope dominates every polynomial preparation and control term. -/
theorem workFactor_dominates (N D L R : ℕ) (hR : 0 < R) :
    1 ≤ workFactor N D L R ∧ (N : ℝ) ≤ workFactor N D L R ∧
      (L : ℝ) ≤ workFactor N D L R ∧ (R : ℝ) ≤ workFactor N D L R ∧
      ((N : ℝ)+1)^4 ≤ workFactor N D L R := by
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hS := setFactor_ge_one N D
  have h16 : (1 : ℝ) ≤ (16 : ℝ)^L := one_le_pow₀ (by norm_num)
  have hZ : (1 : ℝ) ≤ (N : ℝ)+2*L+2 := by
    linarith [Nat.cast_nonneg N (α := ℝ),Nat.cast_nonneg L (α := ℝ)]
  have hZ6 : (1 : ℝ) ≤ ((N : ℝ)+2*L+2)^6 := one_le_pow₀ hZ
  have hf : ((N : ℝ)+2*L+2)^6 ≤ workFactor N D L R := by
    unfold workFactor
    apply (le_mul_of_one_le_left (by positivity) hR1).trans
    apply (le_mul_of_one_le_right (by positivity) h16).trans
    exact le_mul_of_one_le_right (by positivity) hS
  have hzsmall : (N : ℝ)+2*L+2 ≤ ((N : ℝ)+2*L+2)^6 := le_self_pow₀ hZ (by norm_num)
  have hNN : (N : ℝ)+1 ≤ (N : ℝ)+2*L+2 := by linarith [Nat.cast_nonneg L (α := ℝ)]
  have hNpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (N : ℝ)+1) hNN 4
  have h46 : ((N : ℝ)+2*L+2)^4 ≤ ((N : ℝ)+2*L+2)^6 :=
    pow_le_pow_right₀ hZ (by norm_num)
  have hRf : (R : ℝ) ≤ workFactor N D L R := by
    unfold workFactor
    apply (le_mul_of_one_le_right (Nat.cast_nonneg R) hZ6).trans
    apply (le_mul_of_one_le_right (by positivity) h16).trans
    exact le_mul_of_one_le_right (by positivity) hS
  refine ⟨hZ6.trans hf,?_,?_,hRf,(hNpow.trans h46).trans hf⟩
  · exact (by linarith [Nat.cast_nonneg L (α := ℝ)] : (N : ℝ) ≤ (N : ℝ)+2*L+2).trans (hzsmall.trans hf)
  · exact (by linarith [Nat.cast_nonneg L (α := ℝ),Nat.cast_nonneg N (α := ℝ)] : (L : ℝ) ≤ (N : ℝ)+2*L+2).trans (hzsmall.trans hf)

/-- Input preparation, actual cutoff control, random-color generation and trial
work fit one multiple of the declared trial factor. -/
theorem absorb_overhead {N D L R : ℕ} (hR : 0 < R) {prep control trial : ℝ}
    (hp : prep ≤ 96*((N : ℝ)+1)^4)
    (hc : control ≤ 10*(N : ℝ)+2*L+2*R+21)
    (ht : trial ≤ 4096*workFactor N D L R) :
    prep+control+trial ≤ 5000*workFactor N D L R := by
  obtain ⟨h1,hN,hL,hR',hsize⟩ := workFactor_dominates N D L R hR
  linarith

def growth (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  max 0 (max (SKRuntime.trialGrowth a B rho) (Real.log 2/SKRuntime.rate a B rho))

def amplitude (a : ℕ → ℝ) (B rho : ℝ) : ℝ :=
  5000*SKRuntime.trialAmplitude a B rho+
    300*((2 : ℝ)^(Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho))+1)

theorem trialAmplitude_pos (a : ℕ → ℝ) (ha : a 2 = 1) {B rho : ℝ}
    (hB : 0 < B) (hB1 : B < 1) : 0 < SKRuntime.trialAmplitude a B rho := by
  have hq := SKAlgorithm.q_range a ha hB hB1
  have hr : 0 < SKRuntime.rate a B rho := Cutoffs.nu_pos (by norm_num : (0 : ℝ)<1)
    (SKAlgorithm.scale_pos B rho) (SKAlgorithm.c1_pos a ha hB hB1)
  unfold SKRuntime.trialAmplitude SKRuntime.sizeConstant SKRuntime.colorConstant
  positivity [SpinGlass.AlgorithmBudgets.log_inv_pos hq.1 hq.2]

theorem amplitude_pos (a : ℕ → ℝ) (ha : a 2 = 1) {B rho : ℝ}
    (hB : 0 < B) (hB1 : B < 1) : 0 < amplitude a B rho := by
  have ht := trialAmplitude_pos a ha (rho := rho) hB hB1
  unfold amplitude
  positivity

/-- The actual selected trial factor has a fixed envelope including overhead. -/
theorem truncated_envelope (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ) (ha : a 2 = 1)
    {B rho u : ℝ} (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1)
    (hex : ¬ SKAlgorithm.exactBranch N a B rho u) :
    5000*workFactor N (SKAlgorithm.branchCutoff N a B rho u)
      (SKAlgorithm.edgeLimit a B rho u) (SKAlgorithm.trials a B rho u) ≤
      amplitude a B rho*((N : ℝ)+1)^7*
        Real.exp (growth a B rho*SKAlgorithm.budget a B rho u) := by
  have ht := SKRuntime.selected_trial_work N hN a ha hB hB1 hu hu1 hex
  have hLam := (SKAlgorithm.budget_pos a ha (rho := rho) hB hB1 hu hu1).le
  have hg : SKRuntime.trialGrowth a B rho ≤ growth a B rho :=
    (le_max_left _ _).trans (le_max_right _ _)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hg hLam)
  have hA : 5000*SKRuntime.trialAmplitude a B rho ≤ amplitude a B rho := by
    unfold amplitude
    exact le_add_of_nonneg_right (by positivity)
  have hc := trialAmplitude_pos a ha (rho := rho) hB hB1
  have hAmp := amplitude_pos a ha (rho := rho) hB hB1
  calc
    _ ≤ (5000*SKRuntime.trialAmplitude a B rho)*((N : ℝ)+1)^7*
        Real.exp (SKRuntime.trialGrowth a B rho*SKAlgorithm.budget a B rho u) := by
      have hh := mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 5000 by norm_num)
      simpa only [workFactor,mul_assoc] using hh
    _ ≤ _ := by gcongr

/-- Exact enumeration is polynomial in inverse accuracy on the branch where
it is selected, including the bounded-small-system case. -/
theorem exact_envelope (N : ℕ) (a : ℕ → ℝ) (ha : a 2 = 1)
    {B rho u : ℝ} (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1)
    (hex : SKAlgorithm.exactBranch N a B rho u) :
    300*((N : ℝ)+1)^7*(2 : ℝ)^N ≤
      amplitude a B rho*((N : ℝ)+1)^7*
        Real.exp (growth a B rho*SKAlgorithm.budget a B rho u) := by
  have hnu : 0 < SKRuntime.rate a B rho := Cutoffs.nu_pos (by norm_num : (0 : ℝ)<1)
    (SKAlgorithm.scale_pos B rho) (SKAlgorithm.c1_pos a ha hB hB1)
  have hLam := (SKAlgorithm.budget_pos a ha (rho := rho) hB hB1 hu hu1).le
  have hgr : Real.log 2/SKRuntime.rate a B rho ≤ growth a B rho :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hh := HigherOrderCost.exact_cube_bound hnu hLam (le_max_left _ _) hgr hex
  have hA : 300*((2 : ℝ)^(Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho))+1) ≤
      amplitude a B rho := by
    have ht := trialAmplitude_pos a ha (rho := rho) hB hB1
    unfold amplitude
    linarith
  calc
    _ ≤ 300*((N : ℝ)+1)^7*
      (((2 : ℝ)^(Cutoffs.sizeThreshold 2 1 (SKAlgorithm.scale B rho))+1)*
        Real.exp (growth a B rho*SKAlgorithm.budget a B rho u)) := by
          exact mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ _ := by
      have hc := mul_le_mul_of_nonneg_right hA
        (show 0 ≤ ((N : ℝ)+1)^7*Real.exp (growth a B rho*SKAlgorithm.budget a B rho u) by positivity)
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hc

end Manuscript.SKCostBounds
