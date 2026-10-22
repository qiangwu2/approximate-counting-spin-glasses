import Manuscript.SKBranchingBound
import Manuscript.UniformGraphMass

/-! The exact branching split and its weak-field small and extensive tails. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKBranching
open SpinGlass.CutoffTail Manuscript.UniformGraphMass
variable {V : Type*} [Fintype V] [DecidableEq V]

def branchMass (b : ℕ) (h r : ℝ) : ℝ :=
  graphMass id (branchCardFamily (V := V) b) h (fun _ => r)

def branchTail (D : ℕ) (h r : ℝ) : ℝ :=
  graphMass id ((pairGraphs V).filter (fun Γ => D < (SKGraph.branch id Γ).card)) h (fun _ => r)

theorem branchMass_eq (b : ℕ) (h r : ℝ) :
    branchMass (V := V) b h r = ∑ Γ ∈ branchCardFamily (V := V) b,
      (Real.tanh h ^ 2) ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card := by
  simp [branchMass, graphMass, pow_mul]

theorem branchTail_split (D K : ℕ) (hDK : D ≤ K) (h r : ℝ) :
    branchTail (V := V) D h r =
      (∑ b ∈ Finset.Ico (D + 1) (K + 1), branchMass (V := V) b h r) +
        branchTail (V := V) K h r := by
  have hf := Finset.sum_fiberwise_eq_sum_filter (pairGraphs V)
    (Finset.Ico (D + 1) (K + 1)) (fun Γ => (SKGraph.branch id Γ).card)
    (fun Γ => Real.tanh h ^ (2 * (FieldExpansion.boundary id Γ).card) * r ^ Γ.card)
  simp only [branchMass, graphMass, Finset.prod_const, branchCardFamily] at *
  rw [hf]
  unfold branchTail graphMass
  simp only [Finset.prod_const, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  simp only [Finset.mem_Ico]
  by_cases hD : D < (SKGraph.branch id Γ).card
  · by_cases hK : K < (SKGraph.branch id Γ).card
    · have hn : ¬(D + 1 ≤ (SKGraph.branch id Γ).card ∧
          (SKGraph.branch id Γ).card < K + 1) := by omega
      simp [hD, hK, hn]
    · have hh : D + 1 ≤ (SKGraph.branch id Γ).card ∧
          (SKGraph.branch id Γ).card < K + 1 := by omega
      simp [hD, hK, hh]
  · have hK : ¬K < (SKGraph.branch id Γ).card := by omega
    have hn : ¬(D + 1 ≤ (SKGraph.branch id Γ).card ∧
          (SKGraph.branch id Γ).card < K + 1) := by omega
    simp [hD, hK, hn]

theorem branchConstant_nonneg {B F : ℝ} (hB : 0 ≤ B) (hF : 0 ≤ F) :
    0 ≤ branchConstant B F := by
  have := degreeConstant_nonneg hB hF
  unfold branchConstant
  positivity

theorem massConstant_nonneg {B F : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) : 0 ≤ massConstant B F := by
  have := eta_pos hB hB1
  unfold massConstant
  positivity

theorem branch_power_le_exp {N b : ℕ} (hN : 0 < N) (hb : 0 < b)
    {B F C : ℝ} (hB : 0 ≤ B) (hF : 0 ≤ F) (hC : 0 < C)
    (hBC : branchConstant B F ≤ C) :
    (branchConstant B F * b / N)^b ≤ Real.exp (-phi 1 C N b) := by
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hbR : 0 < (b:ℝ) := Nat.cast_pos.mpr hb
  have hab : 0 < C*b/(N:ℝ) := by positivity
  have heq : (C*b/(N:ℝ))^b = Real.exp (-phi 1 C N b) := by
    rw [← Real.exp_log (pow_pos hab _), Real.log_pow]
    have hlog : Real.log ((N:ℝ)/(C*b)) = -Real.log (C*b/(N:ℝ)) := by
      rw [Real.log_div hNR.ne' (mul_pos hC hbR).ne',
        Real.log_div (mul_pos hC hbR).ne' hNR.ne']
      ring
    congr 1
    simp only [phi, one_mul, hlog]
    ring
  rw [← heq]
  apply pow_le_pow_left₀
    (div_nonneg (mul_nonneg (branchConstant_nonneg hB hF) hbR.le) hNR.le)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hbR.le) hNR.le

theorem small_branch_tail {B F h r C alpha : ℝ} {D : ℕ}
    (hN : 0 < Fintype.card V) (hB : 0 ≤ B) (hB1 : B < 1) (hF : 0 ≤ F) (hr : 0 ≤ r)
    (hNr : (Fintype.card V : ℝ) * r ≤ B ^ 2)
    (hfield : Real.tanh h ^ 2 * Real.sqrt (Fintype.card V : ℝ) ≤ F)
    (hC : 0 < C) (hBC : branchConstant B F ≤ C) (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (C * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * Fintype.card V)) :
    (∑ b ∈ Finset.Ico (D + 1) (Nat.floor (alpha * Fintype.card V) + 1),
      branchMass (V := V) b h r) ≤
      2 * massConstant B F * Real.exp (-phi 1 C (Fintype.card V) (D + 1)) := by
  have hfloor : (Nat.floor (alpha * Fintype.card V) : ℝ) ≤ alpha * Fintype.card V :=
    Nat.floor_le (by positivity)
  calc
    _ ≤ ∑ b ∈ Finset.Ico (D + 1) (Nat.floor (alpha * Fintype.card V) + 1),
        massConstant B F * Real.exp (-phi 1 C (Fintype.card V) b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hbpos : 0 < b := by have := (Finset.mem_Ico.mp hb).1; omega
      rw [branchMass_eq]
      apply (branchCard_mass_bound b hbpos hN hB hB1 hF (sq_nonneg _) hr hNr hfield).trans
      exact mul_le_mul_of_nonneg_left (branch_power_le_exp hN hbpos hB hF hC hBC)
        (massConstant_nonneg (F := F) hB hB1)
    _ = massConstant B F *
        (∑ b ∈ Finset.Ico (D + 1) (Nat.floor (alpha * Fintype.card V) + 1),
          Real.exp (-phi 1 C (Fintype.card V) b)) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      have ht := phi_tail (by norm_num : (0 : ℝ) ≤ 1) hC
        (Nat.cast_pos.mpr hN) halpha (by simpa using hgap)
        (m := D + 1) (by omega) hfloor
      have hc := mul_le_mul_of_nonneg_left ht (massConstant_nonneg (F := F) hB hB1)
      simpa only [Nat.cast_add, Nat.cast_one, ← mul_assoc, mul_comm _ (2 : ℝ)] using hc

/-- Three incidences per branching vertex give the manuscript's `3 alpha N / 2`
edge cutoff. This is distinct from the zero-field degree-four estimate. -/
theorem large_branch_family_subset {alpha : ℝ} (halpha : 0 ≤ alpha) :
    (pairGraphs V).filter (fun Γ => Nat.floor (alpha * Fintype.card V) <
      (SKGraph.branch id Γ).card) ⊆
    (pairGraphs V).filter (fun Γ => 3 * alpha * Fintype.card V / 2 < (Γ.card : ℝ)) := by
  intro Γ hΓ
  obtain ⟨hG, hb⟩ := Finset.mem_filter.mp hΓ
  have hbranch : alpha * (Fintype.card V : ℝ) < (SKGraph.branch id Γ).card :=
    (Nat.floor_lt (by positivity)).mp hb
  have hsimple : ∀ e ∈ Γ, e.card = 2 := by
    intro e he
    exact (Finset.mem_powersetCard.mp ((Finset.mem_powerset.mp hG) he)).2
  have hd := SKGraph.three_branch_le_twice_edges id Γ hsimple
  have hdR : (3 : ℝ) * (SKGraph.branch id Γ).card ≤ 2 * Γ.card := by exact_mod_cast hd
  exact Finset.mem_filter.mpr ⟨hG, by nlinarith⟩

/-- A reusable finite-family comparison; the physical mass bound is discharged
in the physical specialization, not postulated as an analytic axiom. -/
theorem large_branch_tail {h r z q alpha Cplus : ℝ}
    (hr : 0 ≤ r) (hz : 0 ≤ z) (hq : 0 < q) (hq1 : q ≤ 1)
    (hrq : r ≤ q * z) (halpha : 0 ≤ alpha)
    (hmass : graphMass id (pairGraphs V) h (fun _ => z) ≤ Cplus) :
    branchTail (V := V) (Nat.floor (alpha * Fintype.card V)) h r ≤
      Cplus * q ^ (3 * alpha * Fintype.card V / 2) := by
  have hsub := large_branch_family_subset (V := V) halpha
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun Γ _ _ => mul_nonneg (fieldFactor_nonneg id Γ h) (pow_nonneg hr Γ.card))
  have ht := finite_geometric_tail_real id (pairGraphs V) h
    (fun _ => r) (fun _ => z) (fun _ => hr) (fun _ => hz) hq hq1
    (fun _ => hrq) (t := 3 * alpha * Fintype.card V / 2) (by positivity) hmass
  unfold branchTail graphMass
  simp only [Finset.prod_const]
  apply hsum.trans
  simpa only [graphMass, Finset.prod_const] using ht.1.trans ht.2

theorem branch_truncation_tail {B F h r z q C alpha Cplus : ℝ} {D : ℕ}
    (hN : 0 < Fintype.card V) (hB : 0 ≤ B) (hB1 : B < 1) (hF : 0 ≤ F) (hr : 0 ≤ r)
    (hNr : (Fintype.card V : ℝ) * r ≤ B ^ 2)
    (hfield : Real.tanh h ^ 2 * Real.sqrt (Fintype.card V : ℝ) ≤ F)
    (hz : 0 ≤ z) (hq : 0 < q) (hq1 : q ≤ 1) (hrq : r ≤ q * z)
    (hmass : graphMass id (pairGraphs V) h (fun _ => z) ≤ Cplus)
    (hC : 0 < C) (hBC : branchConstant B F ≤ C) (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (C * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * Fintype.card V)) :
    branchTail (V := V) D h r ≤
      2 * massConstant B F * Real.exp (-phi 1 C (Fintype.card V) (D + 1)) +
        Cplus * q ^ (3 * alpha * Fintype.card V / 2) := by
  rw [branchTail_split D _ hcut.le h r]
  exact add_le_add (small_branch_tail hN hB hB1 hF hr hNr hfield hC hBC halpha hgap hcut)
    (large_branch_tail hr hz hq hq1 hrq halpha.le hmass)

end Manuscript.SKBranching
