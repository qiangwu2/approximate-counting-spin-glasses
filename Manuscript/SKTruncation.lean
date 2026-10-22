import Manuscript.SKBranchingTail
import Manuscript.DisorderOrthogonality
import Manuscript.UniformMixedMass

/-! The actual signed weak-field SK truncation and its exact error decomposition. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKBranching
open MeasureTheory SpinGlass.Disorder Manuscript.UniformGraphMass SpinGlass.CutoffTail
variable {V : Type*} [Fintype V] [DecidableEq V]

def truncation (D L : ℕ) (h a : ℝ) (J : Finset V → ℝ) : ℝ :=
  ∑ Γ ∈ (pairGraphs V).filter (SKGraph.Retained id D L),
    DisorderOrthogonality.graphWeight id h (fun _ => a) Γ J

theorem truncation_mse_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (D L : ℕ) (h a : ℝ) :
    (∫ J, (FieldExpansion.normalizedPartition id
      ((Finset.univ : Finset V).powersetCard 2) h (fun e => a * J e) -
      truncation D L h a J) ^ 2 ∂iidLaw μ) =
    graphMass id ((pairGraphs V).filter (fun Γ => ¬SKGraph.Retained id D L Γ)) h
      (fun _ => secondMoment μ a) := by
  simp_rw [FieldExpansion.normalizedPartition_eq_graph_sum]
  exact DisorderOrthogonality.retained_family_error μ hμ id h (fun _ => a)
    (pairGraphs V) (SKGraph.Retained id D L)

theorem joint_omitted_mass_le (D L : ℕ) (h : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    graphMass id ((pairGraphs V).filter (fun Γ => ¬SKGraph.Retained id D L Γ)) h (fun _ => r) ≤
      branchTail (V := V) D h r +
      graphMass id ((pairGraphs V).filter (fun Γ => L + 1 ≤ Γ.card)) h (fun _ => r) := by
  unfold branchTail graphMass
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib, Finset.prod_const, SKGraph.Retained]
  apply Finset.sum_le_sum
  intro Γ hΓ
  have hw : 0 ≤ Real.tanh h ^ (2 * (FieldExpansion.boundary id Γ).card) * r ^ Γ.card :=
    mul_nonneg (fieldFactor_nonneg id Γ h) (pow_nonneg hr _)
  by_cases hD : (SKGraph.branch id Γ).card ≤ D
  · have hDb : ¬D < (SKGraph.branch id Γ).card := by omega
    by_cases hL : Γ.card ≤ L
    · have hLb : ¬L + 1 ≤ Γ.card := by omega
      simp [hD,hDb,hL,hLb]
    · have hLb : L + 1 ≤ Γ.card := by omega
      simp [hD,hDb,hL,hLb]
  · have hDb : D < (SKGraph.branch id Γ).card := by omega
    by_cases hL : L + 1 ≤ Γ.card
    · simp only [hD, false_and, not_false_eq_true, if_true, hDb, hL]
      linarith
    · simp [hD,hDb,hL]

/-- The exact three-term truncation estimate at arbitrary physical scaling,
with the uniform mass supplied by its separately proved finite-model theorem. -/
theorem truncation_mse_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (D L : ℕ) (h a : ℝ)
    {B F z q C alpha Cplus : ℝ}
    (hN : 0 < Fintype.card V) (hB : 0 ≤ B) (hB1 : B < 1) (hF : 0 ≤ F)
    (hNr : (Fintype.card V : ℝ) * secondMoment μ a ≤ B ^ 2)
    (hfield : Real.tanh h ^ 2 * Real.sqrt (Fintype.card V : ℝ) ≤ F)
    (hz : 0 ≤ z) (hq : 0 < q) (hq1 : q ≤ 1) (hrq : secondMoment μ a ≤ q * z)
    (hmass : graphMass id (pairGraphs V) h (fun _ => z) ≤ Cplus)
    (hC : 0 < C) (hBC : branchConstant B F ≤ C) (halpha : 0 < alpha)
    (hgap : 2 ≤ Real.log (1 / (C * alpha)) - 1)
    (hcut : D < Nat.floor (alpha * Fintype.card V)) :
    (∫ J, (FieldExpansion.normalizedPartition id
      ((Finset.univ : Finset V).powersetCard 2) h (fun e => a * J e) -
      truncation D L h a J) ^ 2 ∂iidLaw μ) ≤
      Cplus * q ^ (L + 1) +
      2 * massConstant B F * Real.exp (-phi 1 C (Fintype.card V) (D + 1)) +
      Cplus * q ^ (3 * alpha * Fintype.card V / 2) := by
  rw [truncation_mse_eq μ hμ]
  have hb := branch_truncation_tail hN hB hB1 hF (secondMoment_nonneg μ a) hNr hfield
    hz hq hq1 hrq hmass hC hBC halpha hgap hcut
  have he := finite_geometric_tail id (pairGraphs V) h (fun _ => secondMoment μ a)
    (fun _ => z) (fun _ => secondMoment_nonneg μ a) (fun _ => hz) hq.le hq1
    (fun _ => hrq) (L + 1)
  have he' := he.trans (mul_le_mul_of_nonneg_left hmass (pow_nonneg hq.le (L + 1)))
  have hm := joint_omitted_mass_le (V := V) D L h (secondMoment_nonneg μ a)
  linarith

/-- The stated weak-field scale implies the exact second-power bound needed
by the Gaussian branching estimate, including negative fields. -/
theorem weak_field_squared (N : ℕ) (hN : 0 < N) {h rho : ℝ}
    (hh : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    Real.tanh h ^ 2 * Real.sqrt (N : ℝ) ≤ rho ^ 2 := by
  have h4 := UniformMixedMass.weak_field_fourth N hN hh
  have ht := SpinGlass.TanhBound.tanh_sq_le_sq h
  have ht2 := pow_le_pow_left₀ (sq_nonneg (Real.tanh h)) ht 2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs : (Real.tanh h ^ 2 * Real.sqrt (N : ℝ)) ^ 2 ≤ (rho ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0]
    nlinarith [mul_le_mul_of_nonneg_left ht2 hN0]
  nlinarith [mul_nonneg (sq_nonneg (Real.tanh h)) (Real.sqrt_nonneg (N : ℝ)),sq_nonneg rho]

end Manuscript.SKBranching
