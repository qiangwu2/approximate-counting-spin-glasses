import Manuscript.SKPhysicalExecution
import Manuscript.SKCostBounds

/-! Uniform cost bound for the fully counted SK implementation. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKExecutionCost
open Manuscript.Model Manuscript.InputPreparation Manuscript.SKCostBounds

 theorem preparation_bound {N : ℕ} (hN : 2 ≤ N) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N {2} → ℝ) :
    ((prepareInput N {2} a beta h J).operations : ℝ) ≤ 96*((N : ℝ)+1)^4 := by
  have hp := prepareInput_polynomial (by omega : 0<N) {2}
    (by simp : ∀ p∈({2}:Finset ℕ),p≤2) (by simpa using hN) a beta h J
  norm_num only [Finset.card_singleton] at hp
  exact_mod_cast hp

 theorem exact_raw {N : ℕ} (hN : 2 ≤ N) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (hex : SKAlgorithm.exactBranch N a B rho u)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    ((SKPhysicalExecution.execute N a B rho beta h u χ J).operations : ℝ) ≤
      300*((N : ℝ)+1)^7*(2 : ℝ)^N := by
  have hp := preparation_bound hN a beta h J
  have he := SKPhysicalExecution.execute_exact_operations (by omega : 0<N) a B rho beta h u hex χ J
  have hl := SupportExecution.local_cost (Subtype.val : Edge N {2} → Finset (Fin N)) Finset.univ
    (FieldExpansion.spinWeight h) (fun e => SpinGlass.Disorder.weight
      (DisorderOrthogonality.physicalScale N {2} a beta e) (J e)) Finset.univ
  have hc := HigherOrderCost.layerConstant_physical (by omega : 0<N) {2}
    (by simp : ∀ p∈({2}:Finset ℕ),p≤2)
  have hc' : SupportExecution.localConstant N (Fintype.card (Edge N {2})) ≤
      SupportExecution.layerConstant N (Fintype.card (Edge N {2})) := by
    unfold SupportExecution.localConstant SupportExecution.layerConstant
    nlinarith
  simp only [Finset.card_univ,Fintype.card_fin] at hl
  have hl' : (HigherOrderTail.evaluator N {2} a beta h N J).operations ≤
      120*(N+1)^4*2^N := by
    unfold HigherOrderTail.evaluator SupportExecution.supportSum
    rw [if_neg (by simp)]
    have ht := hl.trans (Nat.mul_le_mul_right _ hc')
    apply ht.trans
    apply Nat.mul_le_mul_right
    simpa only [Finset.card_singleton] using hc
  have hlR : ((HigherOrderTail.evaluator N {2} a beta h N J).operations : ℝ) ≤
      120*((N : ℝ)+1)^4*(2 : ℝ)^N := by exact_mod_cast hl'
  have hNs : (1 : ℝ) ≤ (N : ℝ)+1 := by linarith [Nat.cast_nonneg N (α := ℝ)]
  have h47 : ((N : ℝ)+1)^4 ≤ ((N : ℝ)+1)^7 := pow_le_pow_right₀ hNs (by norm_num)
  have h7 : (1 : ℝ) ≤ ((N : ℝ)+1)^7 := one_le_pow₀ hNs
  have h2 : (1 : ℝ) ≤ (2 : ℝ)^N := one_le_pow₀ (by norm_num)
  have heR : ((SKPhysicalExecution.execute N a B rho beta h u χ J).operations : ℝ) =
      (prepareInput N {2} a beta h J).operations+7+
        (HigherOrderTail.evaluator N {2} a beta h N J).operations := by exact_mod_cast he
  have h47' := mul_le_mul_of_nonneg_right h47 (show 0 ≤ (2 : ℝ)^N by positivity)
  have h7' := le_mul_of_one_le_right (show 0≤((N : ℝ)+1)^7 by positivity) h2
  nlinarith

 theorem truncated_raw {N : ℕ} (hN : 2 ≤ N) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (hex : ¬SKAlgorithm.exactBranch N a B rho u)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    ((SKPhysicalExecution.execute N a B rho beta h u χ J).operations : ℝ) ≤
      5000*workFactor N (SKAlgorithm.branchCutoff N a B rho u)
        (SKAlgorithm.edgeLimit a B rho u) (SKAlgorithm.trials a B rho u) := by
  have hp := preparation_bound hN a beta h J
  have ht := SKPhysicalExecution.execute_truncated_operations N a B rho beta h u hex χ J
  have htR : ((SKPhysicalExecution.execute N a B rho beta h u χ J).operations : ℝ) ≤
      (prepareInput N {2} a beta h J).operations+
        (10*(N : ℝ)+2*SKAlgorithm.edgeLimit a B rho u+2*SKAlgorithm.trials a B rho u+21)+
        4096*workFactor N (SKAlgorithm.branchCutoff N a B rho u)
          (SKAlgorithm.edgeLimit a B rho u) (SKAlgorithm.trials a B rho u) := by
    have hh := Nat.cast_le (α := ℝ).mpr ht
    push_cast at hh
    simpa only [workFactor,mul_assoc,add_assoc] using hh
  exact htR.trans (absorb_overhead (SKAlgorithm.trials_pos a B rho u) hp le_rfl le_rfl)

 theorem execute_envelope (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℝ) (ha : a 2=1)
    {B rho beta h u : ℝ} (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    ((SKPhysicalExecution.execute N a B rho beta h u χ J).operations : ℝ) ≤
      amplitude a B rho*((N : ℝ)+1)^7*Real.exp (growth a B rho*SKAlgorithm.budget a B rho u) := by
  by_cases hex : SKAlgorithm.exactBranch N a B rho u
  · exact (exact_raw hN a B rho beta h u hex χ J).trans
      (exact_envelope N a ha hB hB1 hu hu1 hex)
  · exact (truncated_raw hN a B rho beta h u hex χ J).trans
      (truncated_envelope N (by omega) a ha hB hB1 hu hu1 hex)

 theorem execute_polynomial (a : ℕ → ℝ) (ha : a 2=1)
    {B rho : ℝ} (hB : 0 < B) (hB1 : B < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ (beta h u : ℝ), 0 < u → u < 1 →
      ∀ (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ),
      ((SKPhysicalExecution.execute N a B rho beta h u χ J).operations : ℝ) ≤ C*(N : ℝ)^C*u^(-C) := by
  let C := SpinGlass.PolynomialRuntime.envelopeConstant (amplitude a B rho)
    (SKAlgorithm.errorConstant a B rho) (growth a B rho) 7
  refine ⟨C,SpinGlass.PolynomialRuntime.envelopeConstant_pos _ _ _ _,?_⟩
  intro N hN beta h u hu hu1 χ J
  apply (execute_envelope N hN a ha hB hB1 hu hu1 χ J).trans
  have hC := SKAlgorithm.errorConstant_ge_one a ha (rho := rho) hB hB1
  exact SpinGlass.PolynomialRuntime.envelope_le_polynomial
    (amplitude_pos a ha hB hB1).le (by linarith) (by omega) hu hu1.le

end Manuscript.SKExecutionCost
