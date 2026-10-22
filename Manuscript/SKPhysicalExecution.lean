import Manuscript.SKGeneratedExecution
import Manuscript.SKGhostPhysicalEvaluation
import Manuscript.SKControl
import Manuscript.HigherOrderExecution

/-! The complete counted SK GraphApprox program on the prepared physical input.
Every selected cutoff is the output of the concrete comparison-loop control. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKPhysicalExecution
open SpinGlass.ArithmeticEvaluation Manuscript.InputPreparation Manuscript.Model
attribute [local instance] Classical.propDecidable

def preparedWeight {N : ℕ} (input : PreparedInput N {2}) (e : Finset (Fin N)) : ℝ :=
  if he : e.card=2 then cachedWeight input ⟨e,Model.mem_physicalEdges.mpr (by simp [he])⟩ else 0

@[simp] theorem preparedWeight_value {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N {2} → ℝ) :
    preparedWeight (prepareInput N {2} a beta h J) = SKGhostCoefficient.inputWeight N a beta J := by
  funext e
  unfold preparedWeight SKGhostCoefficient.inputWeight
  by_cases he : e.card=2
  · simp [he,cachedWeight_value hN]
  · simp [he]

/-- Transport of the saved color tape only changes dependent type proofs. -/
def castColors {N L R L' R' : ℕ} (hL : L'=L) (hR : R'=R)
    (χ : SKColorEstimator.Colors (Fin N) L R) : SKColorEstimator.Colors (Fin N) L' R' :=
  fun A r v => Fin.cast (congrArg (fun k => 2*k) hL.symm) (χ A (Fin.cast hR r) v)

@[simp] theorem castColors_self {N L R : ℕ} (hL : L=L) (hR : R=R)
    (χ : SKColorEstimator.Colors (Fin N) L R) : castColors hL hR χ=χ := by
  funext A r v
  simp [castColors]

theorem estimator_cast {N L R L' R' : ℕ} (hL : L'=L) (hR : R'=R)
    (D : ℕ) (χ : SKColorEstimator.Colors (Fin N) L R) (mean : ℝ) (w : Finset (Fin N) → ℝ) :
    SKGeneratedExecution.estimator D L' R' (castColors hL hR χ) mean w =
      SKGeneratedExecution.estimator D L R χ mean w := by
  subst L'
  subst R'
  simp

/-- Saved control outputs select the exact local-cube branch or the charged
cached colorful evaluator. -/
def evaluate (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ)
    (χ : SKAlgorithm.Colors N a B rho u) (input : PreparedInput N {2}) : Computation :=
  let ctl := SKControl.control N a B rho u
  if hc : ctl.exact=true then
    SupportExecution.supportSum Subtype.val Finset.univ (cachedFieldWeight input) (cachedWeight input) N
  else
    have hex : ¬SKAlgorithm.exactBranch N a B rho u := by
      intro he
      have hh := SKControl.control_exact N a B rho u he
      exact hc (congrArg SKControl.Control.exact hh)
    have hh := SKControl.control_truncated N a B rho u hex
    SKGeneratedExecution.estimator ctl.branchLimit ctl.edgeLimit ctl.trials
      (castColors hh.2.2.1 hh.2.2.2 χ) input.field.mean (preparedWeight input)

/-- Input coefficients, field weights and elementary functions are shared by
both branches. The counter also includes all finite cutoff computation. -/
def execute (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) : Computation :=
  let input := prepareInput N {2} a beta h J
  let result := evaluate N a B rho u χ input
  ⟨result.value,input.operations+(SKControl.control N a B rho u).operations+result.operations+1⟩

theorem evaluate_exact (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ)
    (hex : SKAlgorithm.exactBranch N a B rho u)
    (χ : SKAlgorithm.Colors N a B rho u) (input : PreparedInput N {2}) :
    evaluate N a B rho u χ input = SupportExecution.supportSum Subtype.val Finset.univ
      (cachedFieldWeight input) (cachedWeight input) N := by
  simp [evaluate,SKControl.control_exact N a B rho u hex]

theorem evaluate_truncated (N : ℕ) (a : ℕ → ℝ) (B rho u : ℝ)
    (hex : ¬SKAlgorithm.exactBranch N a B rho u)
    (χ : SKAlgorithm.Colors N a B rho u) (input : PreparedInput N {2}) :
    evaluate N a B rho u χ input = SKGeneratedExecution.estimator
      (SKAlgorithm.branchCutoff N a B rho u) (SKAlgorithm.edgeLimit a B rho u)
      (SKAlgorithm.trials a B rho u) χ input.field.mean (preparedWeight input) := by
  have hh := SKControl.control_truncated N a B rho u hex
  simp only [evaluate,hh.1,Bool.false_eq_true,↓reduceDIte]
  simp only [hh.2.1]
  exact estimator_cast hh.2.2.1 hh.2.2.2 _ χ _ _

@[simp] theorem execute_value {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ) (ha : a 2=1)
    {B rho beta h u : ℝ} (hB : 0 < B) (hB1 : B < 1) (hu : 0 < u) (hu1 : u < 1)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    (execute N a B rho beta h u χ J).value = SKAlgorithm.run N a B rho beta h u χ J := by
  by_cases hex : SKAlgorithm.exactBranch N a B rho u
  · simp only [execute,evaluate_exact N a B rho u hex,
      HigherOrderExecution.cached_evaluator_eq hN,SKAlgorithm.run,if_pos hex]
  · simp only [execute,evaluate_truncated N a B rho u hex,preparedWeight_value hN]
    change (SKGeneratedExecution.estimator _ _ _ χ (Real.tanh h)
      (SKGhostCoefficient.inputWeight N a beta J)).value = _
    rw [SKGeneratedExecution.estimator_value,SKGhostCoefficient.algorithm_eq_physical
      N _ _ _ (SKAlgorithm.edgeLimit_pos a ha hB hB1 hu hu1)]
    simp only [SKAlgorithm.run,if_neg hex]

/-- Exact-branch cost, including the full prepared input and cutoff tests. -/
theorem execute_exact_operations {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (B rho beta h u : ℝ) (hex : SKAlgorithm.exactBranch N a B rho u)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    (execute N a B rho beta h u χ J).operations =
      (prepareInput N {2} a beta h J).operations+7+
        (HigherOrderTail.evaluator N {2} a beta h N J).operations := by
  simp only [execute,evaluate_exact N a B rho u hex,HigherOrderExecution.cached_evaluator_eq hN,
    SKControl.control_exact N a B rho u hex]
  omega

/-- Truncated-branch cost without an evaluator- or runtime-bound premise. -/
theorem execute_truncated_operations (N : ℕ) (a : ℕ → ℝ) (B rho beta h u : ℝ)
    (hex : ¬SKAlgorithm.exactBranch N a B rho u)
    (χ : SKAlgorithm.Colors N a B rho u) (J : Edge N {2} → ℝ) :
    (execute N a B rho beta h u χ J).operations ≤
      (prepareInput N {2} a beta h J).operations+
        10*N+2*SKAlgorithm.edgeLimit a B rho u+2*SKAlgorithm.trials a B rho u+21+
        4096*SKAlgorithm.trials a B rho u*(N+2*SKAlgorithm.edgeLimit a B rho u+2)^6*
          16^SKAlgorithm.edgeLimit a B rho u*
          (∑ b∈Finset.range (SKAlgorithm.branchCutoff N a B rho u+1),N.choose b*36^(b+1)) := by
  have hc := SKControl.control_operations N a B rho u
  have he := SKGeneratedExecution.estimator_operations (SKAlgorithm.branchCutoff N a B rho u)
    (SKAlgorithm.edgeLimit a B rho u) (SKAlgorithm.trials a B rho u)
    (SKAlgorithm.trials_pos a B rho u) χ (prepareInput N {2} a beta h J).field.mean
    (preparedWeight (prepareInput N {2} a beta h J))
  simp only [Fintype.card_fin] at he
  simp only [execute,evaluate_truncated N a B rho u hex]
  omega

end Manuscript.SKPhysicalExecution
