import Manuscript.HigherOrderCost
import Manuscript.CutoffExecution

/-! Fully counted cached execution of deterministic GraphApprox. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.HigherOrderExecution
open SpinGlass.ArithmeticEvaluation Manuscript.InputPreparation
open Manuscript.HigherOrderAlgorithm Manuscript.HigherOrderTail Manuscript.HigherOrderCost
open Manuscript.Model Manuscript.MixedThreshold Manuscript.SupportExponent

/-- Absolute value uses one sign comparison and, when needed, a negation. -/
def absolute (x : ℝ) : Computation := if x < 0 then ⟨-x,2⟩ else ⟨x,1⟩
@[simp] theorem absolute_value (x : ℝ) : (absolute x).value = |x| := by
  unfold absolute
  split_ifs with hx
  · exact (abs_of_neg hx).symm
  · exact (abs_of_nonneg (le_of_not_gt hx)).symm

theorem absolute_operations (x : ℝ) : (absolute x).operations ≤ 2 := by
  unfold absolute
  split_ifs <;> simp

def minimum (x : ℝ) (y : Computation) : Computation := ⟨min x y.value,y.operations+1⟩

/-- Equation (25) is computed from the cached field mean. The quantities
involving only fixed model parameters are reusable design constants. -/
def kappaComputation (N : ℕ) (rho p h mean : ℝ) : Computation :=
  if h = 0 then ⟨(p-2)/p,1⟩ else
    let b := absolute mean
    let l := logarithm (divide (literal rho) b)
    let q := divide (mul (literal 2) l) (logarithm (literal N))
    let r := minimum ((p-2)/p) (add q (literal (-(1/p))))
    ⟨r.value,r.operations+1⟩

@[simp] theorem kappaComputation_value (N : ℕ) (rho p h : ℝ) (hp : 0 < p) :
    (kappaComputation N rho p h (Real.tanh h)).value =
      HigherFieldExponent.selectedKappa N rho p h := by
  rw [HigherFieldExponent.selectedKappa_eq N rho hp]
  unfold kappaComputation
  split_ifs <;> simp [minimum,add,divide,mul,logarithm,literal,sub_eq_add_neg]

theorem kappaComputation_operations (N : ℕ) (rho p h mean : ℝ) :
    (kappaComputation N rho p h mean).operations ≤ 10 := by
  unfold kappaComputation
  split_ifs
  · norm_num
  · have ha := absolute_operations mean
    simp only [minimum,add,divide,mul,logarithm,literal]
    omega

structure Control where
  cutoff : ℕ
  operations : ℕ

def control (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin h u mean : ℝ) : Control :=
  let lam := logarithm (divide (literal (errorConstant P a B rho)) (literal u))
  if N < Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin) ∨
      Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax)*N ≤ lam.value then
    ⟨N,lam.operations+4⟩
  else
    let kap := kappaComputation N (max 1 rho) pmin h mean
    let scan := CutoffExecution.cutoffSearch (kappaMin pmin) kap.value
      (scale P a B rho pmin) N lam.value
    ⟨scan.found.getD 1-1,lam.operations+kap.operations+scan.operations+7⟩

@[simp] theorem control_cutoff (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin h u : ℝ) (hp : 0 < pmin) :
    (control N pmax P a B rho pmin h u (Real.tanh h)).cutoff =
      selectedCutoff N pmax P a B rho pmin h u := by
  classical
  simp only [control,logarithm,divide,literal]
  by_cases hex : exactBranch N pmax P a B rho pmin u
  · have hc : N < Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin) ∨
        Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax)*N ≤
          Real.log (errorConstant P a B rho/u) := hex
    simp only [if_pos hc]
    simp [selectedCutoff,hex]
  · have hc : ¬(N < Cutoffs.sizeThreshold pmax (kappaMin pmin) (scale P a B rho pmin) ∨
        Cutoffs.nu (kappaMin pmin) (scale P a B rho pmin) (c1 P a B rho pmin pmax)*N ≤
          Real.log (errorConstant P a B rho/u)) := hex
    simp only [if_neg hc]
    simp [selectedCutoff,hex,kappaComputation_value N (max 1 rho) pmin h hp,
      CutoffExecution.cutoffSearch_found _ _ _ _ _ (scale_pos P a B rho pmin),selectedSize,budget,SpinGlass.AlgorithmBudgets.logBudget]

theorem control_operations (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin h u mean : ℝ) :
    (control N pmax P a B rho pmin h u mean).operations ≤ 12*N+30 := by
  dsimp only [control,logarithm,divide,literal]
  split_ifs
  · norm_num [logarithm,divide,literal]
  · have hk := kappaComputation_operations N (max 1 rho) pmin h mean
    have hs := CutoffExecution.cutoffSearch_operations
      (kapMin := kappaMin pmin) (kap := (kappaComputation N (max 1 rho) pmin h mean).value)
      (Lambda := Real.log (errorConstant P a B rho/u)) (N := N)
      (scale_pos P a B rho pmin)
    simp only [logarithm,divide,literal]
    omega

/-- Preparation fills the cached interaction array once. Both field weights
and all interaction weights are then read by the counted support evaluator. -/
def execute (N pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin beta h u : ℝ)
    (J : Edge N P → ℝ) : Computation :=
  let input := prepareInput N P a beta h J
  let ctl := control N pmax P a B rho pmin h u input.field.mean
  let result := SupportExecution.supportSum Subtype.val Finset.univ
    (cachedFieldWeight input) (cachedWeight input) ctl.cutoff
  ⟨result.value,input.operations+ctl.operations+result.operations⟩

theorem cached_evaluator_eq {N : ℕ} (hN : 0 < N) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N P → ℝ) (k : ℕ) :
    SupportExecution.supportSum Subtype.val Finset.univ
      (cachedFieldWeight (prepareInput N P a beta h J))
      (cachedWeight (prepareInput N P a beta h J)) k = evaluator N P a beta h k J := by
  have hb : cachedFieldWeight (prepareInput N P a beta h J) = FieldExpansion.spinWeight h := by
    funext b
    exact cachedFieldWeight_value N P a beta h J b
  have hw : cachedWeight (prepareInput N P a beta h J) =
      fun e => SpinGlass.Disorder.weight (DisorderOrthogonality.physicalScale N P a beta e) (J e) := by
    funext e
    rw [cachedWeight_value hN]
    rw [DisorderOrthogonality.coefficient_eq_physicalScale]
    rfl
  rw [hb,hw]
  rfl

@[simp] theorem execute_value {N : ℕ} (hN : 0 < N) (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h u : ℝ) (hp : 0 < pmin) (J : Edge N P → ℝ) :
    (execute N pmax P a B rho pmin beta h u J).value =
      (run N pmax P a B rho pmin beta h u J).value := by
  simp only [execute,cached_evaluator_eq hN]
  change (evaluator N P a beta h (control N pmax P a B rho pmin h u (Real.tanh h)).cutoff J).value = _
  rw [control_cutoff N pmax P a B rho pmin h u hp]
  rfl

theorem execute_operations {N : ℕ} (hN : 0 < N) (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (B rho pmin beta h u : ℝ) (hp : 0 < pmin) (J : Edge N P → ℝ) :
    (execute N pmax P a B rho pmin beta h u J).operations ≤
      (prepareInput N P a beta h J).operations+12*N+30+
        (run N pmax P a B rho pmin beta h u J).operations := by
  have hc := control_operations N pmax P a B rho pmin h u (Real.tanh h)
  dsimp only [execute]
  rw [cached_evaluator_eq hN]
  change (prepareInput N P a beta h J).operations+
    (control N pmax P a B rho pmin h u (Real.tanh h)).operations+
      (evaluator N P a beta h (control N pmax P a B rho pmin h u (Real.tanh h)).cutoff J).operations ≤ _
  rw [control_cutoff N pmax P a B rho pmin h u hp]
  change _ ≤ _+12*N+30+(evaluator N P a beta h (selectedCutoff N pmax P a B rho pmin h u) J).operations
  omega

def executionAmplitude (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) : ℝ :=
  amplitude pmax P a B rho pmin + 100*(P.card+1)

theorem execute_envelope (N : ℕ) (hN : 0 < N) (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p)
    (pmin : ℝ) (hpmin : 3 ≤ pmin) (horders : ∀ p ∈ P, pmin ≤ (p : ℝ))
    (pmax : ℕ) (hmax : ∀ p ∈ P, p ≤ pmax) (hpN : ∀ p ∈ P, p ≤ N)
    {B rho beta h u : ℝ} (hB : 0 < B) (hBT : B < betaF P a)
    (hfield : |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ))) (hu : 0 < u) (hu1 : u < 1)
    (J : Edge N P → ℝ) :
    ((execute N pmax P a B rho pmin beta h u J).operations : ℝ) ≤
      executionAmplitude pmax P a B rho pmin * ((N : ℝ)+1)^(pmax+3)*
        Real.exp (growth pmax P a B rho pmin*budget P a B rho u) := by
  have hr := run_envelope (beta := beta) N hN P a hP ha pmin hpmin horders pmax hmax hB hBT hfield hu hu1 J
  have hp := prepareInput_polynomial hN P hmax hpN a beta h J
  have he := execute_operations hN pmax P a B rho pmin beta h u (by linarith) J
  have hprep : ((prepareInput N P a beta h J).operations : ℝ) ≤
      48*(P.card+1)*((N : ℝ)+1)^(pmax+2) := by exact_mod_cast hp
  have hop : ((execute N pmax P a B rho pmin beta h u J).operations : ℝ) ≤
      (prepareInput N P a beta h J).operations+12*(N : ℝ)+30+
        (run N pmax P a B rho pmin beta h u J).operations := by exact_mod_cast he
  have hNs : (1 : ℝ) ≤ (N : ℝ)+1 := by linarith [Nat.cast_nonneg N (α := ℝ)]
  have hpow : ((N : ℝ)+1)^(pmax+2) ≤ ((N : ℝ)+1)^(pmax+3) := pow_le_pow_right₀ hNs (by omega)
  have hNp : (N : ℝ)+1 ≤ ((N : ℝ)+1)^(pmax+3) := le_self_pow₀ hNs (by omega)
  have hPc : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hpoly : (prepareInput N P a beta h J).operations+12*(N : ℝ)+30 ≤
      100*(P.card+1)*((N : ℝ)+1)^(pmax+3) := by
    have hh := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 48*((P.card : ℝ)+1) by positivity)
    have hh2 : 1 ≤ ((N : ℝ)+1)^(pmax+3) := one_le_pow₀ hNs
    nlinarith [mul_nonneg hPc (pow_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)+1) (pmax+3))]
  have hpord : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have hh := hpmin.trans (horders p hp)
    have h3 : 3 ≤ p := by exact_mod_cast hh
    omega
  have hC := UniformMixedMass.massConstant_ge_one (rho := rho) P a hP ha hpord
    (betaPlus_sq_range P a hP ha hpord hB hBT).1.le (betaPlus_sq_range P a hP ha hpord hB hBT).2
  have hLam : 0 ≤ budget P a B rho u :=
    (SpinGlass.AlgorithmBudgets.logBudget_pos (by unfold errorConstant; linarith) hu hu1).le
  have hg : 0 ≤ growth pmax P a B rho pmin := le_max_left _ _
  have hexp : 1 ≤ Real.exp (growth pmax P a B rho pmin*budget P a B rho u) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hg hLam)
  have hpolye := le_mul_of_one_le_right
    (show 0 ≤ 100*(P.card+1)*((N : ℝ)+1)^(pmax+3) by positivity) hexp
  unfold executionAmplitude
  nlinarith

/-- Uniform polynomial cost on every finite input, with no randomness and no
analytic or execution-cost conclusion among the hypotheses. -/
theorem execute_polynomial (P : Finset ℕ) (a : ℕ → ℝ)
    (hP : P.Nonempty) (ha : ∀ p ∈ P, 0 < a p)
    (pmin : ℝ) (hpmin : 3 ≤ pmin) (horders : ∀ p ∈ P, pmin ≤ (p : ℝ))
    (pmax : ℕ) (hmax : ∀ p ∈ P, p ≤ pmax)
    {B rho : ℝ} (hB : 0 < B) (hBT : B < betaF P a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → (∀ p ∈ P, p ≤ N) →
      ∀ (beta h u : ℝ), |h| ≤ rho*(N : ℝ)^(-(1/4 : ℝ)) → 0 < u → u < 1 →
      ∀ J : Edge N P → ℝ,
        ((execute N pmax P a B rho pmin beta h u J).operations : ℝ) ≤ C*(N : ℝ)^C*u^(-C) := by
  let C := SpinGlass.PolynomialRuntime.envelopeConstant (executionAmplitude pmax P a B rho pmin)
    (errorConstant P a B rho) (growth pmax P a B rho pmin) (pmax+3)
  refine ⟨C,SpinGlass.PolynomialRuntime.envelopeConstant_pos _ _ _ _,?_⟩
  intro N hN hpN beta h u hfield hu hu1 J
  apply (execute_envelope N hN P a hP ha pmin hpmin horders pmax hmax hpN hB hBT hfield hu hu1 J).trans
  have hpord : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    have hh := hpmin.trans (horders p hp)
    have h3 : 3 ≤ p := by exact_mod_cast hh
    omega
  have hC := UniformMixedMass.massConstant_ge_one (rho := rho) P a hP ha hpord
    (betaPlus_sq_range P a hP ha hpord hB hBT).1.le (betaPlus_sq_range P a hP ha hpord hB hBT).2
  exact SpinGlass.PolynomialRuntime.envelope_le_polynomial
    (by unfold executionAmplitude amplitude; positivity) (by unfold errorConstant; linarith)
    (by omega) hu hu1.le

end Manuscript.HigherOrderExecution
