import Manuscript.SKChargedExecution
import Manuscript.SKChargedPrimitiveCounts
import Manuscript.SKGeneratedExecution

/-!
# Original-edge truncation with the color palette held fixed

The existing array type ties its original-edge capacity to its color count K.
The manuscript instead uses K=2L colors and edge capacity L.  `project L` is
zero-padding of the smaller charge array into the existing one: it retains all
K colors and all six-state degree coordinates.  `projectedEvaluator L` performs
exactly L exponential iterations, truncates every arithmetic update to charge L,
and then selects each direct factor once.

The final theorem proves equality of every retained coefficient with the current
charged evaluator at capacity 2L.  Its positive-charge premise is proved for the
actual ghost-augmented primitives; zero-charge direct edges remain allowed.
This module makes no claim about a compiled machine-code schedule or allocation.
-/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKChargeProjection
open SpinGlass SKCoefficient SKExponential

/-- Retain charge 0,...,L, without reducing the number K of outside colors. -/
def project {b K : ℕ} (L : ℕ) (f : Coefficients b K) : Coefficients b K :=
  fun z => if z.1.val ≤ L then f z else 0

/-- The smaller array has L+1 charge slots and still has all K color bits. -/
abbrev RetainedBasis (b L K : ℕ) :=
  Fin (L+1) × Finset (Fin K) × (Fin b → CappedDegree)

abbrev RetainedCoefficients (b L K : ℕ) := RetainedBasis b L K → ℝ

theorem card_retained_basis (b L K : ℕ) :
    Fintype.card (RetainedBasis b L K) = (L+1) * 2^K * 6^b := by
  simp [RetainedBasis, Fintype.card_prod, Fintype.card_finset,
    CappedDegree.card_eq_six, Nat.mul_assoc]

/-- Read the low-charge coordinates. -/
def restrict {b K L : ℕ} (hLK : L ≤ K) (f : Coefficients b K) :
    RetainedCoefficients b L K := fun z =>
  f (⟨z.1.val, by have := z.1.isLt; omega⟩, z.2)

/-- Zero-pad the smaller array without changing any color or degree state. -/
def expand {b K L : ℕ} (f : RetainedCoefficients b L K) : Coefficients b K :=
  fun z => if hz : z.1.val ≤ L then f (⟨z.1.val, by omega⟩, z.2) else 0

@[simp] theorem restrict_expand {b K L : ℕ} (hLK : L ≤ K)
    (f : RetainedCoefficients b L K) : restrict hLK (expand f) = f := by
  funext z
  have hz : z.1.val ≤ L := by have := z.1.isLt; omega
  simp [restrict, expand, hz]

theorem expand_restrict {b K L : ℕ} (hLK : L ≤ K) (f : Coefficients b K) :
    expand (restrict hLK f) = project L f := by
  funext z
  by_cases hz : z.1.val ≤ L
  · simp [expand, restrict, project, hz]
  · simp [expand, project, hz]

/-- Multiplication in the smaller charge quotient, keeping the same K colors. -/
def retainedMul {b K L : ℕ} (hLK : L ≤ K)
    (f g : RetainedCoefficients b L K) : RetainedCoefficients b L K :=
  restrict hLK (mul (expand f) (expand g))

/-- Agreement on precisely the coefficients retained by the manuscript. -/
def LowAgree {b K : ℕ} (L : ℕ) (f g : Coefficients b K) : Prop :=
  ∀ z, z.1.val ≤ L → f z = g z

@[refl] theorem low_refl {b K : ℕ} (L : ℕ) (f : Coefficients b K) :
    LowAgree L f f := fun _ _ => rfl

theorem low_symm {b K L : ℕ} {f g : Coefficients b K} (h : LowAgree L f g) :
    LowAgree L g f := fun z hz => (h z hz).symm

theorem low_trans {b K L : ℕ} {f g h : Coefficients b K}
    (hfg : LowAgree L f g) (hgh : LowAgree L g h) : LowAgree L f h :=
  fun z hz => (hfg z hz).trans (hgh z hz)

theorem project_low {b K : ℕ} (L : ℕ) (f : Coefficients b K) :
    LowAgree L (project L f) f := by
  intro z hz
  simp [project, hz]

/-- Equal low coefficients are exactly equal arrays after truncation. -/
theorem project_eq_iff {b K L : ℕ} {f g : Coefficients b K} :
    project L f = project L g ↔ LowAgree L f g := by
  constructor
  · intro h z hz
    have he := congrFun h z
    simpa [project, hz] using he
  · intro h
    funext z
    by_cases hz : z.1.val ≤ L
    · simp [project, hz, h z hz]
    · simp [project, hz]

theorem low_add {b K L : ℕ} {f f' g g' : Coefficients b K}
    (hf : LowAgree L f f') (hg : LowAgree L g g') :
    LowAgree L (f + g) (f' + g') := by
  intro z hz
  simp only [Pi.add_apply, hf z hz, hg z hz]

theorem low_scale {b K L : ℕ} (a : ℝ) {f g : Coefficients b K}
    (h : LowAgree L f g) : LowAgree L (scale a f) (scale a g) := by
  intro z hz
  simp only [scale, h z hz]

/-- Nonnegative edge charges mean that a low output only reads low inputs. -/
theorem low_mul {b K L : ℕ} {f f' g g' : Coefficients b K}
    (hf : LowAgree L f f') (hg : LowAgree L g g') :
    LowAgree L (mul f g) (mul f' g') := by
  intro z hz
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hxy : basisMul x y = some z
  · have hdeg := edgeCount_of_basisMul hxy
    have hxL : x.1.val ≤ L := by omega
    have hyL : y.1.val ≤ L := by omega
    simp only [pairContribution, hxy, if_true, hf x hxL, hg y hyL]
  · simp [pairContribution, hxy]

/-- This is the multiplication law of the lower-charge quotient, with the same
color palette: truncating either input early cannot change the output. -/
theorem project_mul {b K : ℕ} (L : ℕ) (f g : Coefficients b K) :
    project L (mul (project L f) (project L g)) = project L (mul f g) :=
  project_eq_iff.mpr (low_mul (project_low L f) (project_low L g))

/-- The smaller array's product is the restriction of the larger product.
Thus its arithmetic is the quotient modulo t^(L+1), with no palette change. -/
theorem retainedMul_restrict {b K L : ℕ} (hLK : L ≤ K) (f g : Coefficients b K) :
    retainedMul hLK (restrict hLK f) (restrict hLK g) = restrict hLK (mul f g) := by
  unfold retainedMul
  rw [expand_restrict, expand_restrict]
  funext z
  exact low_mul (project_low L f) (project_low L g)
    (⟨z.1.val, by have := z.1.isLt; omega⟩, z.2) (by dsimp; have := z.1.isLt; omega)

/-- Original-edge grading, distinct from the existing color grading. -/
def ChargesAtLeast {b K : ℕ} (n : ℕ) (f : Coefficients b K) : Prop :=
  ∀ z, z.1.val < n → f z = 0

theorem charges_mul {b K m n : ℕ} {f g : Coefficients b K}
    (hf : ChargesAtLeast m f) (hg : ChargesAtLeast n g) :
    ChargesAtLeast (m+n) (mul f g) := by
  intro z hz
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  unfold pairContribution
  split
  next h =>
    have hdeg := edgeCount_of_basisMul h
    by_cases hxm : x.1.val < m
    · rw [hf x hxm, MulZeroClass.zero_mul]
    · have hyn : y.1.val < n := by omega
      rw [hg y hyn, MulZeroClass.mul_zero]
  next h => rfl

theorem charges_pow {b K : ℕ} (f : Coefficients b K)
    (hf : ChargesAtLeast 1 f) (n : ℕ) : ChargesAtLeast n (pow f n) := by
  induction n with
  | zero => intro z hz; omega
  | succ n ih => exact charges_mul ih hf

/-- An exponential term of index greater than L has no retained coefficient. -/
theorem term_zero_low {b K L n : ℕ} (f : Coefficients b K)
    (hf : ChargesAtLeast 1 f) (hn : L < n) (z : Basis b K) (hz : z.1.val ≤ L) :
    term f n z = 0 := by
  simp only [term, scale, charges_pow f hf n z (by omega), MulZeroClass.mul_zero]

/-- The extra exponential iterations in the current capacity-K evaluator are
invisible in every charge at most L. -/
theorem expLoop_low_stable {b K : ℕ} (f : Coefficients b K)
    (hf : ChargesAtLeast 1 f) (L k : ℕ) :
    LowAgree L (expLoop f (L+k)).2 (expLoop f L).2 := by
  induction k with
  | zero => simpa using low_refl L (expLoop f L).2
  | succ k ih =>
    intro z hz
    have hv := (expLoop_invariant f (L+k)).1
    change ((expLoop f (L+k)).2 +
      scale (((L+k+1 : ℕ) : ℝ)⁻¹) (mul (expLoop f (L+k)).1 f)) z = _
    rw [hv, term_step]
    simp only [Pi.add_apply, ih z hz, term_zero_low (n := L+k+1) f hf (by omega) z hz, add_zero]

/-- The manuscript's finite-exponential updates, represented by zero-padded
arrays: every multiplication is immediately reduced modulo t^(L+1). -/
def projectedExpLoop {b K : ℕ} (L : ℕ) (f : Coefficients b K) :
    ℕ → Coefficients b K × Coefficients b K
  | 0 => (project L (one b K), project L (one b K))
  | n+1 =>
      let old := projectedExpLoop L f n
      let next := project L (scale (((n+1 : ℕ) : ℝ)⁻¹)
        (mul old.1 (project L f)))
      (next, project L (old.2 + next))

theorem projectedExpLoop_low {b K : ℕ} (L : ℕ) (f : Coefficients b K) (n : ℕ) :
    LowAgree L (projectedExpLoop L f n).1 (expLoop f n).1 ∧
    LowAgree L (projectedExpLoop L f n).2 (expLoop f n).2 := by
  induction n with
  | zero => exact ⟨project_low L _, project_low L _⟩
  | succ n ih =>
    have hnext := low_trans (project_low L _) (low_scale (((n+1 : ℕ) : ℝ)⁻¹)
      (low_mul ih.1 (project_low L f)))
    exact ⟨hnext, low_trans (project_low L _) (low_add ih.2 hnext)⟩

/-- Each direct edge is still selected at most once; it may have charge zero. -/
def projectedDirectLoop {b K : ℕ} (L : ℕ) :
    List (Coefficients b K) → Coefficients b K → Coefficients b K
  | [], acc => project L acc
  | edge :: edges, acc => projectedDirectLoop L edges
      (project L (mul (project L acc) (project L (one b K + edge))))

theorem projectedDirectLoop_low {b K : ℕ} (L : ℕ)
    (edges : List (Coefficients b K)) (acc : Coefficients b K) :
    LowAgree L (projectedDirectLoop L edges acc) (directLoop edges acc) := by
  induction edges generalizing acc with
  | nil => exact project_low L acc
  | cons e es ih =>
    apply low_trans (ih _)
    apply low_directLoop
    exact low_trans (project_low L _)
      (low_mul (project_low L acc) (project_low L (one b K+e)))
where
  low_directLoop {b K L : ℕ} {f g : Coefficients b K}
      (edges : List (Coefficients b K)) (h : LowAgree L f g) :
      LowAgree L (directLoop edges f) (directLoop edges g) := by
    induction edges generalizing f g with
    | nil => exact h
    | cons e es ih => exact ih (low_mul h (low_refl L _))

/-- The smaller quotient and exactly L exponential iterations, followed by all
direct factors, is the mathematical schedule displayed in the manuscript. -/
def projectedEvaluator {b K : ℕ} (L : ℕ) (f : Coefficients b K)
    (edges : List (Coefficients b K)) : Coefficients b K :=
  projectedDirectLoop L edges (projectedExpLoop L f L).2

/-- Algebraic correspondence, proved from coefficient multiplication and charge
positivity, with no premise asserting output equivalence. -/
theorem projectedEvaluator_low {b K L : ℕ} (hLK : L ≤ K)
    (f : Coefficients b K) (hf : ChargesAtLeast 1 f)
    (edges : List (Coefficients b K)) :
    LowAgree L (projectedEvaluator L f edges) (SKDenseExecution.evaluator f edges) := by
  rw [SKDenseExecution.evaluator_correct]
  unfold projectedEvaluator SKExponential.algebraEvaluator
  apply low_trans (projectedDirectLoop_low L edges _)
  apply projectedDirectLoop_low.low_directLoop
  apply low_trans (projectedExpLoop_low L f L).2
  have hstable := expLoop_low_stable f hf L (K-L)
  rw [Nat.add_sub_of_le hLK] at hstable
  exact low_symm hstable

/-- Every monomial with positive original-edge charge vanishes at charge zero. -/
theorem insert_positive {b K : ℕ} (k : ℕ) (S : Finset (Fin K))
    (d : Fin b → CappedDegree) (w : ℝ) (hk : 1 ≤ k) :
    ChargesAtLeast 1 (SKFastEvaluator.insertMonomial k S d w).coeff := by
  unfold SKFastEvaluator.insertMonomial
  split
  · intro z hz
    change (if (⟨k, _⟩, S, d) = z then w else 0) = 0
    split
    next he =>
      have he' := congrArg (fun p : Basis b K => p.1.val) he
      dsimp at he'
      omega
    next he => rfl
  · intro z hz
    rfl

theorem positive_add {b K : ℕ} (f g : SKRing.Element b K)
    (hf : ChargesAtLeast 1 f.coeff) (hg : ChargesAtLeast 1 g.coeff) :
    ChargesAtLeast 1 (f+g).coeff := by
  intro z hz
  change f.coeff z + g.coeff z = 0
  rw [hf z hz, hg z hz, add_zero]

theorem positive_sum {b K : ℕ} {I : Type*} (s : Finset I)
    (f : I → SKRing.Element b K) (hf : ∀ i ∈ s, ChargesAtLeast 1 (f i).coeff) :
    ChargesAtLeast 1 (∑ i ∈ s, f i).coeff := by
  intro z hz
  rw [SKRing.coeff_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i hi => hf i hi z hz)

/-- The only positivity condition needed for paths is that two distinct
endpoints cannot both be the one auxiliary vertex. -/
theorem primitives_positive {V W : Type*} [Fintype W] [DecidableEq W] [DecidableEq V]
    {b K : ℕ} (endpointCharge : Fin b → ℕ) (branch : Fin b → V)
    (outside : W → V) (χ : W → Fin K) (f : Finset V → ℝ)
    (hend : ∀ a c, a<c → 1 ≤ endpointCharge a + endpointCharge c) :
    ChargesAtLeast 1
      (SKChargedExecution.primitives endpointCharge branch outside χ f).coeff := by
  unfold SKChargedExecution.primitives
  apply positive_add
  · apply positive_add
    · apply positive_sum
      intro S hS
      split
      · apply insert_positive
        omega
      · intro z hz; rfl
    · apply positive_sum
      intro a ha
      apply positive_sum
      intro c hc
      split
      next hac =>
        apply positive_sum
        intro S hS
        split
        · apply insert_positive
          have he := hend a c hac
          omega
        · intro z hz; rfl
      next hac => intro z hz; rfl
  · apply positive_sum
    intro a ha
    apply positive_sum
    intro S hS
    split
    · apply insert_positive
      omega
    · intro z hz; rfl

/-- The actual branch labeling has only one possible zero-charge endpoint. -/
theorem ghost_endpoints_positive {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset (Option V)) (a c : Fin A.card) (hac : a<c) :
    1 ≤ SKChargedPrimitiveCounts.endpointCharge A a +
      SKChargedPrimitiveCounts.endpointCharge A c := by
  have hne : SKActualEvaluator.branch A a ≠ SKActualEvaluator.branch A c :=
    fun h => (ne_of_lt hac) (SKActualEvaluator.branch_injective A h)
  by_cases ha : SKActualEvaluator.branch A a = none <;>
    by_cases hc : SKActualEvaluator.branch A c = none
  · exact (hne (ha.trans hc.symm)).elim
  all_goals simp [SKChargedPrimitiveCounts.endpointCharge, ha, hc]

/-- For the actual augmented evaluator with 2L colors, truncating the charge
array to L after each update and stopping the exponential at L gives exactly
the same retained coefficient. Zero-charge direct auxiliary edges are allowed. -/
theorem ghost_capacity_two_mul_eq_manuscript {V : Type*} [Fintype V] [DecidableEq V]
    (L : ℕ) (A : Finset (Option V)) (χ : SKActualEvaluator.Outside A → Fin (2*L))
    (f : Finset (Option V) → ℝ) (z : Basis A.card (2*L)) (hz : z.1.val ≤ L) :
    projectedEvaluator L
      (SKChargedExecution.primitives (SKChargedPrimitiveCounts.endpointCharge A)
        (SKActualEvaluator.branch A) Subtype.val χ f).coeff
      ((SKChargedExecution.directPairs A.card).toList.map (fun p =>
        (SKChargedExecution.direct (L := 2*L) (SKChargedPrimitiveCounts.endpointCharge A)
          (SKActualEvaluator.branch A) f p.1 p.2).coeff)) z =
    SKChargedExecution.evaluate (SKChargedPrimitiveCounts.endpointCharge A)
      (SKActualEvaluator.branch A) Subtype.val χ f z := by
  apply projectedEvaluator_low (by omega)
    (SKChargedExecution.primitives (SKChargedPrimitiveCounts.endpointCharge A)
      (SKActualEvaluator.branch A) Subtype.val χ f).coeff
    (primitives_positive _ _ _ _ _ (ghost_endpoints_positive A)) _ z hz

section OriginalGraphExtraction
variable {V : Type*} [Fintype V] [DecidableEq V]
open SKGhostAdmissible SKActualEvaluator SKChargedPrimitiveCounts SKAugmentFinset

/-- The projected L-step evaluator on the actual original candidate set, field,
and weights. Its palette remains exactly Fin (2*L). -/
def projectedGhostEvaluate (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (h : ℝ) (w : Finset V → ℝ) : Coefficients (distinguished A).card (2*L) :=
  projectedEvaluator L
    (SKChargedExecution.primitives (endpointCharge (distinguished A))
      (branch (distinguished A)) Subtype.val (outsideColor A χ) (edgeWeight h w)).coeff
    ((SKChargedExecution.directPairs (distinguished A).card).toList.map (fun p =>
      (SKChargedExecution.direct (L := 2*L) (endpointCharge (distinguished A))
        (branch (distinguished A)) (edgeWeight h w) p.1 p.2).coeff))

/-- Apply the original accepting-state, edge, and outside-size extraction to the
projected arrays. The filtered large index is the zero-padded smaller array. -/
def projectedByOutsideSize (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (m : ℕ) (h : ℝ) (w : Finset V → ℝ) : ℝ :=
  ∑ k : Fin (2*L+1), ∑ S : Finset (Fin (2*L)), ∑ d ∈ accepted A,
    if k.val ≤ L ∧ S.card = m then
      projectedGhostEvaluate L A χ h w (SKChargedMonomial.target k S d) else 0

/-- The actual extracted outside-size vectors agree, with no equality premise. -/
theorem projectedByOutsideSize_eq (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (m : ℕ) (h : ℝ) (w : Finset V → ℝ) :
    projectedByOutsideSize L A χ m h w =
      SKGhostCoefficient.byOutsideSize A χ L m h w := by
  unfold projectedByOutsideSize SKGhostCoefficient.byOutsideSize
    SKChargedExecution.byOutsideSize
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hc : k.val ≤ L ∧ S.card = m
  · simp only [hc]
    exact ghost_capacity_two_mul_eq_manuscript L (distinguished A) (outsideColor A χ)
      (edgeWeight h w) (SKChargedMonomial.target k S d) hc.1
  · simp only [hc, if_false]

/-- The inverse-color-probability correction is applied to projected output. -/
def projectedTrial (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (h : ℝ) (w : Finset V → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (2*L+1), (ColoringProbability.probability (2*L) m)⁻¹ *
    projectedByOutsideSize L A χ m h w

/-- Each actual generated trial has the projected manuscript value. -/
theorem projectedTrial_eq (L : ℕ) (A : Finset V) (χ : V → Fin (2*L))
    (h : ℝ) (w : Finset V → ℝ) :
    projectedTrial L A χ h w = (SKGeneratedExecution.trial L A χ (Real.tanh h) w).value := by
  rw [SKGeneratedExecution.trial_value]
  simp only [projectedTrial, projectedByOutsideSize_eq]

/-- Average the projected trials over the actual candidate and repetition sets. -/
def projectedAlgorithm (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (h : ℝ) (w : Finset V → ℝ) : ℝ :=
  ∑ b ∈ Finset.range (D+1), ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
    (R : ℝ)⁻¹ * ∑ r : Fin R, projectedTrial L A (χ A r) h w

/-- Full candidate/repetition aggregation preserves the proven correspondence. -/
theorem projectedAlgorithm_eq (D L R : ℕ) (χ : SKColorEstimator.Colors V L R)
    (h : ℝ) (w : Finset V → ℝ) :
    projectedAlgorithm D L R χ h w = SKGhostCoefficient.algorithm D L R χ h w := by
  simp only [projectedAlgorithm, projectedTrial, projectedByOutsideSize_eq,
    SKGhostCoefficient.algorithm]

/-- Direct transfer to the actual counted finite estimator, for every color
outcome and finite signed edge input. No estimator-equivalence assumption occurs. -/
theorem projectedAlgorithm_eq_generated (D L R : ℕ)
    (χ : SKColorEstimator.Colors V L R) (h : ℝ) (w : Finset V → ℝ) :
    projectedAlgorithm D L R χ h w =
      (SKGeneratedExecution.estimator D L R χ (Real.tanh h) w).value := by
  rw [SKGeneratedExecution.estimator_value, projectedAlgorithm_eq]

/-- The projected manuscript schedule is also exactly the analyzed graph
estimator on the original disorder inputs, not merely an algebraic surrogate. -/
theorem projectedAlgorithm_eq_disorder (D L R : ℕ) (hL : 0 < L)
    (χ : SKColorEstimator.Colors V L R) (h : ℝ) (a J : Finset V → ℝ) :
    projectedAlgorithm D L R χ h (fun e => Real.tanh (a e * J e)) =
      SKColorEstimator.estimator id ((Finset.univ : Finset V).powersetCard 2)
        D L R h a χ J := by
  rw [projectedAlgorithm_eq, SKGhostCoefficient.algorithm_eq_disorder D L R hL]

end OriginalGraphExtraction

/-- The manuscript array has precisely its displayed number of entries. -/
theorem manuscript_array_size (b L : ℕ) :
    Fintype.card (RetainedBasis (b+1) L (2*L)) = (L+1)*4^L*6^(b+1) := by
  rw [card_retained_basis]
  have hpow : (2 : ℕ)^(2*L) = 4^L := by rw [pow_mul]; norm_num
  rw [hpow]

end Manuscript.SKChargeProjection
