import Manuscript.SKChargedExtractionExecution
import SpinGlass.SKActualEvaluator

/-! # Structural and sampling schedules for the cached evaluator

These counters supplement real arithmetic with the control, comparisons, finite
uniform draws and register/index visits of the same finite loops. Finite sets
of colors are represented by `L` bits and branch degrees by `b` six-state digits.
The conservative per-visit allowances include rejected states, scans of colors,
integer index formation, initialization, and a scan of up to `N²` prepared edge
keys for each input-weight read. They describe an explicit unit-operation
implementation schedule, not the instruction count of the Lean interpreter.
-/
noncomputable section
namespace Manuscript.SKChargedControlExecution
open SpinGlass SpinGlass.SKCountedExecution Manuscript.SKChargedPrimitiveExecution
open scoped BigOperators

/-- A literal list traversal, including its terminating test. The allowance at
each visited index pays all its tests, indexing and data movement. -/
def visitControl {I : Type*} (allowance : ℕ) : List I → ℕ
  | [] => 1
  | _ :: xs => allowance + visitControl allowance xs

@[simp] theorem visitControl_eq {I : Type*} (c : ℕ) (xs : List I) :
    visitControl c xs = 1 + xs.length * c := by
  induction xs with
  | nil => simp [visitControl]
  | cons x xs ih => simp [visitControl, ih, Nat.add_mul]; omega

/-- Every saved-layer coordinate checks its cardinality and color bits; all `N`
predecessors receive a full prepared-edge scan allowance, even if unused. -/
def memoPassControl (N b L : ℕ) {W : Type*} [Fintype W] : ℕ :=
  visitControl (20 * (N + L + 1)^3)
    (Finset.univ.toList : List (Finset (Fin L) × W))

def memoControl (N b L : ℕ) {W : Type*} [Fintype W] : ℕ → ℕ
  | 0 => 1 + 2^L * Fintype.card W
  | n+1 => memoControl (W := W) N b L n + memoPassControl (W := W) N b L

@[simp] theorem memoControl_eq (N b L n : ℕ) {W : Type*} [Fintype W] :
    memoControl (W := W) N b L n = 1 + 2^L * Fintype.card W +
      n * (1 + (2^L * Fintype.card W) * (20 * (N+L+1)^3)) := by
  induction n with
  | zero => simp [memoControl]
  | succ n ih =>
    simp only [memoControl, ih, memoPassControl, visitControl_eq, Finset.length_toList,
      Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    ring

/-- The once-per-root cache schedule, including table initialization and writes. -/
def rootControl (N b L : ℕ) {W : Type*} [Fintype W] : ℕ :=
  visitControl (memoControl (W := W) N b L L + 2)
    (Finset.univ.toList : List (Root W b))

/-- Primitive insertion scans the identical sum-type instruction catalog.
A cycle key is allowed all `N²` closures with full `N²` edge-key scans. -/
def primitiveControl (N b L : ℕ) : ℕ :=
  visitControl (20 * (N+L+1)^4)
    (Finset.univ.toList : List (PrimitiveKey b L))

/-- Coordinate extraction uses its existing flat `(k,S)` schedule. This includes
forming the inverse coloring probability by at most `L` rational factors. -/
def extractionControl (N b L : ℕ) : ℕ :=
  visitControl (10 * (N+L+1)^2)
    (Finset.univ.toList : List (SKCoefficient.Basis b L))

/-- All possible branch pairs are tested; every direct-factor array may be
materialized with a complete scan and a prepared-edge lookup at each register. -/
def directSetupControl (N b L : ℕ) : ℕ :=
  visitControl (1 + 10 * SKOperationCount.registers b L * (N+L+1)^2)
    (Finset.univ.toList : List (Fin b × Fin b))

/-- The unused entries in the mathematical global color tape are never sampled:
exactly one finite-uniform draw is used for each actual outside vertex. -/
def samplingDraws {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V) : ℕ :=
  (Finset.univ.toList : List (SKActualEvaluator.Outside A)).length

@[simp] theorem samplingDraws_eq {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V) :
    samplingDraws A = Fintype.card (SKActualEvaluator.Outside A) := by simp [samplingDraws]

/-- Control outside coefficient algebra, including sampling and candidate
labeling/index initialization. -/
def outerTrialControl (N b L : ℕ) {W : Type*} [Fintype W] : ℕ :=
  rootControl (W := W) N b L + primitiveControl N b L + extractionControl N b L +
    directSetupControl N b L + Fintype.card W + 20 * (N+L+1)^2

/-- The acceptance family is stored as a list. Every extracted coordinate
compares at most all stored degree vectors, with all `b` digits inspected.
The initial digit scan also pays for generating/filtering the state family. -/
def acceptanceControl (b K : ℕ) (accepted : Finset (Fin b → CappedDegree)) : ℕ :=
  visitControl (visitControl (2*b+2) accepted.toList)
    (Finset.univ.toList : List (SKCoefficient.Basis b K)) +
      visitControl (2*b+2) (Finset.univ.toList : List (Fin b → CappedDegree))

theorem acceptanceControl_bound {N b K : ℕ} (hb : b ≤ N)
    (accepted : Finset (Fin b → CappedDegree)) :
    acceptanceControl b K accepted ≤ 16*(N+K+1)^6*4^K*36^b := by
  let M := N+K+1
  let T := 4^K*36^b
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hbM : b+1 ≤ M := by dsimp [M]; omega
  have hK : K+1 ≤ M := by dsimp [M]; omega
  have hcard : accepted.card ≤ 6^b := by
    simpa [Fintype.card_fun,CappedDegree.card_eq_six] using Finset.card_le_univ accepted
  have hs : 6^b ≤ T := by
    have hh := Nat.pow_le_pow_left (by omega : 6≤36) b
    exact hh.trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hr : (K+1)*2^K*6^b ≤ M*T := by
    dsimp [T]
    have hh := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : 2≤4) K)
      (Nat.pow_le_pow_left (by omega : 6≤36) b)
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul hK hh
  have hr2 : (K+1)*2^K*6^b*6^b ≤ M*T := by
    dsimp [T]
    have hh := Nat.mul_le_mul hK (Nat.pow_le_pow_left (by omega : 2≤4) K)
    have he : (6:ℕ)^b*6^b=36^b := by rw [← mul_pow]; norm_num
    calc
      _ = (K+1)*2^K*(6^b*6^b) := by ring
      _ ≤ (M*4^K)*(6^b*6^b) := Nat.mul_le_mul_right _ hh
      _ = _ := by rw [he]; ring
  have hT : 1 ≤ T := Nat.succ_le_of_lt (by dsimp [T]; positivity)
  have hp : M^2*T ≤ M^6*T := Nat.mul_le_mul_right T (Nat.pow_le_pow_right hM (by omega))
  have hm : M*T ≤ M^2*T := Nat.mul_le_mul_right T (by nlinarith)
  unfold acceptanceControl
  simp only [visitControl_eq,Finset.length_toList,Finset.card_univ,SKCoefficient.card_basis,
    Fintype.card_fun,Fintype.card_fin,CappedDegree.card_eq_six]
  change _ ≤ 16*M^6*4^K*36^b
  have he : 16*M^6*4^K*36^b=16*M^6*T := by dsimp [T]; ring
  rw [he]
  have hc := Nat.mul_le_mul_left ((K+1)*2^K*6^b) hcard
  have hca : (K+1)*2^K*6^b*accepted.card ≤ M*T := hc.trans hr2
  have hca' := Nat.mul_le_mul hca (show 2*b+2≤2*M by omega)
  have hs' := Nat.mul_le_mul hs (show 2*b+2≤2*M by omega)
  have hbase : 1≤M^6*T := Nat.succ_le_of_lt (by positivity)
  nlinarith

/-- All finite control schedules retain an absolute polynomial exponent. -/
theorem outerTrialControl_bound {N b L : ℕ} {W : Type*} [Fintype W]
    (hb : b ≤ N) (hw : Fintype.card W ≤ N) :
    outerTrialControl (W := W) N b L ≤ 256 * (N+L+1)^6 * 4^L * 36^b := by
  let M := N+L+1
  let T := 4^L*36^b
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hN : N ≤ M := by dsimp [M]; omega
  have hW : Fintype.card W ≤ M := hw.trans hN
  have hbM : b ≤ M := hb.trans hN
  have hL : L ≤ M := by dsimp [M]; omega
  have hL1 : L+1 ≤ M := by dsimp [M]; omega
  have hT : 1 ≤ T := Nat.succ_le_of_lt (by dsimp [T]; positivity)
  have h2 : 2^L ≤ T := by
    calc
      2^L ≤ 4^L := Nat.pow_le_pow_left (by omega) _
      _ ≤ 4^L*36^b := Nat.le_mul_of_pos_right _ (by positivity)
  have hreg : SKOperationCount.registers b L ≤ M^2*T := by
    have hreg2 : SKOperationCount.registers b L ^ 2 ≤ M^2*T := by
      rw [SKOperationCount.registers_sq]
      dsimp [T]
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (36^b) (Nat.mul_le_mul_right (4^L) (Nat.pow_le_pow_left hL1 2))
    have hr : 1 ≤ SKOperationCount.registers b L := Nat.succ_le_of_lt (by unfold SKOperationCount.registers; positivity)
    have : SKOperationCount.registers b L ≤ SKOperationCount.registers b L ^ 2 := by nlinarith
    exact this.trans hreg2
  have hreg' : (L+1)*2^L*6^b ≤ M^2*T := hreg
  have hp (i : ℕ) (hi : i ≤ 6) : M^i*T ≤ M^6*T :=
    Nat.mul_le_mul_right T (Nat.pow_le_pow_right hM hi)
  have hbase : 1 ≤ M^6*T := Nat.succ_le_of_lt (by positivity)
  have hplain : M ≤ M^6*T := by
    have hh := hp 1 (by omega)
    simp only [pow_one] at hh
    have hm : M ≤ M*T := Nat.le_mul_of_pos_right _ (by positivity)
    simpa using hm.trans hh
  have hplain2 : M^2 ≤ M^6*T := by
    have hm : M^2 ≤ M^2*T := Nat.le_mul_of_pos_right _ (by positivity)
    exact hm.trans (hp 2 (by omega))
  unfold outerTrialControl rootControl primitiveControl extractionControl directSetupControl
  simp only [visitControl_eq, Finset.length_toList, Finset.card_univ, memoControl_eq,
    Root, PrimitiveKey, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_finset, SKCoefficient.card_basis]
  change _ ≤ 256 * M^6 * 4^L * 36^b
  calc
    _ ≤ (1 + (M+M) * (1 + T*M + M*(1 + T*M*(20*M^3)) + 2)) +
        (1 + (T + (M*(M*T) + M*T))*(20*M^4)) +
        (1 + (M^2*T)*(10*M^2)) +
        (1 + (M*M)*(1 + 10*(M^2*T)*M^2)) + M + 20*M^2 := by
      gcongr
      · exact hL1.trans (by nlinarith : M ≤ M^2)
      · have hh : 2^L*6^b ≤ T := Nat.mul_le_mul
          (Nat.pow_le_pow_left (by omega : 2≤4) L)
          (Nat.pow_le_pow_left (by omega : 6≤36) b)
        simpa [Fintype.card_fun, CappedDegree.card_eq_six] using hh
    _ ≤ 256 * M^6 * T := by
      nlinarith [hp 1 (by omega), hp 2 (by omega), hp 3 (by omega),
        hp 4 (by omega), hp 5 (by omega), hp 6 (by omega)]
    _ = _ := by dsimp [T]; ring

end Manuscript.SKChargedControlExecution
