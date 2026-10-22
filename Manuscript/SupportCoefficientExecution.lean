import Manuscript.SupportEvaluation
import SpinGlass.ArithmeticEvaluation

/-! Linear-work arithmetic evaluation of the coefficients in Algorithm 2. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SupportCoefficientExecution
open SpinGlass.ArithmeticEvaluation

def divide (x y : Computation) : Computation :=
  ⟨x.value/y.value, x.operations+y.operations+1⟩

/-- A natural index subtraction includes its comparison and subtraction. -/
def indexDifference (n k : ℕ) : Computation := ⟨(n-k : ℕ),2⟩

def descending (n : ℕ) : ℕ → Computation
  | 0 => literal 1
  | k+1 => mul (indexDifference n k) (descending n k)

def factorial : ℕ → Computation
  | 0 => literal 1
  | k+1 => mul ⟨(k+1 : ℕ),1⟩ (factorial k)

@[simp] theorem descending_value (n k : ℕ) : (descending n k).value = n.descFactorial k := by
  induction k with
  | zero => simp [descending,literal]
  | succ k ih => simp [descending, mul, indexDifference, ih, Nat.descFactorial_succ]

@[simp] theorem descending_operations (n k : ℕ) : (descending n k).operations = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [descending, mul, indexDifference, ih]; omega

@[simp] theorem factorial_value (k : ℕ) : (factorial k).value = k.factorial := by
  induction k with
  | zero => simp [factorial,literal]
  | succ k ih => simp [factorial, mul, ih, Nat.factorial_succ]

@[simp] theorem factorial_operations (k : ℕ) : (factorial k).operations = 2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [factorial, mul, ih]; omega

def binomial (n k : ℕ) : Computation := divide (descending n k) (factorial k)

@[simp] theorem binomial_value (n k : ℕ) : (binomial n k).value = n.choose k := by
  simp only [binomial, divide, descending_value, factorial_value]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  exact mul_div_cancel_left₀ _ hf

@[simp] theorem binomial_operations (n k : ℕ) : (binomial n k).operations = 5*k+1 := by
  simp only [binomial, divide, descending_operations, factorial_operations]
  omega

def signPower (k : ℕ) : Computation :=
  productFinset (Finset.range k) (fun _ => literal (-1))

@[simp] theorem signPower_value (k : ℕ) : (signPower k).value = (-1 : ℝ)^k := by
  simp [signPower,literal]

@[simp] theorem signPower_operations (k : ℕ) : (signPower k).operations = k := by
  simp [signPower,literal]

/-- The three index subtractions and coefficient arithmetic are all charged. -/
def coefficient (N k s : ℕ) : Computation :=
  let d := k-s
  let n := N-s-1
  let c := mul (signPower d) (binomial n d)
  ⟨c.value,c.operations+6⟩

@[simp] theorem coefficient_value (N k s : ℕ) :
    (coefficient N k s).value = SupportEvaluation.coefficient N k s := by
  simp [coefficient,mul,SupportEvaluation.coefficient]

@[simp] theorem coefficient_operations (N k s : ℕ) :
    (coefficient N k s).operations = 6*(k-s)+8 := by
  simp [coefficient,mul]
  omega

theorem coefficient_operations_le (N k s : ℕ) :
    (coefficient N k s).operations ≤ 6*k+8 := by
  rw [coefficient_operations]
  omega

end Manuscript.SupportCoefficientExecution
