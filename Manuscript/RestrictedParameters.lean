import Manuscript.RestrictedControlFrames

noncomputable section
namespace Manuscript.RestrictedParameters
open RestrictedMachine RestrictedControl

def controlBase (pmax : ℕ) := pmax+1
def budgetBase (pmax : ℕ) := pmax+8

def background (pmax : ℕ) (a : ℕ → ℝ) (C exponent : ℝ) : Parameters :=
  Function.update (Function.update a (budgetBase pmax) C) (budgetBase pmax+1) exponent

def higher (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) : Parameters :=
  parameterBlock (controlBase pmax) 7
    (higherConstants (manuscriptHigherDesign pmax P a B rho pmin))
    (background pmax a (LogApprox.constant P a B rho) (LogApprox.exponent P a B))

def sk (a : ℕ → ℝ) (B rho : ℝ) : Parameters :=
  parameterBlock (controlBase 2) 5 (skConstants (manuscriptSKDesign a B rho))
    (background 2 a (LogApprox.constant {2} a B rho) (LogApprox.exponent {2} a B))

theorem background_model (pmax : ℕ) (a : ℕ → ℝ) (C exponent : ℝ) (p : ℕ) (hp : p ≤ pmax) :
    background pmax a C exponent p=a p := by
  simp [background,budgetBase,show p ≠ pmax+8 by omega,show p ≠ pmax+8+1 by omega]

theorem higher_model (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ)
    (p : ℕ) (hp : p ≤ pmax) : higher pmax P a B rho pmin p=a p := by
  unfold higher
  rw [parameterBlock_outside _ _ _ _ _ (Or.inl (by dsimp [controlBase]; omega))]
  exact background_model _ _ _ _ _ hp

theorem sk_model (a : ℕ → ℝ) (B rho : ℝ) : sk a B rho 2=a 2 := by
  unfold sk
  rw [parameterBlock_outside _ _ _ _ _ (Or.inl (by decide))]
  exact background_model _ _ _ _ _ (by omega)

theorem background_budget (pmax : ℕ) (a : ℕ → ℝ) (C exponent : ℝ) :
    background pmax a C exponent (budgetBase pmax)=C ∧
    background pmax a C exponent (budgetBase pmax+1)=exponent := by
  simp [background,budgetBase]

theorem higher_budget (pmax : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (B rho pmin : ℝ) :
    higher pmax P a B rho pmin (budgetBase pmax)=LogApprox.constant P a B rho ∧
    higher pmax P a B rho pmin (budgetBase pmax+1)=LogApprox.exponent P a B := by
  unfold higher
  rw [parameterBlock_outside _ _ _ _ _ (Or.inr (by dsimp [controlBase,budgetBase]; omega)),
    parameterBlock_outside _ _ _ _ _ (Or.inr (by dsimp [controlBase,budgetBase]; omega))]
  exact background_budget _ _ _ _

theorem sk_budget (a : ℕ → ℝ) (B rho : ℝ) :
    sk a B rho (budgetBase 2)=LogApprox.constant {2} a B rho ∧
    sk a B rho (budgetBase 2+1)=LogApprox.exponent {2} a B := by
  unfold sk
  rw [parameterBlock_outside _ _ _ _ _ (Or.inr (by decide)),
    parameterBlock_outside _ _ _ _ _ (Or.inr (by decide))]
  exact background_budget _ _ _ _

end Manuscript.RestrictedParameters
