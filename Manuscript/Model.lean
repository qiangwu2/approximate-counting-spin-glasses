import Manuscript.FieldExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The manuscript's finite mixed-spin model

The physical inputs are indexed by distinct unordered subsets with cardinality in
`P`. This file ties the literal exponential model, with coefficients `a_p` and
homogeneous field `h`, to the finite field expansion. No moment, probability,
truncation or polynomial-runtime conclusion is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.Model
open SpinGlass.Expansion

/-- Exactly the distinct unordered physical hyperedges of the active orders. -/
def physicalEdges (N : ℕ) (P : Finset ℕ) : Finset (Finset (Fin N)) :=
  Finset.univ.filter (fun e => e.card ∈ P)

/-- The input array contains only physical interactions. -/
abbrev Edge (N : ℕ) (P : Finset ℕ) := {e : Finset (Fin N) // e ∈ physicalEdges N P}

@[simp] theorem mem_physicalEdges {N : ℕ} {P : Finset ℕ} {e : Finset (Fin N)} :
    e ∈ physicalEdges N P ↔ e.card ∈ P := by simp [physicalEdges]

theorem edge_order_mem {N : ℕ} {P : Finset ℕ} (e : Edge N P) : e.val.card ∈ P :=
  mem_physicalEdges.mp e.property

/-- The denominator in equation (2), with a real half-integer exponent. -/
def scaleDenominator (N p : ℕ) : ℝ := (N : ℝ) ^ (((p : ℝ) - 1) / 2)

/-- The interaction coefficient `x_e` in the normalized expansion. -/
def coefficient (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (J : Edge N P → ℝ) (e : Edge N P) : ℝ :=
  beta * a e.val.card * J e / scaleDenominator N e.val.card

/-- Equation (2), expressed as a single sum over the disjoint physical orders. -/
def hamiltonian (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (J : Edge N P → ℝ) (σ : Fin N → Bool) : ℝ :=
  ∑ e, (a e.val.card * J e / scaleDenominator N e.val.card) *
    edgeCharacter Subtype.val σ e

/-- The unnormalized exponential partition function in equation (3). -/
def partition (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (J : Edge N P → ℝ) : ℝ :=
  ∑ σ : Fin N → Bool,
    Real.exp (beta * hamiltonian N P a J σ + h * ∑ v, spinSign (σ v))

/-- The explicit factor separated in equation (13). -/
def prefactor (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (J : Edge N P → ℝ) : ℝ :=
  (2 * Real.cosh h) ^ N * ∏ e, Real.cosh (coefficient N P a beta J e)

def normalizedPartition (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta h : ℝ)
    (J : Edge N P → ℝ) : ℝ := partition N P a beta h J / prefactor N P a beta h J

/-- Exact coefficient identity; no restrictions on the finite real input. -/
theorem beta_hamiltonian (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (J : Edge N P → ℝ) (σ : Fin N → Bool) :
    beta * hamiltonian N P a J σ =
      ∑ e, coefficient N P a beta J e * edgeCharacter Subtype.val σ e := by
  unfold hamiltonian
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  unfold coefficient
  ring

/-- The finite field-expansion theorem applies to the exact manuscript model. -/
theorem partition_eq_fieldPartition (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N P → ℝ) :
    partition N P a beta h J = FieldExpansion.partitionFunction
      Subtype.val Finset.univ h (coefficient N P a beta J) := by
  unfold partition FieldExpansion.partitionFunction
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [beta_hamiltonian]

@[simp] theorem prefactor_eq_fieldPrefactor (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N P → ℝ) :
    prefactor N P a beta h J = FieldExpansion.prefactor (V := Fin N)
      Finset.univ h (coefficient N P a beta J) := by
  simp [prefactor, FieldExpansion.prefactor]

theorem normalizedPartition_eq_fieldNormalized (N : ℕ) (P : Finset ℕ)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Edge N P → ℝ) :
    normalizedPartition N P a beta h J = FieldExpansion.normalizedPartition
      Subtype.val Finset.univ h (coefficient N P a beta J) := by
  simp only [normalizedPartition, FieldExpansion.normalizedPartition,
    partition_eq_fieldPartition, prefactor_eq_fieldPrefactor]

/-- Equation (14) on the actual finite mixed physical-edge input type. -/
theorem normalizedPartition_eq_graph_sum (N : ℕ) (P : Finset ℕ)
    (a : ℕ → ℝ) (beta h : ℝ) (J : Edge N P → ℝ) :
    normalizedPartition N P a beta h J =
      ∑ Γ ∈ (Finset.univ : Finset (Edge N P)).powerset,
        FieldExpansion.graphWeight Subtype.val h
          (fun e => Real.tanh (coefficient N P a beta J e)) Γ := by
  rw [normalizedPartition_eq_fieldNormalized]
  exact FieldExpansion.normalizedPartition_eq_graph_sum _ _ _ _

theorem partition_pos (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N P → ℝ) : 0 < partition N P a beta h J := by
  rw [partition_eq_fieldPartition]
  exact FieldExpansion.partition_pos _ _ _ _

theorem normalizedPartition_pos (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta h : ℝ) (J : Edge N P → ℝ) : 0 < normalizedPartition N P a beta h J := by
  rw [normalizedPartition_eq_fieldNormalized]
  exact FieldExpansion.normalizedPartition_pos _ _ _ _

/-- Setting the field to zero gives the earlier arbitrary-incidence partition. -/
theorem partition_zero_field (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta : ℝ) (J : Edge N P → ℝ) :
    partition N P a beta 0 J = SpinGlass.Partition.partitionFunction
      Subtype.val Finset.univ (coefficient N P a beta J) := by
  rw [partition_eq_fieldPartition]
  simp [FieldExpansion.partitionFunction, SpinGlass.Partition.partitionFunction]

/-- Normalization specializes as well, including the factor `2^N`. -/
theorem normalizedPartition_zero_field (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta : ℝ) (J : Edge N P → ℝ) :
    normalizedPartition N P a beta 0 J = SpinGlass.Partition.normalizedPartition
      Subtype.val Finset.univ (coefficient N P a beta J) := by
  simp [normalizedPartition, SpinGlass.Partition.normalizedPartition,
    partition_zero_field, prefactor, SpinGlass.Partition.prefactor]

/-- The old even-hypergraph sum is an exact zero-field specialization. -/
theorem zero_field_even_graph_sum (N : ℕ) (P : Finset ℕ) (a : ℕ → ℝ)
    (beta : ℝ) (J : Edge N P → ℝ) :
    normalizedPartition N P a beta 0 J =
      ∑ Γ ∈ (Finset.univ : Finset (Edge N P)).powerset.filter (IsEven Subtype.val),
        ∏ e ∈ Γ, Real.tanh (coefficient N P a beta J e) := by
  rw [normalizedPartition_zero_field]
  exact SpinGlass.Partition.normalizedPartition_eq_even_sum _ _ _

/-- A singleton active set is precisely the usual family of `p`-element edges. -/
theorem physicalEdges_singleton (N p : ℕ) :
    physicalEdges N {p} = (Finset.univ : Finset (Fin N)).powersetCard p := by
  ext e
  simp

@[simp] theorem singleton_edge_card {N p : ℕ} (e : Edge N {p}) : e.val.card = p := by
  simpa using edge_order_mem e

/-- Coefficients specialize literally to the stated pure-order formula. -/
theorem coefficient_singleton (N p : ℕ) (a : ℕ → ℝ) (beta : ℝ)
    (J : Edge N {p} → ℝ) (e : Edge N {p}) :
    coefficient N {p} a beta J e = beta * a p * J e / scaleDenominator N p := by
  simp [coefficient]

end Manuscript.Model
