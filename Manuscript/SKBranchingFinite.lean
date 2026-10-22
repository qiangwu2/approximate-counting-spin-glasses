import Manuscript.SKGraphBasics
import SpinGlass.SKBranchingMassFinite

/-!
# Pairing majorization with the weak-field degree weights

The pairing injection applies to arbitrary degree sequences. This module keeps
the odd-degree field factor in every degree fiber, instead of discarding all
odd-degree graphs as in the zero-field specialization.
-/

noncomputable section
open scoped BigOperators

namespace Manuscript.SKBranching

open MeasureTheory SpinGlass.SKBranching

variable {V : Type*} [Fintype V] [DecidableEq V]

def oddCount (d : V → ℕ) : ℕ :=
  (Finset.univ.filter (fun v => ¬Even (d v))).card

def weightedDegreeMonomial (φ r : ℝ) (d : V → ℕ) (x : ℝ) : ℝ :=
  φ ^ oddCount d * degreeMonomial r d x

theorem oddCount_degree (Γ : Finset (Finset V)) :
    oddCount (SpinGlass.Hypergraph.degree Γ) = (FieldExpansion.boundary id Γ).card := rfl

/-- An actual graph fiber has the same weak-field factor at every realization. -/
theorem weighted_degree_fiber_mass_le (F : Finset (Finset (Finset V)))
    (hF : ∀ Γ ∈ F, ∀ e ∈ Γ, e.card = 2) {φ r : ℝ}
    (hφ : 0 ≤ φ) (hr : 0 ≤ r) (d : V → ℕ)
    {k : ℕ} (hsum : ∑ v, d v = 2 * k) :
    (∑ Γ ∈ F.filter (fun Γ => SpinGlass.Hypergraph.degree Γ = d),
      φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) ≤
        gaussianMean (weightedDegreeMonomial φ r d) := by
  have heq : (∑ Γ ∈ F.filter (fun Γ => SpinGlass.Hypergraph.degree Γ = d),
      φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) =
      φ ^ oddCount d *
        ∑ Γ ∈ F.filter (fun Γ => SpinGlass.Hypergraph.degree Γ = d), r ^ Γ.card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Γ hΓ
    rw [← oddCount_degree, (Finset.mem_filter.mp hΓ).2]
  unfold weightedDegreeMonomial
  rw [heq, gaussianMean_const_mul]
  exact mul_le_mul_of_nonneg_left (degree_fiber_mass_le F hF r hr d hsum)
    (pow_nonneg hφ _)

theorem gaussianIntegrable_weightedDegreeMonomial {φ r : ℝ} (hr : 0 ≤ r)
    (d : V → ℕ) {k : ℕ} (hsum : ∑ v, d v = 2 * k) :
    GaussianIntegrable (weightedDegreeMonomial φ r d) := by
  have hi := gaussianIntegrable_degreeMonomial r hr d hsum
  unfold GaussianIntegrable weightedDegreeMonomial
  simpa only [mul_assoc] using hi.const_mul (φ ^ oddCount d)

/-- Finite Gaussian majorization of the actual weak-field graph mass. -/
theorem finite_weighted_degree_mass_le_gaussian (F : Finset (Finset (Finset V)))
    (hF : ∀ Γ ∈ F, ∀ e ∈ Γ, e.card = 2) {φ r : ℝ}
    (hφ : 0 ≤ φ) (hr : 0 ≤ r) (D : Finset (V → ℕ))
    (hcover : ∀ Γ ∈ F, SpinGlass.Hypergraph.degree Γ ∈ D)
    (heven : ∀ d ∈ D, ∃ k, ∑ v, d v = 2 * k) :
    (∑ Γ ∈ F, φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) ≤
      gaussianMean (fun x => ∑ d ∈ D, weightedDegreeMonomial φ r d x) := by
  rw [gaussianMean_sum D _ (fun d hd => by
    obtain ⟨k, hk⟩ := heven d hd
    exact gaussianIntegrable_weightedDegreeMonomial hr d hk),
    ← Finset.sum_fiberwise_of_maps_to hcover]
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨k, hk⟩ := heven d hd
  exact weighted_degree_fiber_mass_le F hF hφ hr d hk

/-- All pair-interaction graphs, including odd degrees. -/
def pairGraphs (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset (Finset V)) :=
  ((Finset.univ : Finset V).powersetCard 2).powerset

def branchFamily (A : Finset V) : Finset (Finset (Finset V)) :=
  (pairGraphs V).filter (fun Γ => SKGraph.branch id Γ = A)

def branchCardFamily (b : ℕ) : Finset (Finset (Finset V)) :=
  (pairGraphs V).filter (fun Γ => (SKGraph.branch id Γ).card = b)

theorem branchFamily_simple (A : Finset V) {Γ : Finset (Finset V)}
    (hΓ : Γ ∈ branchFamily A) : ∀ e ∈ Γ, e.card = 2 := by
  intro e he
  exact (Finset.mem_powersetCard.mp
    ((Finset.mem_powerset.mp (Finset.mem_filter.mp hΓ).1) he)).2

/-- The actual degree signatures occurring in the fixed-branching family. -/
def realizedDegrees (A : Finset V) : Finset (V → ℕ) :=
  (branchFamily A).image SpinGlass.Hypergraph.degree

theorem realizedDegrees_even (A : Finset V) (d : V → ℕ)
    (hd : d ∈ realizedDegrees A) : ∃ k, ∑ v, d v = 2 * k := by
  obtain ⟨Γ, hΓ, rfl⟩ := Finset.mem_image.mp hd
  exact ⟨Γ.card, sum_degrees_simple Γ (branchFamily_simple A hΓ)⟩

/-- No hypothesis about realizability or parity is left for the caller to prove. -/
theorem branchFamily_mass_le_gaussian (A : Finset V) {φ r : ℝ}
    (hφ : 0 ≤ φ) (hr : 0 ≤ r) :
    (∑ Γ ∈ branchFamily A, φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) ≤
      gaussianMean (fun x => ∑ d ∈ realizedDegrees A, weightedDegreeMonomial φ r d x) := by
  apply finite_weighted_degree_mass_le_gaussian (branchFamily A)
    (fun Γ hΓ => branchFamily_simple A hΓ) hφ hr (realizedDegrees A)
  · intro Γ hΓ
    exact Finset.mem_image.mpr ⟨Γ, hΓ, rfl⟩
  · exact realizedDegrees_even A

/-- The full branching-cardinality mass partitions by its exact branching set. -/
theorem branchCard_mass_eq (b : ℕ) (φ r : ℝ) :
    (∑ Γ ∈ branchCardFamily (V := V) b,
      φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card) =
      ∑ A ∈ (Finset.univ : Finset V).powersetCard b,
        ∑ Γ ∈ branchFamily A, φ ^ (FieldExpansion.boundary id Γ).card * r ^ Γ.card := by
  have hcover : ∀ Γ ∈ branchCardFamily (V := V) b,
      SKGraph.branch id Γ ∈ (Finset.univ : Finset V).powersetCard b := by
    intro Γ hΓ
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hΓ).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hcover]
  apply Finset.sum_congr rfl
  intro A hA
  have hcard := (Finset.mem_powersetCard.mp hA).2
  congr 1
  ext Γ
  simp only [branchCardFamily, branchFamily, Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2 ▸ hcard⟩, h.2⟩

end Manuscript.SKBranching
