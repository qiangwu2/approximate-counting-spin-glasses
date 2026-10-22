import Manuscript.UniformPhysicalMass
import Manuscript.SKBranchingFinite

/-! Exact transport between untyped pair graphs and the physical edge subtype. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.UniformSKTransport
open SpinGlass.Expansion Manuscript.Model Manuscript.UniformGraphMass
open Manuscript.FieldExpansion

/-- Forget only the membership proof; the finite graph itself is preserved. -/
def forget (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P)) : Finset (Finset (Fin N)) :=
  Γ.image Subtype.val

theorem forget_injective (N : ℕ) (P : Finset ℕ) : Function.Injective (forget N P) :=
  Finset.image_injective Subtype.val_injective

@[simp] theorem forget_card (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P)) :
    (forget N P Γ).card = Γ.card := Finset.card_image_of_injective Γ Subtype.val_injective

@[simp] theorem forget_degree (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P)) (v : Fin N) :
    degree id (forget N P Γ) v = degree Subtype.val Γ v := by
  unfold degree forget
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ Subtype.val_injective

@[simp] theorem forget_boundary (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P)) :
    boundary id (forget N P Γ) = boundary Subtype.val Γ := by
  ext v
  simp [boundary]

@[simp] theorem forget_branch (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P)) :
    SKGraph.branch id (forget N P Γ) = SKGraph.branch Subtype.val Γ := by
  ext v
  simp [SKGraph.branch]

@[simp] theorem forget_product (N : ℕ) (P : Finset ℕ) (Γ : Finset (Edge N P))
    (r : Finset (Fin N) → ℝ) :
    (∏ e ∈ forget N P Γ, r e) = ∏ e ∈ Γ, r e.val := by
  exact Finset.prod_image (fun _ _ _ _ h => Subtype.val_injective h)

theorem image_physical_univ (N : ℕ) (P : Finset ℕ) :
    (Finset.univ : Finset (Edge N P)).image Subtype.val = physicalEdges N P := by
  ext e
  simp

theorem forget_powerset (N : ℕ) (P : Finset ℕ) :
    (Finset.univ : Finset (Edge N P)).powerset.image (forget N P) =
      (physicalEdges N P).powerset := by
  calc
    _ = ((Finset.univ : Finset (Edge N P)).image Subtype.val).powerset :=
      Finset.powerset_image.symm
    _ = _ := congrArg Finset.powerset (image_physical_univ N P)

theorem physicalEdges_sk (N : ℕ) :
    physicalEdges N {2} = (Finset.univ : Finset (Fin N)).powersetCard 2 := by
  ext e
  simp [physicalEdges]

theorem forget_pairGraphs (N : ℕ) :
    (Finset.univ : Finset (Edge N {2})).powerset.image (forget N {2}) =
      SKBranching.pairGraphs (Fin N) := by
  rw [forget_powerset, physicalEdges_sk]
  rfl

/-- Transport arbitrary subfamilies, so both the edge and branching cutoffs
commute with the subtype representation. -/
theorem graphMass_transport (N : ℕ) (P : Finset ℕ)
    (Q : Finset (Finset (Fin N)) → Prop) [DecidablePred Q]
    (h : ℝ) (r : Finset (Fin N) → ℝ) :
    graphMass id ((physicalEdges N P).powerset.filter Q) h r =
      graphMass Subtype.val ((Finset.univ : Finset (Edge N P)).powerset.filter
        (fun Γ => Q (forget N P Γ))) h (fun e => r e.val) := by
  conv_lhs => rw [← forget_powerset N P, Finset.filter_image]
  unfold graphMass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro Γ hΓ
    rw [forget_boundary, forget_product]
  · exact fun _ _ _ _ heq => forget_injective N P heq

theorem pair_graphMass_transport (N : ℕ) (h : ℝ) (r : Finset (Fin N) → ℝ) :
    graphMass id (SKBranching.pairGraphs (Fin N)) h r =
      graphMass Subtype.val (Finset.univ : Finset (Edge N {2})).powerset h (fun e => r e.val) := by
  have ht := graphMass_transport N {2} (fun _ => True) h r
  simpa only [physicalEdges_sk, Finset.filter_true, SKBranching.pairGraphs] using ht

/-- The uniform mass bound in the untyped pair-graph representation used by
the SK branching analysis. -/
theorem pair_comparison_mass (N : ℕ) (hN : 2 ≤ N) {v h rho : ℝ}
    (hv : 0 < v) (hv1 : v < 1)
    (hfield : |h| ≤ rho * (N : ℝ) ^ (-(1 / 4 : ℝ))) :
    graphMass id (SKBranching.pairGraphs (Fin N)) h (fun _ => v / N) ≤
      UniformMixedMass.massConstant {2} (fun _ => 1) v rho := by
  rw [pair_graphMass_transport]
  have heq : (fun _ : Edge N {2} => v / (N : ℝ)) =
      MixedCoefficient.comparisonWeight N {2} (fun _ => 1) v := by
    funext e
    have he : e.val.card = 2 := by simpa using edge_order_mem e
    simp [MixedCoefficient.comparisonWeight, he]
  rw [heq]
  apply UniformMixedMass.uniform_graphical_mass N {2} (fun _ => 1)
    (by simp) (by simp) (by simp) (by simpa using hN) hv _ hfield
  simpa only [MixedThreshold.thresholdSquared_sk (fun _ => 1) rfl] using hv1

end Manuscript.UniformSKTransport
