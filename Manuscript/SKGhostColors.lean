import Manuscript.SKGhostAdmissible

/-! The ghost does not receive an outside color; original colors are preserved. -/
noncomputable section
open scoped BigOperators
namespace Manuscript.SKGhostAdmissible
open SpinGlass SKActualEvaluator SKChargedMonomial SKAugmentFinset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every outside augmented vertex is an original vertex. -/
def originalOutside (A : Finset V) : Outside (distinguished A) → V
  | ⟨none,h⟩ => False.elim (h (none_mem_distinguished A))
  | ⟨some v,_h⟩ => v

def outsideColor {K : ℕ} (A : Finset V) (χ : V → Fin K) : Outside (distinguished A) → Fin K :=
  fun v => χ (originalOutside A v)

theorem totalColor_original {K : ℕ} (A : Finset V) (χ : V → Fin K) (hK : 0 < K)
    (v : V) (hv : v ∉ A) :
    totalColor (distinguished A) (outsideColor A χ) hK (some v) = χ v := by
  have hx : some v ∉ distinguished A := by simpa using hv
  simp [totalColor,hx,outsideColor,originalOutside]

/-- The exact outside-color set after augmentation. -/
theorem colors_augment {K : ℕ} (A : Finset V) (Γ : Finset (Finset V))
    (χ : V → Fin K) (hK : 0 < K) :
    colors id (distinguished A) (totalColor (distinguished A) (outsideColor A χ) hK) (augment Γ) =
      (SupportEvaluation.support id Γ \ A).image χ := by
  rw [colors,outside_augment,Finset.image_image]
  apply Finset.image_congr
  intro v hv
  exact totalColor_original A χ hK v (Finset.mem_sdiff.mp hv).2

/-- Color injectivity is preserved exactly, including unused vertices. -/
theorem colorful_augment {K : ℕ} (A : Finset V) (Γ : Finset (Finset V))
    (χ : V → Fin K) (hK : 0 < K) :
    Colorful id (distinguished A) (totalColor (distinguished A) (outsideColor A χ) hK) (augment Γ) ↔
      Set.InjOn χ (↑(SupportEvaluation.support id Γ \ A) : Set V) := by
  unfold Colorful
  rw [outside_augment]
  constructor
  · intro hc v hv w hw heq
    have hvA := (Finset.mem_sdiff.mp hv).2
    have hwA := (Finset.mem_sdiff.mp hw).2
    apply Option.some_injective V
    apply hc (Finset.mem_image.mpr ⟨v,hv,rfl⟩) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    rw [totalColor_original A χ hK v hvA,totalColor_original A χ hK w hwA]
    exact heq
  · intro hc x hx y hy heq
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    rw [totalColor_original A χ hK v (Finset.mem_sdiff.mp hv).2,
      totalColor_original A χ hK w (Finset.mem_sdiff.mp hw).2] at heq
    exact congrArg some (hc hv hw heq)

theorem colors_augment_branch {K : ℕ} (A : Finset V) (Γ : Finset (Finset V))
    (hbranch : SKGraph.branch id Γ = A) (χ : V → Fin K) (hK : 0 < K) :
    colors id (distinguished A) (totalColor (distinguished A) (outsideColor A χ) hK) (augment Γ) =
      (SKGraph.outside id Γ).image χ := by
  rw [colors_augment]
  simp only [SKGraph.outside,hbranch]

theorem colorful_augment_branch {K : ℕ} (A : Finset V) (Γ : Finset (Finset V))
    (hbranch : SKGraph.branch id Γ = A) (χ : V → Fin K) (hK : 0 < K) :
    Colorful id (distinguished A) (totalColor (distinguished A) (outsideColor A χ) hK) (augment Γ) ↔
      Set.InjOn χ (SKGraph.outside id Γ) := by
  rw [colorful_augment]
  simp only [SKGraph.outside,hbranch]

end Manuscript.SKGhostAdmissible
