import Manuscript.RestrictedInteractions
import Manuscript.RestrictedMaskBridge

/-! Raw input format: each coupling record contains its interaction label,
order, and real coupling. No evaluated weight, approximation, or computed
control parameter is supplied in the input. The remaining natural words form
the saved random tape. -/
noncomputable section
namespace Manuscript.RestrictedInputEncoding
open RestrictedMachine InputPreparation Model

/-- The enumeration only specifies the order of raw coupling records. The
machine is uniform in this order and does not contain it in its program. -/
def encode {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) : Inputs where
  nat i := if i=0 then N else if i=1 then M else
    if hi : i-2 < M then (order ⟨i-2,hi⟩).val.card else
    if hi : i-(M+2) < M then RestrictedMaskBridge.encode (order ⟨i-(M+2),hi⟩).val else
    tape (i-(2*M+2))
  real i := if i=0 then beta else
    if hi : i-1 < M then J (order ⟨i-1,hi⟩) else
    if i=M+1 then h else if i=M+2 then epsilon else if i=M+3 then delta else 0

@[simp] theorem nat_size {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) :
    (encode order beta h epsilon delta J tape).nat 0=N := by simp [encode]
@[simp] theorem nat_count {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) :
    (encode order beta h epsilon delta J tape).nat 1=M := by simp [encode]
@[simp] theorem real_beta {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) :
    (encode order beta h epsilon delta J tape).real 0=beta := by simp [encode]

theorem nat_order {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) (j : Fin M) :
    (encode order beta h epsilon delta J tape).nat (j.val+2)=(order j).val.card := by
  simp [encode,j.isLt]

theorem nat_mask {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) (j : Fin M) :
    (encode order beta h epsilon delta J tape).nat (M+2+j.val)=RestrictedMaskBridge.encode (order j).val := by
  have h0 : M+2+j.val ≠ 0 := by omega
  have h1 : M+2+j.val ≠ 1 := by omega
  have hfirst : ¬(M+2+j.val-2 < M) := by omega
  simp [encode,h1,hfirst,j.isLt]

theorem real_coupling {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) (j : Fin M) :
    (encode order beta h epsilon delta J tape).real (j.val+1)=J (order j) := by
  simp [encode,j.isLt]

theorem real_fields {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ) :
    (encode order beta h epsilon delta J tape).real (M+1)=h ∧
    (encode order beta h epsilon delta J tape).real (M+2)=epsilon ∧
    (encode order beta h epsilon delta J tape).real (M+3)=delta := by
  simp [encode]

theorem tableEdge_physical {N M : ℕ} {P : Finset ℕ} (order : Fin M ≃ Edge N P)
    (beta h epsilon delta : ℝ) (J : Edge N P → ℝ) (tape : ℕ → ℕ)
    (a : ℕ → ℝ) (params : Parameters) (hparams : ∀ p ∈ P, params p=a p) (j : Fin M) :
    RestrictedInteractions.tableEdge params (encode order beta h epsilon delta J tape) j.val =
      prepareEdge N (order j).val.card (a (order j).val.card) beta (J (order j)) := by
  simp only [RestrictedInteractions.tableEdge,nat_size,nat_order,real_beta,real_coupling]
  rw [hparams _ (mem_physicalEdges.mp (order j).property)]

end Manuscript.RestrictedInputEncoding
