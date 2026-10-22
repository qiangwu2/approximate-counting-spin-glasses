import Manuscript.RestrictedInputEncoding
import Manuscript.SKBasisEncoding
import Manuscript.SKColorEstimator

noncomputable section
namespace Manuscript.SKRawColorTape
open SpinGlass

/-- A coloring table is serialized as raw random words indexed by candidate
mask, trial, and original vertex. It supplies no graph sums or evaluated data. -/
def encode {N L R : ℕ} (χ : SKColorEstimator.Colors (Fin N) L R) (i : ℕ) : ℕ :=
  if hA : i/N/R<2^N then
    if hr : i/N%R<R then
      if hv : i%N<N then
        (χ ((SKBasisEncoding.maskEquiv N).symm ⟨i/N/R,hA⟩)
          ⟨i/N%R,hr⟩ ⟨i%N,hv⟩).val
      else 0
    else 0
  else 0

theorem at_color {N L R : ℕ} (hN : 0<N) (hR : 0<R)
    (χ : SKColorEstimator.Colors (Fin N) L R) (A : Finset (Fin N)) (r : Fin R) (v : Fin N) :
    encode χ ((SKBasisEncoding.maskEquiv N A).val*R*N+r.val*N+v.val)=
      (χ A r v).val := by
  have hdiv : ((SKBasisEncoding.maskEquiv N A).val*R*N+r.val*N+v.val)/N=
      (SKBasisEncoding.maskEquiv N A).val*R+r.val := by
    rw [show (SKBasisEncoding.maskEquiv N A).val*R*N+r.val*N+v.val=
      ((SKBasisEncoding.maskEquiv N A).val*R+r.val)*N+v.val by ring]
    simp [Nat.add_div,Nat.div_eq_of_lt v.isLt,Nat.mod_eq_of_lt v.isLt,hN]
  have hmod : ((SKBasisEncoding.maskEquiv N A).val*R*N+r.val*N+v.val)%N=v.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt v.isLt]
  have hrdiv : ((SKBasisEncoding.maskEquiv N A).val*R+r.val)/R=
      (SKBasisEncoding.maskEquiv N A).val := by
    simp [Nat.add_div,Nat.div_eq_of_lt r.isLt,Nat.mod_eq_of_lt r.isLt,hR]
  have hrmod : ((SKBasisEncoding.maskEquiv N A).val*R+r.val)%R=r.val := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt r.isLt]
  simp only [encode,hdiv,hmod,hrdiv,hrmod]
  simp only [(SKBasisEncoding.maskEquiv N A).isLt,r.isLt,v.isLt,↓reduceDIte,
    Fin.eta,Equiv.symm_apply_apply]

theorem input_tape {N M : ℕ} {P : Finset ℕ} (order : Fin M≃Model.Edge N P)
    (beta h epsilon delta : ℝ) (J : Model.Edge N P→ℝ) (tape : ℕ→ℕ) (i : ℕ) :
    (RestrictedInputEncoding.encode order beta h epsilon delta J tape).nat (2*M+2+i)=tape i := by
  have h0 : 2*M+2+i≠0 := by omega
  have h1 : 2*M+2+i≠1 := by omega
  have hfirst : ¬2*M+2+i-2<M := by omega
  have hsecond : ¬2*M+2+i-(M+2)<M := by omega
  simp [RestrictedInputEncoding.encode,h0,h1,hfirst,hsecond]

theorem input_color {N M L R : ℕ} {P : Finset ℕ} (hN : 0<N) (hR : 0<R)
    (order : Fin M≃Model.Edge N P) (beta h epsilon delta : ℝ) (J : Model.Edge N P→ℝ)
    (χ : SKColorEstimator.Colors (Fin N) L R) (A : Finset (Fin N)) (r : Fin R) (v : Fin N) :
    (RestrictedInputEncoding.encode order beta h epsilon delta J (encode χ)).nat
      (2*M+2+(RestrictedMaskBridge.encode A*R+r.val)*N+v.val)%(2*L)=(χ A r v).val := by
  rw [show 2*M+2+(RestrictedMaskBridge.encode A*R+r.val)*N+v.val=
    2*M+2+((SKBasisEncoding.maskEquiv N A).val*R*N+r.val*N+v.val) by
      simp only [RestrictedMaskBridge.encode];ring]
  rw [input_tape,at_color hN hR,Nat.mod_eq_of_lt (χ A r v).isLt]

end Manuscript.SKRawColorTape
