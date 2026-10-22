import Manuscript.RestrictedArrays
import Manuscript.SKBasisEncoding

noncomputable section
namespace Manuscript.SKRestrictedArrays
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding

/-- Contiguous representation of one coefficient array. -/
def Represents {b K : ℕ} (base : ℕ) (f : Coefficients b K) (memory : ℕ → ℝ) : Prop :=
  ∀ x, memory (base+encode x)=f x

theorem array_frame (op : RestrictedArrays.Operation) (params : Parameters) (input : Inputs)
    {s t : State} {count : ℕ} (he : Exec params input (RestrictedArrays.program op) s count t) :
    (∀ r, 15 ≤ r → t.natReg r=s.natReg r) ∧
    (∀ r, 3 ≤ r → t.realReg r=s.realReg r) ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_,?_⟩
  · intro r hr
    apply he.natReg_frame
    cases op <;> simp [RestrictedArrays.program, RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic, code, Program.All, Instruction.natDestination] <;> omega
  · intro r hr
    apply he.realReg_frame
    cases op <;> simp [RestrictedArrays.program, RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic, code, Program.All, Instruction.realDestination] <;> omega
  · apply he.natMem_frame
    cases op <;> simp [RestrictedArrays.program, RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic, code, Program.All, Instruction.writesNatMemory]

theorem coefficient_array (op : RestrictedArrays.Operation) {b K : ℕ}
    (params : Parameters) (input : Inputs) (s : State) (left right out : ℕ)
    (f g : Coefficients b K) (hleft : s.natReg 10=left) (hright : s.natReg 11=right)
    (hout : s.natReg 12=out) (hone : s.natReg 13=1)
    (hlength : s.natReg 14=(K+1)*2^K*6^b)
    (hf : Represents left f s.realMem) (hg : Represents right g s.realMem)
    (hs : ∀ i j, i < (K+1)*2^K*6^b → j < i → left+i ≠ out+j ∧ right+i ≠ out+j) :
    ∃ count t, Exec params input (RestrictedArrays.program op) s count t ∧
      count ≤ 30*((K+1)*2^K*6^b)+5 ∧
      Represents out (fun x => op.eval (s.realReg 4) (f x) (g x)) t.realMem ∧
      RestrictedArrays.Invariant op s (s.natReg 14) t := by
  obtain ⟨count,t,he,hc,hi,hv⟩ := RestrictedArrays.pointwise_realized op params input s hone (by
    simpa only [hleft,hright,hout,hlength] using hs)
  refine ⟨count,t,he,by simpa only [hlength] using hc,?_,hi⟩
  intro x
  have hx := hv (encode x) (by rw [hlength]; exact encode_lt x)
  simpa only [hleft,hright,hout,hf x,hg x] using hx

theorem preserved_outside (op : RestrictedArrays.Operation) (params : Parameters)
    (input : Inputs) {s t : State}
    (hi : RestrictedArrays.Invariant op s (s.natReg 14) t)
    (address : ℕ) (h : ∀ i, i < s.natReg 14 → address ≠ s.natReg 12+i) :
    t.realMem address=s.realMem address := by
  rw [hi.1]
  exact RestrictedArrays.loop_frame op _ _ _ _ _ _ _ h

/-- A uniform fill needs no assertion about the previous contents. -/
theorem fill_array {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base : ℕ) (hp : s.natReg 10=base) (hp' : s.natReg 11=base)
    (hp'' : s.natReg 12=base) (hone : s.natReg 13=1)
    (hlength : s.natReg 14=(K+1)*2^K*6^b) :
    ∃ count t, Exec params input (RestrictedArrays.program .fill) s count t ∧
      count ≤ 30*((K+1)*2^K*6^b)+5 ∧
      Represents base (fun _ : Basis b K => s.realReg 4) t.realMem ∧
      RestrictedArrays.Invariant .fill s (s.natReg 14) t := by
  obtain ⟨c,t,he,hc,hv,hi⟩ := coefficient_array .fill params input s base base base
    (fun x => s.realMem (base+encode x)) (fun x => s.realMem (base+encode x))
    hp hp' hp'' hone hlength (fun _ => rfl) (fun _ => rfl) (by intro i j hi hj; omega)
  exact ⟨c,t,he,hc,hv,hi⟩

end Manuscript.SKRestrictedArrays
