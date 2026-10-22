import Manuscript.SKPhysicalMatrix
import Manuscript.SKGhostPhysicalEvaluation

noncomputable section
namespace Manuscript.SKPhysicalPairCanonical
open RestrictedMachine Model RestrictedMaskBridge SKPhysicalMatrix SKAugmentFinset

/-- Physical labels0..N−1 and the explicitly appended ghost sentinelN. -/
def vertex (N u : ℕ) : Option (Fin N) := if h:u<N then some ⟨u,h⟩ else none

theorem pairValue_eq {N M : ℕ} (order : Fin M≃Edge N {2})
    (a : ℕ→ℝ) (beta h : ℝ) (J : Edge N {2}→ℝ) (s : State)
    (hN : s.natReg 500=N) (hM : s.natReg 501=M)
    (hm : s.realReg 504=Real.tanh h)
    (hE : ∀i:Fin M,s.natMem i.val=encode (order i).val)
    (hW : ∀i:Fin M,s.realMem (2*i.val)=Real.tanh (coefficient N {2} a beta J (order i)))
    (u v : ℕ) (hu : u≤N) (hv : v≤N) :
    pairValue s u v=SpinGlass.SKFastEvaluator.pairWeight
      (edgeWeight h (SKGhostCoefficient.inputWeight N a beta J)) (vertex N u) (vertex N v) := by
  have hkey : Function.Injective (fun i:Fin M=>encode (order i).val) := by
    intro i j he
    apply order.injective
    apply Subtype.ext
    apply (SKBasisEncoding.maskEquiv N).injective
    exact Fin.ext he
  by_cases hgu : u=N
  · subst u
    simp [pairValue,SKPhysicalPair.value,writeNatReg,hN,hm,vertex,
      SpinGlass.SKFastEvaluator.pairWeight,edgeWeight]
  by_cases hgv : v=N
  · subst v
    simp [pairValue,SKPhysicalPair.value,writeNatReg,hN,hm,vertex,
      SpinGlass.SKFastEvaluator.pairWeight,edgeWeight]
  have hu' : u<N := by omega
  have hv' : v<N := by omega
  let x : Fin N := ⟨u,hu'⟩
  let y : Fin N := ⟨v,hv'⟩
  have hvertexu : vertex N u=some x := by simp [vertex,hu',x]
  have hvertexv : vertex N v=some y := by simp [vertex,hv',y]
  rw [hvertexu,hvertexv]
  unfold SpinGlass.SKFastEvaluator.pairWeight
  have hlift : ({some x,some y} : Finset (Option (Fin N)))=liftEdge {x,y} := by simp [liftEdge]
  rw [hlift,edgeWeight_lift]
  by_cases huv : u=v
  · subst v
    have hxy : x=y := Fin.ext rfl
    simp [pairValue,SKPhysicalPair.value,writeNatReg,hN,hgu,SKGhostCoefficient.inputWeight,
      hxy,mem_physicalEdges]
  · have hxy : x≠y := by intro he; exact huv (congrArg Fin.val he)
    let e : Edge N {2} := ⟨{x,y},by simp [mem_physicalEdges,hxy]⟩
    have hencode : encode e.val=2^u+2^v := by
      simp [e,encode_sum,hxy,x,y]
    let t := writeNatReg s 380 (2^u+2^v)
    have hlookup := SKPhysicalLookup.value_at t (fun i:Fin M=>encode (order i).val)
      (fun i=>Real.tanh (coefficient N {2} a beta J (order i))) hkey
      (by simpa [t] using hE) (by simpa [t] using hW) (order.symm e) (by
        simp [t,hencode])
    have hval : pairValue s u v=Real.tanh (coefficient N {2} a beta J e) := by
      simpa [pairValue,SKPhysicalPair.value,writeNatReg,hN,hM,hgu,hgv,huv,
        SKPhysicalLookup.value,t] using hlookup
    rw [hval]
    exact (SKGhostCoefficient.inputWeight_physical N a beta J e).symm

end Manuscript.SKPhysicalPairCanonical
