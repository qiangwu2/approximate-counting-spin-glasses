import Manuscript.SKCandidateCoefficientOutput
import Manuscript.SKRestrictedCandidateSharpCost

/-! Every colorful coefficient remains available in the actual output array.
Summing its three accepted ghost-degree coordinates gives precisely the
original graph sum f_A^χ(k,S), simultaneously for all k and S. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
namespace Manuscript.SKColorfulCoefficientOutput
open SpinGlass SKActualEvaluator SKChargedMonomial SKGhostAdmissible
open RestrictedMachine SKCandidateLayout SKBasisEncoding

/-- Relabeling leaves each charged degree and color-set coordinate unchanged. -/
theorem evaluate_labels {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {b K : ℕ} (A : Finset V)
    (lab : Fin b → Option V) (out : W → Option V)
    (hb : Function.Injective lab) (ho : Function.Injective out)
    (hbr : ∀v,v∈distinguished A ↔ ∃i,lab i=v)
    (hor : ∀v,v∉distinguished A ↔ ∃i,out i=v)
    (ψ : Option V → Fin K) (f : Finset (Option V)→ℝ) :
    SKChargedExecution.evaluate (fun i=>if lab i=none then 0 else 1)
      lab out (ψ ∘ out) f =
    SKBranchReindex.pull (SKCanonicalLabels.branchEquiv (distinguished A) lab hb hbr)
      (SKChargedExecution.evaluate (SKChargedPrimitiveCounts.endpointCharge (distinguished A))
        (branch (distinguished A)) (Subtype.val : Outside (distinguished A)→Option V) (ψ ∘ Subtype.val) f) := by
  let B := distinguished A
  let eb := SKCanonicalLabels.branchEquiv B lab hb hbr
  let eo := SKCanonicalLabels.outsideEquiv B out ho hor
  have hbv : branch B ∘ eb=lab := funext (SKCanonicalLabels.branchEquiv_value B lab hb hbr)
  have hov : (Subtype.val : Outside B→Option V) ∘ eo=out := rfl
  have hq : SKChargedPrimitiveCounts.endpointCharge B ∘ eb=
      (fun i=>if lab i=none then 0 else 1) := by
    funext i
    simp only [Function.comp_apply,SKChargedPrimitiveCounts.endpointCharge]
    rw [SKCanonicalLabels.branchEquiv_value]
  have hsep : ∀a,branch B a∉Set.range (Subtype.val : Outside B→Option V) := by
    intro a h
    obtain ⟨v,hv⟩ := h
    exact v.property (hv ▸ branch_mem B a)
  have hout := SKOutsideReindex.evaluate eo (SKChargedPrimitiveCounts.endpointCharge B ∘ eb)
    (branch B ∘ eb) (Subtype.val : Outside B→Option V) (ψ ∘ Subtype.val) f
  have hbranch := SKPrimitiveReindex.evaluate_map eb (SKChargedPrimitiveCounts.endpointCharge B)
    (branch B) (Subtype.val : Outside B→Option V) (branch_injective B) (outside_injective B) hsep (ψ ∘ Subtype.val) f
  simpa only [hq,hbv,hov,Function.comp_assoc] using hout.trans hbranch.symm

theorem accepted_pull {b c K : ℕ} (e : Fin b≃Fin c) (g : Fin b)
    (f : SKCoefficient.Coefficients c K) (k : Fin (K+1)) (S : Finset (Fin K)) :
    (∑d∈SKExtractionCell.accepted g,SKBranchReindex.pull e f (target k S d))=
      ∑d∈SKExtractionCell.accepted (e g),f (target k S d) := by
  classical
  symm
  apply Finset.sum_bij (fun d _=>d ∘ e)
  · intro d hd
    exact (SKTrialReindex.accepted_map e g d).mpr hd
  · intro d hd v hv he
    funext j
    obtain ⟨j,rfl⟩ := e.surjective j
    exact congrFun he j
  · intro d hd
    refine ⟨d ∘ e.symm,?_,?_⟩
    · apply (SKTrialReindex.accepted_map e g _).mp
      simpa only [Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id] using hd
    · funext j; simp
  · intro d hd
    simp [SKBranchReindex.pull,SKBranchReindex.coordinate,target,Function.comp_def]

def extendColor {V : Type*} {K : ℕ} (hK : 0<K) (χ : V→Fin K) : Option V→Fin K :=
  fun v=>v.elim ⟨0,hK⟩ χ

theorem extendColor_outside {V : Type*} [Fintype V] [DecidableEq V] {K : ℕ}
    (A : Finset V) (hK : 0<K) (χ : V→Fin K) :
    extendColor hK χ ∘ (Subtype.val : Outside (distinguished A)→Option V)=outsideColor A χ := by
  funext v
  rcases v with ⟨v,hv⟩
  cases v with
  | none => exact False.elim (hv (none_mem_distinguished A))
  | some v => rfl

/-- Original colorful graph sums, valid for any injective enumeration of the
branch and outside vertices used by the machine. -/
theorem coefficient_original {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {b K : ℕ} (A : Finset V)
    (lab : Fin b→Option V) (out : W→Option V)
    (hb : Function.Injective lab) (ho : Function.Injective out)
    (hbr : ∀v,v∈distinguished A ↔ ∃i,lab i=v)
    (hor : ∀v,v∉distinguished A ↔ ∃i,out i=v)
    (g : Fin b) (hg : lab g=none) (χ : V→Fin K) (hK : 0<K)
    (h : ℝ) (w : Finset V→ℝ) (k : Fin (K+1)) (S : Finset (Fin K)) :
    (∑d∈SKExtractionCell.accepted g,
      SKChargedExecution.evaluate (fun i=>if lab i=none then 0 else 1)
        lab out (extendColor hK χ ∘ out) (SKAugmentFinset.edgeWeight h w) (target k S d))=
    ∑Γ∈SKBranching.branchFamily A,
      if Γ.card=k.val ∧ (SKGraph.outside id Γ).image χ=S ∧ Set.InjOn χ (SKGraph.outside id Γ)
      then FieldExpansion.graphWeight id h w Γ else 0 := by
  rw [evaluate_labels A lab out hb ho hbr hor,accepted_pull]
  have hg' : branch (distinguished A) (SKCanonicalLabels.branchEquiv (distinguished A) lab hb hbr g)=none :=
    (SKCanonicalLabels.branchEquiv_value (distinguished A) lab hb hbr g).trans hg
  rw [SKRestrictedExtraction.accepted_eq A _ hg',extendColor_outside]
  exact SKGhostCoefficient.coefficient_original A χ hK h w k S

/-- Read the three accepted degree states from the retained output array. -/
def readout {b K : ℕ} (base : ℕ) (ghost : Fin b) (memory : ℕ→ℝ)
    (k : Fin (K+1)) (S : Finset (Fin K)) : ℝ :=
  ∑d∈SKExtractionCell.accepted ghost,memory (base+encode (target k S d))

/-- Proposition 4.4's complete colorful output, with the manuscript's precise
local exponential factors. The premises describe source labels, colors and
edge weights only; every path table and coefficient array is actually built. -/
theorem end_to_end {N : ℕ} (p : Parameters) (input : RestrictedMachine.Inputs)
    (d : Layout) (L : ℕ) (hL : 1≤L) (hK : d.root.K=2*L)
    (A : Finset (Fin N)) (hn : d.root.N≤N) (hbcard : d.root.B=A.card+1)
    (lab : Fin d.root.B→Option (Fin N)) (out : Fin d.root.N→Option (Fin N))
    (hb : Function.Injective lab) (ho : Function.Injective out)
    (hbr : ∀v,v∈distinguished A ↔ ∃j,lab j=v)
    (hor : ∀v,v∉distinguished A ↔ ∃j,out j=v)
    (hg : lab d.ghost=none) (χ : Fin N→Fin d.root.K) (h : ℝ) (w : Finset (Fin N)→ℝ)
    (s : State)
    (hs : SKRootCache.InputsReady d.root (extendColor (by omega : 0<d.root.K) χ ∘ out)
      (fun x y=>SKFastEvaluator.pairWeight (SKAugmentFinset.edgeWeight h w) (out x) (out y))
      (fun x y=>SKFastEvaluator.pairWeight (SKAugmentFinset.edgeWeight h w) (lab x) (out y)) s)
    (hl : SKCandidateLayout.Inputs d s)
    (hq : ∀x,s.natMem (d.chargeBase+x.val)=(if lab x=none then 0 else 1))
    (hw : ∀a c,s.realMem (d.branchWeightBase+a.val*d.root.B+c.val)=
      SKFastEvaluator.pairWeight (SKAugmentFinset.edgeWeight h w) (lab a) (lab c)) :
    ∃ count t,Exec p input SKRestrictedCandidateExecution.program s count t ∧
      count≤360000*(N+2*L+1)^6*16^L*36^A.card ∧
      ∀ (k : Fin (d.root.K+1)) (S : Finset (Fin d.root.K)),
        readout d.base d.ghost t.realMem k S=
          ∑Γ∈SKBranching.branchFamily A,
            if Γ.card=k.val ∧ (SKGraph.outside id Γ).image χ=S ∧
              Set.InjOn χ (SKGraph.outside id Γ)
            then FieldExpansion.graphWeight id h w Γ else 0 := by
  have hkpos : 0<d.root.K := by omega
  obtain ⟨count,t,he,hc,hv,hcoeff,hrest⟩ := SKCandidateCoefficientOutput.candidate_exec p input d
    (by omega) (fun j=>if lab j=none then 0 else 1) lab out (extendColor hkpos χ ∘ out)
    (SKAugmentFinset.edgeWeight h w) s hs hl hq hw
  refine ⟨count,t,he,hc.trans (SKRestrictedCandidateSharpCost.candidate_bound d N L A.card
    hn hbcard (by simpa using Finset.card_le_univ A) hK),?_⟩
  intro k S
  unfold readout
  unfold SKRestrictedArrays.Represents at hcoeff
  simp_rw [hcoeff]
  exact coefficient_original A lab out hb ho hbr hor d.ghost hg χ hkpos h w k S

/-- The raw degree vector associated with a selected even ghost state. -/
def acceptedDegree {b : ℕ} (g : Fin b) (v : ℕ) : Fin b→CappedDegree :=
  fun i=>if i=g then CappedDegree.ofNat v else CappedDegree.ofNat 4

theorem accepted_three {b : ℕ} (g : Fin b) :
    SKExtractionCell.accepted g={acceptedDegree g 0,acceptedDegree g 2,acceptedDegree g 4} := by
  classical
  ext d
  simp only [SKExtractionCell.accepted,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hd
    have he (v : ℕ) (hv : d g=CappedDegree.ofNat v) : d=acceptedDegree g v := by
      funext i
      by_cases hi : i=g
      · subst i; simpa [acceptedDegree] using hv
      · simpa [acceptedDegree,hi] using hd i
    have hg : d g=CappedDegree.ofNat 0 ∨ d g=CappedDegree.ofNat 2 ∨ d g=CappedDegree.ofNat 4 := by
      simpa using hd g
    exact hg.elim (fun h=>Or.inl (he 0 h))
      (fun h=>h.elim (fun h=>Or.inr (Or.inl (he 2 h))) (fun h=>Or.inr (Or.inr (he 4 h))))
  · rintro (rfl|rfl|rfl) i <;> by_cases hi : i=g <;> simp [acceptedDegree,hi]

/-- Each colorful sum is a fixed three-entry readout, without any additional
sum over graph objects or a search through the coefficient array. -/
theorem readout_three {b K : ℕ} (base : ℕ) (g : Fin b) (memory : ℕ→ℝ)
    (k : Fin (K+1)) (S : Finset (Fin K)) :
    readout base g memory k S=
      memory (base+encode (target k S (acceptedDegree g 0)))+
      memory (base+encode (target k S (acceptedDegree g 2)))+
      memory (base+encode (target k S (acceptedDegree g 4))) := by
  classical
  have hn (a b : ℕ) (h : CappedDegree.ofNat a≠CappedDegree.ofNat b) :
      acceptedDegree g a≠acceptedDegree g b := by
    intro he
    apply h
    simpa [acceptedDegree] using congrFun he g
  have h02 := hn 0 2 (by decide)
  have h04 := hn 0 4 (by decide)
  have h24 := hn 2 4 (by decide)
  simp [readout,accepted_three,h02,h04,h24,add_assoc]

end Manuscript.SKColorfulCoefficientOutput
