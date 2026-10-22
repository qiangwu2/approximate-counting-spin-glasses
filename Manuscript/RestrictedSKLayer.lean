import Manuscript.RestrictedSKMaskFold
import Manuscript.RestrictedSubsets

noncomputable section
namespace Manuscript.RestrictedSKLayer
open RestrictedMachine
private theorem state_ext {s t : State}
    (hR : s.realReg=t.realReg) (hN : s.natReg=t.natReg)
    (hmR : s.realMem=t.realMem) (hmN : s.natMem=t.natMem) : s=t := by
  cases s; cases t; simp_all

/-- Only physical/control globals and physical cache contents are invariant.
Candidate indices, generated-array addresses, and loop scratch are mutable. -/
structure Stable (P : State→Prop) : Prop where
  nat : ∀ s,P s → ∀ r v,r≠500 ∧ r≠501 ∧ r≠510 ∧ r≠512 ∧ r≠513 ∧ r≠570 → P (writeNatReg s r v)
  real : ∀ s,P s → ∀ r v,570≤r → P (writeRealReg s r v)
  memory : ∀ s,P s → ∀ j v,s.natReg 501≤j → P (writeNatMem s j v)

def SafeLayout (s : State) : Prop :=
  RestrictedCandidateLabelPreparation.Layout s ∧ s.natReg 501≤s.natReg 530

theorem mask_lt (N k j : ℕ) (hj : j<N.choose k) :
    (RestrictedSubsets.masks N k 0 1)[j]!<2^N := by
  have hi : j<(RestrictedSubsets.masks N k 0 1).length := by simpa using hj
  have hm : (RestrictedSubsets.masks N k 0 1)[j]!∈RestrictedSubsets.masks N k 0 1 := by
    simpa [List.getElem?_eq_getElem hi] using List.getElem_mem hi
  rw [RestrictedMaskBridge.support_masks_chosen] at hm
  obtain ⟨A,hA,he⟩:=List.mem_map.mp hm
  rw [←RestrictedMaskBridge.support_masks_chosen] at he
  rw [←he]
  exact (SKBasisEncoding.maskEquiv N A).isLt

def genCode : List Instruction := [.ncopy 200 500,.ncopy 201 574,.ncopy 204 576]
def setupCode : List Instruction :=
  [.ncopy 578 204,.nsub 577 204 576,.ncopy 530 204,.nconst 579 1,
   .nadd 531 530 500,.nadd 531 531 579,.nadd 532 531 500,.nadd 532 532 579,
   .nadd 533 532 500,.nadd 533 533 579,.nconst 575 0]
def program (candidate : Program) : RestrictedRecursiveMachine.Program 1 := .seq (.base (code genCode))
  (.seq RestrictedSubsets.program (.seq (.base (code setupCode)) (.base (RestrictedSKMaskFold.program candidate))))

def generated (params : Parameters) (input : Inputs) (s : State) : State :=
  RestrictedSubsets.output (runCode params input RestrictedSubsets.initCode (runCode params input genCode s))
    (RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1)
def ready (params : Parameters) (input : Inputs) (s : State) : State := runCode params input setupCode (generated params input s)

theorem output_stable {P : State→Prop} (stable : Stable P) (xs : List ℕ) :
    ∀ s,P s → s.natReg 501≤s.natReg 204 → P (RestrictedSubsets.output s xs) := by
  induction xs with
  | nil => intro s hs h;simpa using hs
  | cons x xs ih =>
      intro s hs h
      have hstep : RestrictedSubsets.output s [x]=writeNatReg (writeNatMem s (s.natReg 204) x) 204 (s.natReg 204+1) := by
        apply state_ext <;> simp [RestrictedSubsets.output,RestrictedSubsets.writeList,writeNatMem,writeNatReg]
      have hp : P (RestrictedSubsets.output s [x]) := by
        rw [hstep]
        exact stable.nat _ (stable.memory _ hs _ _ h) _ _ (by omega)
      have hh := ih _ hp (by simp;omega)
      simpa using hh

theorem ready_stable {P : State→Prop} (stable : Stable P) (params : Parameters) (input : Inputs)
    (s : State) (hs : P s) (hbase : s.natReg 501≤s.natReg 576) : P (ready params input s) := by
  have hg : P (runCode params input genCode s) := by
    simp only [genCode,runCode,step]
    exact stable.nat _ (stable.nat _ (stable.nat _ hs _ _ (by omega)) _ _ (by omega)) _ _ (by omega)
  have hinit : P (runCode params input RestrictedSubsets.initCode (runCode params input genCode s)) := by
    simp only [RestrictedSubsets.initCode,runCode,step]
    exact stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _ hg _ _ (by omega)) _ _ (by omega)) _ _ (by omega)) _ _ (by omega)) _ _ (by omega)
  have hout : P (generated params input s) := output_stable stable _ _ hinit
    (by simpa [genCode,RestrictedSubsets.initCode,runCode,step] using hbase)
  dsimp only [ready,setupCode,runCode,step]
  exact stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _
    (stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _ (stable.nat _ hout _ _ (by omega))
    _ _ (by omega)) _ _ (by omega)) _ _ (by omega)) _ _ (by omega)) _ _ (by omega))
    _ _ (by omega)) _ _ (by omega)) _ _ (by omega)) _ _ (by omega)) _ _ (by omega)

theorem ready_nat (params : Parameters) (input : Inputs) (s : State) :
    let t:=ready params input s
    t.natReg 500=s.natReg 500 ∧ t.natReg 513=s.natReg 513 ∧
    t.natReg 530=s.natReg 576+(s.natReg 500).choose (s.natReg 574) ∧
    t.natReg 576=s.natReg 576 ∧ t.natReg 577=(s.natReg 500).choose (s.natReg 574) ∧
    t.natReg 575=0 ∧ t.natReg 579=1 ∧
    t.natMem=RestrictedSubsets.writeList s.natMem (s.natReg 576)
      (RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1) := by
  simp [ready,generated,genCode,setupCode,RestrictedSubsets.initCode,runCode,step]

theorem ready_layout (params : Parameters) (input : Inputs) (s : State) :
    RestrictedCandidateLabelPreparation.Layout (ready params input s) := by
  constructor <;> simp [ready,generated,genCode,setupCode,RestrictedSubsets.initCode,runCode,step] <;> omega

theorem fold_stable {P : State→Prop} (stable : Stable P) :
    RestrictedSKMaskFold.Stable (fun s=>P s ∧ SafeLayout s) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro s hs r v hr
    refine ⟨stable.nat s hs.1 r v (by omega),?_⟩
    rcases hs.2 with ⟨⟨h1,h2,h3⟩,hfit⟩
    refine ⟨⟨?_,?_,?_⟩,?_⟩
    · simpa [show 500≠r by omega,show 530≠r by omega,show 531≠r by omega] using h1
    · simpa [show 500≠r by omega,show 531≠r by omega,show 532≠r by omega] using h2
    · simpa [show 500≠r by omega,show 532≠r by omega,show 533≠r by omega] using h3
    · simpa [show 501≠r by omega,show 530≠r by omega] using hfit
  · intro s hs r v hr
    exact ⟨stable.real s hs.1 r v (by omega),⟨⟨hs.2.1.branch_before,hs.2.1.outside_before,hs.2.1.charge_before⟩,hs.2.2⟩⟩
  · intro s hs r v hr
    refine ⟨stable.nat s hs.1 r v (by omega),?_⟩
    rcases hs.2 with ⟨⟨h1,h2,h3⟩,hfit⟩
    refine ⟨⟨?_,?_,?_⟩,?_⟩
    · simpa [show 500≠r by omega,show 530≠r by omega,show 531≠r by omega] using h1
    · simpa [show 500≠r by omega,show 531≠r by omega,show 532≠r by omega] using h2
    · simpa [show 500≠r by omega,show 532≠r by omega,show 533≠r by omega] using h3
    · simpa [show 501≠r by omega,show 530≠r by omega] using hfit
  · intro s hs v
    exact ⟨stable.real s hs.1 _ v (by omega),⟨⟨hs.2.1.branch_before,hs.2.1.outside_before,hs.2.1.charge_before⟩,hs.2.2⟩⟩

theorem program_exec (params : Parameters) (input : Inputs) (candidate : Program)
    (P : State→Prop) (stable : Stable P) (f : ℕ→ℕ→ℝ) (bound : ℕ→ℕ)
    (realized : ∀ s,P s ∧ SafeLayout s →
      RestrictedSKTrials.Prepared s → ∃ count t,Exec params input candidate s count t ∧
        RestrictedSKTrials.CandidateResult (fun s=>P s ∧ SafeLayout s) f bound s t count)
    (s : State) (hs : P s) (hbase : s.natReg 501≤s.natReg 576) :
    ∃ count t,RestrictedRecursiveMachine.Exec RestrictedSubsets.table params input (program candidate) s count t ∧ P t ∧
      count≤RestrictedSubsets.work (s.natReg 500) (s.natReg 574)+
        RestrictedSKMaskFold.cost bound (s.natReg 513)
          (fun j=>(RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1)[j]!)
          ((s.natReg 500).choose (s.natReg 574)) 0+56 ∧
      t.realReg 572=s.realReg 572+RestrictedSKMaskFold.value f (s.natReg 513)
          (fun j=>(RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1)[j]!)
          ((s.natReg 500).choose (s.natReg 574)) 0 ∧
      (∀ r,580<r ∨ r=500 ∨ r=501 ∨ r=510 ∨ r=512 ∨ r=513 ∨ r=570 ∨ r=573 ∨ r=574 ∨ r=576 →
        t.natReg r=s.natReg r) ∧
      (∀ r,573≤r → t.realReg r=s.realReg r) ∧
      (∀ j,j<s.natReg 576 → t.natMem j=s.natMem j) := by
  let a:=runCode params input genCode s
  have hg : RestrictedRecursiveMachine.Exec RestrictedSubsets.table params input RestrictedSubsets.program a
      (5+RestrictedSubsets.work (s.natReg 500) (s.natReg 574)) (generated params input s) := by
    simpa [a,generated,genCode,runCode,step] using RestrictedSubsets.program_exact params input a
  let b:=ready params input s
  obtain ⟨hN,hR,h530,h576,h577,h575,h579,hmem⟩ := ready_nat params input s
  have h501 : b.natReg 501=s.natReg 501 := by
    simp [b,ready,generated,genCode,setupCode,RestrictedSubsets.initCode,runCode,step]
  let masks : ℕ→ℕ := fun j=>(RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1)[j]!
  have hread : ∀ j,j<b.natReg 577 → b.natMem (b.natReg 576+j)=masks j := by
    intro j hj
    have hi : j<(RestrictedSubsets.masks (s.natReg 500) (s.natReg 574) 0 1).length := by rw [h577] at hj;simpa using hj
    rw [h576,hmem,RestrictedSubsets.writeList_get _ _ _ _ hi]
    simp [masks,List.getElem?_eq_getElem hi]
  obtain ⟨c,t,he,hp,hc,hv,hn,hr,hm⟩ := RestrictedSKMaskFold.program_exec params input candidate
    (fun s=>P s ∧ SafeLayout s) (fold_stable stable) f bound realized masks b
    ⟨ready_stable stable params input s hs hbase,ready_layout params input s,by
      change b.natReg 501≤b.natReg 530
      rw [h501,h530]
      omega⟩
    h579 h575 (by rw [h576,h577,h530]) hread
    (by intro j hj;rw [hN];exact mask_lt _ _ j (by rwa [h577] at hj))
  refine ⟨6+(5+RestrictedSubsets.work (s.natReg 500) (s.natReg 574)+(34+c)),t,?_,hp.1,?_,?_,?_,?_,?_⟩
  · have hh := RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base (exec_code params input genCode s))
      (RestrictedRecursiveMachine.Exec.seq hg (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base (exec_code params input setupCode (generated params input s))) (RestrictedRecursiveMachine.Exec.base he)))
    simpa [program,genCode,setupCode,codeCost,instrCost,a,b,ready] using hh
  · rw [hR,h577] at hc
    dsimp [masks] at hc
    omega
  · rw [hv,hR,h577]
    simp [b,ready,generated,genCode,setupCode,RestrictedSubsets.initCode,runCode,step,masks]
  · intro r h
    rw [hn r (by omega)]
    simp [b,ready,generated,genCode,setupCode,RestrictedSubsets.initCode,runCode,step,
      show r≠200 by omega,show r≠201 by omega,show r≠202 by omega,show r≠203 by omega,
      show r≠204 by omega,show r≠205 by omega,show r≠206 by omega,show r≠207 by omega,
      show r≠530 by omega,show r≠531 by omega,show r≠532 by omega,show r≠533 by omega,
      show r≠575 by omega,show r≠577 by omega,show r≠578 by omega,show r≠579 by omega]
  · intro r h
    rw [hr r h]
    simp [b,ready,generated,genCode,setupCode,RestrictedSubsets.initCode,runCode,step]
  · intro j hj
    rw [hm j (by rw [h530];omega),hmem,RestrictedSubsets.writeList_below _ _ _ _ hj]

end Manuscript.RestrictedSKLayer
