import Manuscript.RestrictedArrays
import Manuscript.RestrictedMaskBridge

noncomputable section
open scoped BigOperators
namespace Manuscript.SKPhysicalLookup
open RestrictedMachine

/-- Read-only lookup in the serialized physical edge cache. Natural380 is
an edge mask and381 is the edge count. The result is real380. -/
def initCode : List Instruction :=
  [.nconst 382 0,.nconst 383 2,.nconst 384 1,.rconst 380 0]
def bodyCode : List Instruction :=
  [.loadNat 386 382,.neq 387 386 380,.nmul 385 383 382,
   .loadReal 381 385,.natToReal 382 387,.rmul 381 381 382,
   .radd 380 380 381,.nadd 382 382 384]
def program : Program := .seq (code initCode) (.repeat 381 (code bodyCode))

def value (s : State) (n : ℕ) : ℝ :=
  ∑i∈Finset.range n,if s.natMem i=s.natReg 380 then s.realMem (2*i) else 0

def Invariant (s : State) (n : ℕ) (t : State) : Prop :=
  t.realReg 380=value s n ∧ t.natReg 382=n ∧ t.natReg 383=2 ∧ t.natReg 384=1 ∧
  t.realMem=s.realMem ∧ t.natMem=s.natMem ∧
  (∀r,r≠382 → r≠383 → r≠384 → r≠385 → r≠386 → r≠387 → t.natReg r=s.natReg r) ∧
  (∀r,r≠380 → r≠381 → r≠382 → t.realReg r=s.realReg r)

theorem invariant_step (params : Parameters) (input : Inputs) (s t : State) (n : ℕ)
    (hi : Invariant s n t) : Invariant s (n+1) (runCode params input bodyCode t) := by
  rcases hi with ⟨hv,hn,h2,h1,hm,hmem,hf,hr⟩
  have ht : t.natReg 380=s.natReg 380 := hf 380 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hval : value s (n+1)=value s n+(if s.natMem n=s.natReg 380 then s.realMem (2*n) else 0) := by
    simp [value,Finset.sum_range_succ]
  by_cases hmatch : s.natMem n=s.natReg 380
  all_goals
    simp [Invariant,bodyCode,runCode,step,writeRealReg,writeNatReg,
      hv,hn,h2,h1,hm,hmem,ht,hmatch,hval]
    refine ⟨?_,?_⟩
    · intro r h382 h383 h384 h385 h386 h387
      simp [h382,h385,h386,h387,hf r h382 h383 h384 h385 h386 h387]
    · intro r h380 h381 h382
      simp [h380,h381,h382,hr r h380 h381 h382]

theorem execution (params : Parameters) (input : Inputs) (s : State) :
    ∃t,Exec params input program s (34*s.natReg 381+9) t ∧
      Invariant s (s.natReg 381) t := by
  let a := runCode params input initCode s
  let F : ℕ→State := fun n => (runCode params input bodyCode)^[n] a
  have hi : ∀n,Invariant s n (F n) := by
    intro n
    induction n with
    | zero =>
      simp [F,a,initCode,runCode,step,Invariant,value]
      constructor
      · intro r h382 h383 h384 h385 h386 h387
        simp [h382,h383,h384]
      · intro r h380 h381 h382
        simp [h380]
    | succ n ih =>
      simpa only [F,Function.iterate_succ_apply'] using invariant_step params input s (F n) n ih
  have he := repeats_of_steps params input (code bodyCode) F (fun _=>codeCost bodyCode)
    (s.natReg 381) (by intro i _; simpa only [F,Function.iterate_succ_apply'] using exec_code params input bodyCode (F i))
  have hc : codeCost bodyCode=29 := by simp [bodyCode,codeCost,instrCost]
  refine ⟨F (s.natReg 381),?_,hi _⟩
  have hr : Exec params input (.repeat 381 (code bodyCode)) a
      ((∑ _i ∈ Finset.range (s.natReg 381),codeCost bodyCode)+5*s.natReg 381+3+2)
      (F (s.natReg 381)) := Exec.repeat (by simpa [F,a,initCode,runCode,step] using he)
  have hrun := Exec.seq (exec_code params input initCode s) hr
  convert hrun using 1 <;> first | rfl | simp [initCode,codeCost,instrCost,hc]; omega

/-- A lookup returns the unique cached value when the ordinary input labels
are injective. This condition concerns the input serialization, not a
computed result or a machine oracle. -/
theorem value_at {M : ℕ} (s : State) (key : Fin M→ℕ) (weight : Fin M→ℝ)
    (hk : Function.Injective key) (hn : ∀i,s.natMem i.val=key i)
    (hw : ∀i,s.realMem (2*i.val)=weight i) (e : Fin M) (he : s.natReg 380=key e) :
    value s M=weight e := by
  rw [value,←Fin.sum_univ_eq_sum_range]
  simp_rw [hn,hw,he]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b hb hbe
    simp [show key b≠key e from fun h => hbe (hk h)]
  · simp

end Manuscript.SKPhysicalLookup
