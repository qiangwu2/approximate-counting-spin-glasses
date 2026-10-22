import Manuscript.SKCandidateLayout

/-! One fixed program computes all root tables and the primitive polynomial
from colors, endpoint charges, and the three supplied edge-weight matrices. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace Manuscript.SKCandidatePrimitives
open RestrictedMachine SKCandidateLayout SKBasisEncoding SpinGlass SKFastEvaluator

def program : Program := .seq SKRootCache.program
  (.seq SKCandidateLayout.program SKPrimitiveAssembly.program)
def operationBound (d : Layout) :=
  9*d.root.K+36+(d.root.B+d.root.N)*(SKRootCache.bodyCost d.root+5)+
  (9*(d.root.K+d.root.B)+100)+SKPrimitiveAssembly.operationBound d.root.N d.root.B d.root.K

theorem cache_bound (d : Layout) (a : ℕ) (ha : a<d.root.B+d.root.N)
    (S : Finset (Fin d.root.K)) (j : Fin d.root.N) :
    SKMemoUpdate.rowAddress d.root.N (d.root.cache+a*d.root.T) S j.val<d.primitiveBase := by
  have hb := (SKRootCache.row_bounds d.root.N d.root.K (d.root.cache+a*d.root.T) S j).2
  have hm := Nat.mul_le_mul_right d.root.T (show a+1≤d.root.B+d.root.N by omega)
  have hp := d.base_lt_primitive
  simp only [Nat.add_mul,Nat.one_mul] at hm
  change _<d.root.cache+a*d.root.T+d.root.T at hb
  unfold Layout.base at hp
  rw [Nat.add_mul] at hp
  omega

theorem prepared_data {V : Type*} [DecidableEq V] (d : Layout)
    (q : Fin d.root.B→ℕ) (branch : Fin d.root.B→V) (outside : Fin d.root.N→V)
    (χ : Fin d.root.N→Fin d.root.K) (f : Finset V→ℝ) (a s : State)
    (hi : SKRootCache.Invariant d.root χ
      (fun x y => pairWeight f (outside x) (outside y))
      (fun x y => pairWeight f (branch x) (outside y)) (d.root.B+d.root.N) a)
    (hr : PrimitiveRegisters d s) (hm : s.realMem=a.realMem) (hn : s.natMem=a.natMem)
    (hq : ∀x,a.natMem (d.chargeBase+x.val)=q x) :
    SKPrimitiveScan.Data q branch outside f (SKCountedExecution.rootCache branch outside χ f).value s := by
  rcases hr with ⟨h200,h201,h220,h253,h255,h256,h257,h273,h274,h275,h276,h282,h292⟩
  refine ⟨h200,h201,h220,h256,h273,h274,h275,h292,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x; rw [h282,hn]; exact hq x
  · intro x S j
    rw [h253,hm]
    exact SKRootCache.invariant_canonical d.root branch outside f χ a hi (.inl x) S j
  · intro x S j
    rw [h253,h276]
    exact cache_bound d x.val (by have := x.isLt; omega) S j
  · intro x S j
    rw [h253,hm]
    exact SKRootCache.invariant_canonical d.root branch outside f χ a hi (.inr x) S j
  · intro x S j
    rw [h253,h276]
    exact cache_bound d (d.root.B+x.val) (by have := x.isLt; omega) S j
  · intro x j
    rw [h255,hm,hi.branchRead]
    simp [pairWeight,Finset.pair_comm]
  · intro x j
    rw [h255,h276]
    have h := d.root.branch_lt x j
    have h1 := d.arena_le_base; have h2 := d.base_lt_primitive
    omega
  · intro x j; rw [h257,hm,hi.weightRead]
  · intro x j
    rw [h257,h276]
    have h := d.root.weight_lt x j
    have h1 := d.arena_le_base; have h2 := d.base_lt_primitive
    omega

theorem program_exec {V : Type*} [DecidableEq V] (p : Parameters) (i : RestrictedMachine.Inputs)
    (d : Layout) (q : Fin d.root.B→ℕ) (branch : Fin d.root.B→V) (outside : Fin d.root.N→V)
    (χ : Fin d.root.N→Fin d.root.K) (f : Finset V→ℝ) (s : State)
    (hs : SKRootCache.InputsReady d.root χ
      (fun x y => pairWeight f (outside x) (outside y))
      (fun x y => pairWeight f (branch x) (outside y)) s)
    (hl : SKCandidateLayout.Inputs d s)
    (hq : ∀x,s.natMem (d.chargeBase+x.val)=q x) :
    ∃ c t, Exec p i program s c t ∧ c≤operationBound d ∧ Shape d t ∧
      (∀y,t.realMem (d.primitiveBase+encode y)=(SKChargedExecution.primitives q branch outside χ f).coeff y) ∧
      t.natMem=s.natMem ∧ (∀address,address<d.root.arena → t.realMem address=s.realMem address) ∧
      (∀r,500≤r → t.natReg r=s.natReg r) ∧ (∀r,500≤r → t.realReg r=s.realReg r) := by
  obtain ⟨c0,a,he0,bc0,hi,hn0,hf0⟩ := SKRootCache.cache_execution p i d.root χ _ _ s hs
  have han (r : ℕ) (hr : 245≤r) := SKRootCache.natReg_frame p i s a c0 r he0 hr
  have hla : SKCandidateLayout.Inputs d a := by
    exact ⟨(han 400 (by omega)).trans hl.chargeBase,(han 401 (by omega)).trans hl.branchBase,
      (han 402 (by omega)).trans hl.metadataBase,(han 403 (by omega)).trans hl.ghost,
      (han 417 (by omega)).trans hl.retained⟩
  obtain ⟨c1,b,he1,bc1,hshape,hregs,hm1,hn1,hr1⟩ := SKCandidateLayout.program_exec p i d a hi.regs hla
  have hd := prepared_data d q branch outside χ f a b hi hregs hm1 hn1 (by intro x; rw [hn0]; exact hq x)
  obtain ⟨c2,t,he2,bc2,hst,hv⟩ := SKPrimitiveAssembly.actual_primitives_exec p i b q branch outside χ f hd
  refine ⟨c0+(c1+c2),t,Exec.seq he0 (Exec.seq he1 he2),by dsimp [operationBound]; omega,?_,?_,
    hst.2.1.trans (hn1.trans hn0),?_,?_,?_⟩
  · intro r hlo hhi
    rw [SKPrimitiveFrames.natReg_frame he2 (by omega)]
    exact hshape r hlo hhi
  · intro y
    have hh := hv y
    rw [hregs.2.2.2.2.2.2.2.2.2.2.1] at hh
    exact hh
  · intro address ha
    rw [hst.2.2,hm1,hf0 address ha]
    have hb : b.natReg 276=d.primitiveBase := hregs.2.2.2.2.2.2.2.2.2.2.1
    rw [hb]
    have h1 := d.arena_le_base; have h2 := d.base_lt_primitive
    omega
  · intro r hr
    rw [SKPrimitiveFrames.natReg_frame he2 (by omega),SKCandidateLayout.natReg_frame he1 (by omega),han r (by omega)]
  · intro r hr
    rw [SKPrimitiveFrames.realReg_frame he2 (by omega),hr1 r,
      SKRootCache.realReg_frame p i s a c0 r he0 (by omega)]
end Manuscript.SKCandidatePrimitives
