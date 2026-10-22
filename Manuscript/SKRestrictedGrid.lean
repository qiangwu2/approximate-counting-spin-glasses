import Manuscript.SKRestrictedKernels

/-! A uniform rectangular dot-product traversal used for outside cycles.
The inner and outer bounds, row strides, and cache pointers are runtime data. -/
noncomputable section
namespace Manuscript.SKRestrictedGrid
open RestrictedMachine SKRestrictedKernels
open scoped BigOperators

def tailCode : List Instruction := [.nadd 0 0 6, .nadd 1 1 7]
def body : Program := .seq dotProgram (code tailCode)
def program : Program := .repeat 5 body

def Invariant (s : State) (n : ℕ) (t : State) : Prop :=
  t.realMem=s.realMem ∧ t.natMem=s.natMem ∧
  t.natReg 0=s.natReg 0+n*(s.natReg 4*s.natReg 2+s.natReg 6) ∧
  t.natReg 1=s.natReg 1+n*(s.natReg 4*s.natReg 3+s.natReg 7) ∧
  (∀ r, 2≤r → t.natReg r=s.natReg r) ∧
  (∀ r, 4≤r → t.realReg r=s.realReg r) ∧
  t.realReg 0=s.realReg 0+∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (s.natReg 4),
    s.realMem (s.natReg 0+i*(s.natReg 4*s.natReg 2+s.natReg 6)+j*s.natReg 2)*
    s.realMem (s.natReg 1+i*(s.natReg 4*s.natReg 3+s.natReg 7)+j*s.natReg 3)

theorem body_realized (params : Parameters) (input : Inputs) {s t : State} {n : ℕ}
    (hi : Invariant s n t) :
    ∃ u, Exec params input body t (27*s.natReg 4+13) u ∧ Invariant s (n+1) u := by
  rcases hi with ⟨hm,hn,h0,h1,hf,hr,hv⟩
  obtain ⟨u,he,hu⟩ := dot_realized params input t
  rcases hu with ⟨um,un,u0,u1,uf,ur,uv⟩
  let v := runCode params input tailCode u
  have un2 (r : ℕ) (hr : 2≤r) : u.natReg r=s.natReg r :=
    (uf r (by omega) (by omega)).trans (hf r hr)
  refine ⟨v,?_,?_⟩
  · have ht : Exec params input (code tailCode) u 8 v := by
      simpa [v,tailCode,codeCost,instrCost] using exec_code params input tailCode u
    rw [hf 4 (by omega)] at he
    convert Exec.seq he ht using 1 <;> first | rfl | omega
  · dsimp [Invariant]
    simp only [v,tailCode,runCode,step,writeNatReg_realMem,writeNatReg_natMem,
      writeNatReg_natReg,writeNatReg_realReg]
    norm_num
    refine ⟨um.trans hm,un.trans hn,?_,?_,?_,?_,?_⟩
    · rw [u0,h0,hf 4 (by omega),hf 2 (by omega),un2 6 (by omega)]
      ring
    · rw [u1,h1,hf 4 (by omega),hf 3 (by omega),un2 7 (by omega)]
      ring
    · intro r hr2
      have hr0 : r ≠ 0 := by omega
      have hr1 : r ≠ 1 := by omega
      simp [hr0,hr1,un2 r hr2]
    · intro r hr4
      exact (ur r hr4).trans (hr r hr4)
    · rw [uv,hv,hm,h0,h1,hf 4 (by omega),hf 2 (by omega),hf 3 (by omega),
        Finset.sum_range_succ]
      ring

theorem grid_repeats (params : Parameters) (input : Inputs) (s : State) (remaining : ℕ) :
    ∀ n t, Invariant s n t →
    ∃ u, Repeats params input body remaining t (remaining*(27*s.natReg 4+18)+3) u ∧
      Invariant s (n+remaining) u := by
  induction remaining with
  | zero =>
    intro n t ht
    exact ⟨t,by simpa using Repeats.zero (params:=params) (input:=input) body t,by simpa using ht⟩
  | succ k ih =>
    intro n t ht
    obtain ⟨u,hu,hui⟩ := body_realized params input ht
    obtain ⟨v,hv,hvi⟩ := ih (n+1) u hui
    refine ⟨v,?_,?_⟩
    · convert Repeats.succ hu hv using 1 <;> ring
    · convert hvi using 1 <;> omega

theorem grid_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ t, Exec params input program s (s.natReg 5*(27*s.natReg 4+18)+5) t ∧
      Invariant s (s.natReg 5) t := by
  have hs : Invariant s 0 s := by simp [Invariant]
  obtain ⟨t,he,hi⟩ := grid_repeats params input s (s.natReg 5) 0 s hs
  refine ⟨t,?_,by simpa using hi⟩
  convert Exec.repeat he using 1 <;> first | rfl | omega

end Manuscript.SKRestrictedGrid
