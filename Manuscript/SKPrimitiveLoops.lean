import Manuscript.SKPrimitiveScan

/-! Complete bounded loops over runtime primitive-key spaces. -/
noncomputable section
namespace Manuscript.SKPrimitiveLoops
open RestrictedMachine SKBasisEncoding SKPrimitiveScan SKPrimitiveTerms
open SpinGlass SKCoefficient SKCountedExecution
open scoped BigOperators

def body (pair : Bool) : Program := if pair then pairBody else cycleBody
def limit (pair : Bool) (b K : ℕ) : ℕ := if pair then (b*b)*2^K else 2^K
def cost (pair : Bool) (N b K : ℕ) : ℕ :=
  if pair then 27*N+58*K+18*b+224 else N*(27*N+18)+58*K+142

def entry {V : Type*} [DecidableEq V] {N b K : ℕ} (pair : Bool)
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) : ℕ → Coefficients b K :=
  if pair then pairEntry q branch outside f cache else cycleEntry outside f cache

def cumulative {b K : ℕ} (old : Coefficients b K) (values : ℕ → Coefficients b K) (n : ℕ) : Coefficients b K :=
  fun y => old y+∑ j∈Finset.range n,values j y

theorem step_exec {V : Type*} [DecidableEq V] {N b K : ℕ} (pair : Bool)
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (old : Coefficients b K) (index : ℕ)
    (hs : Data q branch outside f cache s) (hi : index<limit pair b K) (hindex : s.natReg 290=index)
    (hm : ∀ y,s.realMem (s.natReg 276+encode y)=old y) :
    ∃ count t, Exec p i (body pair) s count t ∧ count≤cost pair N b K ∧
      Stable s t ∧ t.natReg 290=index+1 ∧
      (∀ y,t.realMem (s.natReg 276+encode y)=old y+entry pair q branch outside f cache index y) := by
  cases pair with
  | false => exact cycle_body_exec p i s q branch outside f cache old index hs hi hindex hm
  | true => exact pair_body_exec p i s q branch outside f cache old index hs hi hindex hm

theorem repeats_exec {V : Type*} [DecidableEq V] {N b K : ℕ} (pair : Bool)
    (p : Parameters) (i : Inputs) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (old : Coefficients b K)
    (n index : ℕ) (s : State) (hs : Data q branch outside f cache s)
    (hi : index+n≤limit pair b K) (hindex : s.natReg 290=index)
    (hm : ∀ y,s.realMem (s.natReg 276+encode y)=cumulative old (entry pair q branch outside f cache) index y) :
    ∃ count t, Repeats p i (body pair) n s count t ∧ count≤n*(cost pair N b K+5)+3 ∧
      Stable s t ∧ t.natReg 290=index+n ∧
      (∀ y,t.realMem (s.natReg 276+encode y)=cumulative old (entry pair q branch outside f cache) (index+n) y) := by
  induction n generalizing index s with
  | zero => exact ⟨3,s,Repeats.zero _ _,by simp,stable_refl s,by simpa using hindex,by simpa using hm⟩
  | succ n ih =>
    obtain ⟨c,a,hea,bc,hstable,hidx,hcoeff⟩ := step_exec pair p i s q branch outside f cache
      (cumulative old (entry pair q branch outside f cache) index) index hs (by omega) hindex hm
    have ha : ∀ y,a.realMem (a.natReg 276+encode y)=cumulative old (entry pair q branch outside f cache) (index+1) y := by
      intro y
      rw [hstable.1 276 (by simp [stableRegs]),hcoeff]
      simp [cumulative,Finset.sum_range_succ,_root_.add_assoc]
    obtain ⟨d,t,het,bd,htstable,htidx,htcoeff⟩ := ih (index+1) a (hs.stable hstable) (by omega) hidx ha
    refine ⟨c+d+5,t,Repeats.succ hea het,?_,hstable.trans htstable,by omega,?_⟩
    · calc
        c+d+5≤cost pair N b K+(n*(cost pair N b K+5)+3)+5 := by omega
        _ =(n+1)*(cost pair N b K+5)+3 := by ring
    · intro y
      have hh := htcoeff y
      rw [hstable.1 276 (by simp [stableRegs])] at hh
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

def initCode (pair : Bool) : List Instruction := if pair then pairInit else cycleInit
def boundRegister (pair : Bool) : ℕ := if pair then 291 else 274
def program (pair : Bool) : Program := .seq (code (initCode pair)) (.repeat (boundRegister pair) (body pair))

theorem init_stable {V : Type*} [DecidableEq V] {N b K : ℕ} (pair : Bool)
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (hs : Data q branch outside f cache s) :
    Stable s (runCode p i (initCode pair) s) := by
  refine ⟨?_,?_,?_⟩
  · intro r hr
    simp only [stableRegs,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst r <;>
      cases pair <;> simp [initCode,pairInit,cycleInit,runCode,step,hs.one]
  · cases pair <;> simp [initCode,pairInit,cycleInit,runCode,step]
  · intro address hlt
    cases pair <;> simp [initCode,pairInit,cycleInit,runCode,step]

theorem program_exec {V : Type*} [DecidableEq V] {N b K : ℕ} (pair : Bool)
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (old : Coefficients b K)
    (hs : Data q branch outside f cache s) (hm : ∀ y,s.realMem (s.natReg 276+encode y)=old y) :
    ∃ count t, Exec p i (program pair) s count t ∧ count≤limit pair b K*(cost pair N b K+5)+15 ∧
      Stable s t ∧
      (∀ y,t.realMem (s.natReg 276+encode y)=cumulative old (entry pair q branch outside f cache) (limit pair b K) y) := by
  let a := runCode p i (initCode pair) s
  have hstable : Stable s a := init_stable pair p i s q branch outside f cache hs
  have hi : a.natReg 290=0 := by cases pair <;> simp [a,initCode,pairInit,cycleInit,runCode,step]
  have ha : ∀ y,a.realMem (a.natReg 276+encode y)=cumulative old (entry pair q branch outside f cache) 0 y := by
    intro y
    cases pair <;> simpa [a,initCode,pairInit,cycleInit,runCode,step,cumulative] using hm y
  obtain ⟨c,t,he,bc,htstable,_,hvalue⟩ := repeats_exec pair p i q branch outside f cache old
    (limit pair b K) 0 a (hs.stable hstable) (by simp) hi ha
  have hbound : a.natReg (boundRegister pair)=limit pair b K := by
    cases pair <;> simp [a,initCode,boundRegister,limit,pairInit,cycleInit,runCode,step,hs.branches,hs.colors]
  have hcode : codeCost (initCode pair)≤10 := by cases pair <;> decide
  refine ⟨codeCost (initCode pair)+(c+2),t,
    Exec.seq (exec_code p i (initCode pair) s) (Exec.repeat (by rwa [hbound])),by omega,hstable.trans htstable,?_⟩
  intro y
  have hh := hvalue y
  rw [hstable.1 276 (by simp [stableRegs])] at hh
  simpa using hh

theorem pair_sum {V : Type*} [DecidableEq V] {N b K : ℕ}
    (q : Fin b → ℕ) (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) :
    (∑ j∈Finset.range ((b*b)*2^K),pairEntry q branch outside f cache j)=
      ∑ a,∑ c,∑ S,pairTerm q branch outside f cache a c S := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [pairEntry,Fin.isLt,dif_pos]
  change (∑ j : Fin ((b*b)*2^K),pairTerm q branch outside f cache
    ((pairEquiv b K).symm j).1.1 ((pairEquiv b K).symm j).1.2 ((pairEquiv b K).symm j).2)=_
  rw [(pairEquiv b K).symm.sum_comp (fun key => pairTerm q branch outside f cache key.1.1 key.1.2 key.2)]
  simp [Fintype.sum_prod_type]

theorem cycle_sum {V : Type*} [DecidableEq V] {N b K : ℕ}
    (outside : Fin N → V) (f : Finset V → ℝ) (cache : Root (Fin N) b → Table (Fin N) K) :
    (∑ j∈Finset.range (2^K),cycleEntry outside f cache j)=∑ S,cycleTerm outside f cache S := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [cycleEntry,Fin.isLt,dif_pos]
  change (∑ j : Fin (2^K),cycleTerm outside f cache ((maskEquiv K).symm j))=_
  exact (maskEquiv K).symm.sum_comp (cycleTerm outside f cache)
end Manuscript.SKPrimitiveLoops
