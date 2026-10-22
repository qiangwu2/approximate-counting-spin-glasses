import Manuscript.SKRootCacheBody

noncomputable section
namespace Manuscript.SKRootCache
open RestrictedMachine SKMemoUpdate SKMemoPass

structure Invariant (d : Layout) (χ : Fin d.N→Fin d.K)
    (w : Fin d.N→Fin d.N→ℝ) (branch : Fin d.B→Fin d.N→ℝ) (r : ℕ) (s : State) : Prop where
  regs : Registers d r s
  colorRead : ∀j,s.natMem (d.colorBase+j.val)=(χ j).val
  weightRead : ∀i j,s.realMem (d.weightBase+i.val*d.N+j.val)=w i j
  branchRead : ∀i j,s.realMem (d.branchBase+i.val*d.N+j.val)=branch i j
  computed : ∀a,a<r → ∀S j,s.realMem (rowAddress d.N (d.cache+a*d.T) S j.val)=
    SpinGlass.ColorPath.pathTable χ (start branch a) w S j

theorem step_invariant (params : Parameters) (input : Inputs) (d : Layout)
    (χ : Fin d.N→Fin d.K) (w : Fin d.N→Fin d.N→ℝ) (branch : Fin d.B→Fin d.N→ℝ)
    (r : ℕ) (s : State) (hs : Invariant d χ w branch r s) :
    ∃c t,Exec params input body s c t ∧ c≤bodyCost d ∧ Invariant d χ w branch (r+1) t ∧
      t.natMem=s.natMem ∧ (∀a,a<d.arena → t.realMem a=s.realMem a) := by
  obtain ⟨c,t,he,hb,hr,hn,hv,hf⟩ := body_execution params input d χ w branch r s
    hs.regs hs.colorRead hs.weightRead hs.branchRead
  refine ⟨c,t,he,hb,?_,hn,fun a ha => hf a (Or.inl ha)⟩
  refine ⟨hr,?_,?_,?_,?_⟩
  · intro j; rw [hn]; exact hs.colorRead j
  · intro i j; rw [hf _ (Or.inl (d.weight_lt i j))]; exact hs.weightRead i j
  · intro i j; rw [hf _ (Or.inl (d.branch_lt i j))]; exact hs.branchRead i j
  · intro a ha S j
    by_cases har : a=r
    · subst a; exact hv S j
    · rw [hf]
      · exact hs.computed a (by omega) S j
      · apply Or.inr
        have hrow := row_bounds d.N d.K (d.cache+a*d.T) S j
        have ha' : (a+1)*d.T≤r*d.T := Nat.mul_le_mul_right d.T (by omega)
        change d.cache≤rowAddress d.N (d.cache+a*d.T) S j.val ∧
          (rowAddress d.N (d.cache+a*d.T) S j.val<d.cache+r*d.T ∨ _)
        constructor
        · omega
        · apply Or.inl
          have hrlt : rowAddress d.N (d.cache+a*d.T) S j.val<d.cache+a*d.T+d.T := hrow.2
          simp only [Nat.add_mul,Nat.one_mul] at ha'
          omega

theorem loop_execution (params : Parameters) (input : Inputs) (d : Layout)
    (χ : Fin d.N→Fin d.K) (w : Fin d.N→Fin d.N→ℝ) (branch : Fin d.B→Fin d.N→ℝ)
    (n r : ℕ) (s : State) (hs : Invariant d χ w branch r s) :
    ∃c t,Repeats params input body n s c t ∧ c≤n*(bodyCost d+5)+3 ∧
      Invariant d χ w branch (r+n) t ∧ t.natMem=s.natMem ∧
      (∀a,a<d.arena → t.realMem a=s.realMem a) := by
  induction n generalizing r s with
  | zero => exact ⟨3,s,Repeats.zero body s,by simp,by simpa using hs,rfl,by simp⟩
  | succ n ih =>
    obtain ⟨c,m,he,hb,hm,hn,hf⟩ := step_invariant params input d χ w branch r s hs
    obtain ⟨e,t,het,hbt,ht,hnt,hft⟩ := ih (r+1) m hm
    refine ⟨c+e+5,t,Repeats.succ he het,?_,?_,hnt.trans hn,?_⟩
    · calc
        c+e+5≤bodyCost d+(n*(bodyCost d+5)+3)+5 := by omega
        _=(n+1)*(bodyCost d+5)+3 := by ring
    · convert ht using 1; omega
    · intro a ha; exact (hft a ha).trans (hf a ha)

end Manuscript.SKRootCache
