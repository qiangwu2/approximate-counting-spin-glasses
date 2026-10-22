import Manuscript.RestrictedArrays

noncomputable section
namespace Manuscript.RestrictedDeltaVector
open RestrictedMachine

/-- Fill the vector at register 12, of length 14, with the coordinate vector
whose nonzero coordinate is in register 15. Register 13 contains one. -/
def bodyCode : List Instruction :=
  [.neq 17 16 15,.natToReal 0 17,.storeReal 12 0,
   .nadd 12 12 13,.nadd 16 16 13]
def program : Program := .seq (code [.nconst 16 0]) (.repeat 14 (code bodyCode))

def memoryLoop (base target : ℕ) : ℕ → (ℕ→ℝ) → (ℕ→ℝ)
  | 0,m => m
  | n+1,m => Function.update (memoryLoop base target n m) (base+n)
      (if n=target then 1 else 0)

theorem frame (base target n address : ℕ) (m : ℕ→ℝ)
    (h : ∀j,j<n → address≠base+j) : memoryLoop base target n m address=m address := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [memoryLoop,Function.update_of_ne (h n (by omega))]
    exact ih (fun j hj => h j (by omega))

theorem values (base target n : ℕ) (m : ℕ→ℝ) :
    ∀j,j<n → memoryLoop base target n m (base+j)=if j=target then 1 else 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    by_cases h : j=n
    · subst j; simp [memoryLoop]
    · rw [memoryLoop,Function.update_of_ne (by omega : base+j≠base+n)]
      exact ih j (by omega)

def Invariant (s : State) (n : ℕ) (t : State) : Prop :=
  t.realMem=memoryLoop (s.natReg 12) (s.natReg 15) n s.realMem ∧
  t.natMem=s.natMem ∧ t.natReg 12=s.natReg 12+n ∧ t.natReg 16=n ∧
  (∀r,r≠12 → r≠16 → r≠17 → t.natReg r=s.natReg r) ∧
  (∀r,r≠0 → t.realReg r=s.realReg r)

theorem invariant_step (params : Parameters) (input : Inputs) (s t : State) (n : ℕ)
    (hone : s.natReg 13=1) (hi : Invariant s n t) :
    Invariant s (n+1) (runCode params input bodyCode t) := by
  rcases hi with ⟨hm,hn,hp,hc,hf,hr⟩
  have h1 : t.natReg 13=1 := (hf 13 (by decide) (by decide) (by decide)).trans hone
  have ht : t.natReg 15=s.natReg 15 := hf 15 (by decide) (by decide) (by decide)
  by_cases hnt : n=s.natReg 15
  all_goals
    simp [Invariant,bodyCode,runCode,step,writeRealMem,writeNatReg,writeRealReg,
      hm,hn,hp,hc,h1,ht,memoryLoop,hnt,Nat.add_assoc]
    refine ⟨?_,?_⟩
    · intro r h12 h16 h17
      simp [h12,h16,h17,hf r h12 h16 h17]
    · intro r h0
      simp [h0,hr r h0]

theorem program_exec (params : Parameters) (input : Inputs) (s : State)
    (hone : s.natReg 13=1) :
    ∃c t, Exec params input program s c t ∧ c≤23*s.natReg 14+6 ∧
      Invariant s (s.natReg 14) t := by
  let a := runCode params input [.nconst 16 0] s
  let F : ℕ→State := fun n => (runCode params input bodyCode)^[n] a
  have hi : ∀n,Invariant s n (F n) := by
    intro n
    induction n with
    | zero =>
      simp [F,a,runCode,step,Invariant,memoryLoop]
      intro r h12 h16 h17 he
      exact (h16 he).elim
    | succ n ih =>
      simpa only [F,Function.iterate_succ_apply'] using invariant_step params input s (F n) n hone ih
  have he := repeats_of_steps params input (code bodyCode) F (fun _=>codeCost bodyCode)
    (s.natReg 14) (by
      intro i hi
      simpa only [F,Function.iterate_succ_apply'] using exec_code params input bodyCode (F i))
  have hc : codeCost bodyCode=18 := by simp [bodyCode,codeCost,instrCost]
  refine ⟨1+((∑ _i ∈ Finset.range (s.natReg 14),codeCost bodyCode)+5*s.natReg 14+3+2),
    F (s.natReg 14),?_,?_,hi _⟩
  · exact Exec.seq (exec_code params input [.nconst 16 0] s) (Exec.repeat he)
  · simp [hc]; omega

end Manuscript.RestrictedDeltaVector
