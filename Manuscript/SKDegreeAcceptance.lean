import Manuscript.RestrictedLoops
import Manuscript.RestrictedFrames
import Manuscript.SKBasisEncoding
import Manuscript.SKGhostAdmissible

/-! Uniform base-six acceptance test for the unique ghost coordinate. -/
noncomputable section
namespace Manuscript.SKDegreeAcceptance
open RestrictedMachine SKBasisEncoding

def good (digit ghost index : ℕ) : Prop :=
  if index=ghost then digit%2=0 else digit=4
instance (d g j : ℕ) : Decidable (good d g j) := inferInstanceAs (Decidable (if j=g then d%2=0 else d=4))
def badFold : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,_,_,_,a => a
  | n+1,x,g,j,a => badFold n (x/6) g (j+1) (a+if good (x%6) g j then 0 else 1)

def initCode : List Instruction :=
  [.nconst 323 0,.nconst 324 0,.nconst 325 6,.nconst 326 2,
   .nconst 327 4,.nconst 328 0,.nconst 329 1]
def headCode : List Instruction := [.nmod 330 320 325,.neq 331 323 322]
def ghostCode : List Instruction := [.nmod 332 330 326,.neq 333 332 328]
def otherCode : List Instruction := [.neq 333 330 327]
def tailCode : List Instruction :=
  [.nsub 334 329 333,.nadd 324 324 334,.ndiv 320 320 325,.nadd 323 323 329]
def body : Program := .seq (code headCode)
  (.seq (.branch 331 (code ghostCode) (code otherCode)) (code tailCode))
def program : Program := .seq (code initCode) (.repeat 321 body)
def next (p : Parameters) (i : Inputs) (s : State) : State :=
  let h := runCode p i headCode s
  runCode p i tailCode (if h.natReg 331=0 then runCode p i otherCode h else runCode p i ghostCode h)
def Constants (s : State) : Prop :=
  s.natReg 325=6 ∧ s.natReg 326=2 ∧ s.natReg 327=4 ∧ s.natReg 328=0 ∧ s.natReg 329=1

theorem next_exec (p : Parameters) (i : Inputs) (s : State) :
    ∃ c, Exec p i body s c (next p i s) ∧ c≤35 := by
  let h := runCode p i headCode s
  by_cases hz : h.natReg 331=0
  · refine ⟨8+(4+3+16),?_,by decide⟩
    exact Exec.seq (exec_code p i headCode s) (Exec.seq
      (Exec.branchZero hz (exec_code p i otherCode h))
      (by simpa [next,h,hz,tailCode,codeCost,instrCost] using exec_code p i tailCode (runCode p i otherCode h)))
  · refine ⟨8+(8+3+16),?_,by decide⟩
    exact Exec.seq (exec_code p i headCode s) (Exec.seq
      (Exec.branchNonzero hz (exec_code p i ghostCode h))
      (by simpa [next,h,hz,tailCode,codeCost,instrCost] using exec_code p i tailCode (runCode p i ghostCode h)))

theorem next_spec (p : Parameters) (i : Inputs) (s : State) (hs : Constants s) :
    let t := next p i s
    t.natReg 320=s.natReg 320/6 ∧ t.natReg 322=s.natReg 322 ∧
    t.natReg 323=s.natReg 323+1 ∧
    t.natReg 324=s.natReg 324+(if good (s.natReg 320%6) (s.natReg 322) (s.natReg 323) then 0 else 1) ∧
    Constants t := by
  rcases hs with ⟨h6,h2,h4,h0,h1⟩
  by_cases hg : s.natReg 323=s.natReg 322
  · by_cases hv : s.natReg 320%2=0 <;>
      simp [next,headCode,ghostCode,otherCode,tailCode,runCode,step,Constants,good,hg,hv,h6,h2,h4,h0,h1]
  · by_cases hv : s.natReg 320%6=4 <;>
      simp [next,headCode,ghostCode,otherCode,tailCode,runCode,step,Constants,good,hg,hv,h6,h2,h4,h0,h1]

theorem iterate_value (p : Parameters) (i : Inputs) (n : ℕ) (s : State) (hs : Constants s) :
    (iterateState (next p i) n s).natReg 324=
      badFold n (s.natReg 320) (s.natReg 322) (s.natReg 323) (s.natReg 324) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    have hh := next_spec p i s hs
    rw [iterateState,ih _ hh.2.2.2.2,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1]
    rfl

theorem acceptance_realized (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i program s c t ∧ c≤40*s.natReg 321+12 ∧
      t.natReg 324=badFold (s.natReg 321) (s.natReg 320) (s.natReg 322) 0 0 := by
  let a := runCode p i initCode s
  have ha : Constants a := by simp [a,Constants,initCode,runCode,step]
  obtain ⟨c,hc,bc⟩ := repeats_bounded p i body (next p i) 35 (next_exec p i) (a.natReg 321) a
  refine ⟨7+(c+2),iterateState (next p i) (a.natReg 321) a,
    Exec.seq (exec_code p i initCode s) (Exec.repeat hc),?_,?_⟩
  · have hb : a.natReg 321=s.natReg 321 := by simp [a,initCode,runCode,step]
    rw [hb] at bc; omega
  · rw [iterate_value p i _ a ha]
    simp [a,initCode,runCode,step]

theorem badFold_zero_iff (n x g j a : ℕ) :
    badFold n x g j a=0 ↔ a=0 ∧ ∀ r<n, good (x/6^r%6) g (j+r) := by
  induction n generalizing x j a with
  | zero => simp [badFold]
  | succ n ih =>
    rw [badFold,ih]
    have hshift (r : ℕ) : x/6/6^r=x/6^(r+1) := by rw [Nat.div_div_eq_div_mul,pow_succ]; congr 1; omega
    simp only [Nat.add_eq_zero]
    constructor
    · rintro ⟨⟨ha,hhead⟩,htail⟩
      refine ⟨ha,?_⟩
      intro r hr
      cases r with
      | zero => simpa using (show good (x%6) g j from by split_ifs at hhead <;> simp_all)
      | succ r => simpa [hshift,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using htail r (by omega)
    · rintro ⟨ha,hall⟩
      refine ⟨⟨ha,?_⟩,?_⟩
      · have hh := hall 0 (by omega)
        simpa using (show (if good (x%6) g j then 0 else 1)=0 from by simpa using hh)
      · intro r hr
        simpa [hshift,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hall (r+1) (by omega)

theorem encoded_acceptance_iff {b : ℕ} (d : Fin b → SpinGlass.CappedDegree) (g : Fin b) :
    badFold b (degreeEquiv b d).val g.val 0 0=0 ↔
      ∀ i : Fin b, if i=g then
        d i=SpinGlass.CappedDegree.ofNat 0 ∨ d i=SpinGlass.CappedDegree.ofNat 2 ∨ d i=SpinGlass.CappedDegree.ofNat 4
      else d i=SpinGlass.CappedDegree.ofNat 4 := by
  rw [badFold_zero_iff]
  simp only [true_and,Nat.zero_add]
  constructor
  · intro h i
    have hi := h i.val i.isLt
    rw [degree_digit] at hi
    have hd := (d i).isLt
    by_cases hg : i=g
    · simp only [hg,if_true]
      have hp : (d i).val%2=0 := by simpa [good,hg] using hi
      have hv : (d i).val=0 ∨ (d i).val=2 ∨ (d i).val=4 := by omega
      rcases hv with hv|hv|hv
      · left; apply SpinGlass.CappedDegree.ext_val; simpa [SpinGlass.rho,hg] using hv
      · right; left; apply SpinGlass.CappedDegree.ext_val; simpa [SpinGlass.rho,hg] using hv
      · right; right; apply SpinGlass.CappedDegree.ext_val; simpa [SpinGlass.rho,hg] using hv
    · simp only [hg,if_false]
      have hgv : i.val≠g.val := fun hh => hg (Fin.ext hh)
      have hv : (d i).val=4 := by simpa [good,hgv] using hi
      apply SpinGlass.CappedDegree.ext_val; simpa [SpinGlass.rho,hg] using hv
  · intro h r hr
    let i : Fin b := ⟨r,hr⟩
    have hi := h i
    change good ((degreeEquiv b d).val/6^i.val%6) g.val i.val
    rw [degree_digit]
    by_cases hg : i=g
    · simp only [hg,if_true] at hi
      rcases hi with hi|hi|hi <;> simp [good,hg,hi]
    · rw [if_neg hg] at hi
      simp [good,Fin.ext_iff,hg,hi]

theorem memory_frame {p : Parameters} {i : Inputs} {s t : State} {c : ℕ}
    (h : Exec p i program s c t) : t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  constructor
  · apply h.realMem_frame
    simp [program,body,initCode,headCode,ghostCode,otherCode,tailCode,code,Program.All,Instruction.writesRealMemory]
  · apply h.natMem_frame
    simp [program,body,initCode,headCode,ghostCode,otherCode,tailCode,code,Program.All,Instruction.writesNatMemory]

theorem natReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i program s c t) (hr : r<320 ∨ 334<r ∨ r=321 ∨ r=322) : t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [program,body,initCode,headCode,ghostCode,otherCode,tailCode,code,Program.All,Instruction.natDestination]
  omega

theorem realReg_frame {p : Parameters} {i : Inputs} {s t : State} {c r : ℕ}
    (h : Exec p i program s c t) : t.realReg r=s.realReg r := by
  apply h.realReg_frame
  simp [program,body,initCode,headCode,ghostCode,otherCode,tailCode,code,Program.All,Instruction.realDestination]
end Manuscript.SKDegreeAcceptance
