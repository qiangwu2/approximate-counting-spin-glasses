import Manuscript.RestrictedFrames
import Manuscript.RestrictedInteractions

noncomputable section
namespace Manuscript.RestrictedInputCache
open RestrictedMachine

def setup : List Instruction :=
  [.ncopy 400 501,.nconst 401 0,.nconst 404 2,.nconst 405 1,
   .nadd 402 501 404,.nconst 403 1,.rcopy 510 507]
def body : List Instruction :=
  [.readNatInput 406 402,.storeNat 401 406,.loadReal 511 403,.radd 510 510 511,
   .nadd 401 401 405,.nadd 402 402 405,.nadd 403 403 404]
def program : Program := .seq (code setup) (.repeat 400 (code body))

def Invariant (input : Inputs) (M : ℕ) (base : ℝ) (memory : ℕ → ℝ) (i : ℕ) (s : State) : Prop :=
  s.natReg 401=i ∧ s.natReg 402=M+2+i ∧ s.natReg 403=2*i+1 ∧
  s.natReg 404=2 ∧ s.natReg 405=1 ∧ s.realMem=memory ∧
  s.realReg 510=base+∑ j∈Finset.range i,memory (2*j+1) ∧
  (∀ j, j < i → s.natMem j=input.nat (M+2+j))

theorem body_invariant (params : Parameters) (input : Inputs) (M : ℕ) (base : ℝ)
    (memory : ℕ → ℝ) (i : ℕ) (s : State) (hs : Invariant input M base memory i s) :
    Invariant input M base memory (i+1) (runCode params input body s) := by
  rcases hs with ⟨h401,h402,h403,h404,h405,hm,hr,hn⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals try { simp [body,runCode,step,writeNatMem,h401,h402,h403,h404,h405,hm,hr] <;> omega }
  · simp [body,runCode,step,writeNatMem,h401,h402,h403,h404,h405,hm,hr,Finset.sum_range_succ]
    ring
  · intro j hj
    by_cases hji : j=i
    · subst j
      simp [body,runCode,step,writeNatMem,h401,h402,h403,h404,h405]
    · simp [body,runCode,step,writeNatMem,h401,h402,h403,h404,h405,hji,hn j (by omega)]

theorem repeats_exec (params : Parameters) (input : Inputs) (M : ℕ) (base : ℝ)
    (memory : ℕ → ℝ) (steps i : ℕ) (s : State) (hs : Invariant input M base memory i s) :
    ∃ t, Repeats params input (code body) steps s (30*steps+3) t ∧
      Invariant input M base memory (i+steps) t := by
  induction steps generalizing i s with
  | zero => exact ⟨s,Repeats.zero _ _,by simpa using hs⟩
  | succ steps ih =>
    let u := runCode params input body s
    have hu : Exec params input (code body) s 25 u := exec_code _ _ _ _
    obtain ⟨t,ht,hi⟩ := ih (i+1) u (body_invariant params input M base memory i s hs)
    refine ⟨t,?_,?_⟩
    · convert Repeats.succ hu ht using 1 <;> omega
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

theorem program_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ t, Exec params input program s (30*s.natReg 501+17) t ∧
      (∀ j, j < s.natReg 501 → t.natMem j=input.nat (s.natReg 501+2+j)) ∧
      t.realReg 510=s.realReg 507+∑ j∈Finset.range (s.natReg 501),s.realMem (2*j+1) ∧
      t.realMem=s.realMem := by
  let u := runCode params input setup s
  have hu : Exec params input (code setup) s 12 u := exec_code _ _ _ _
  have hi : Invariant input (s.natReg 501) (s.realReg 507) s.realMem 0 u := by
    simp [Invariant,u,setup,runCode,step]
  obtain ⟨t,ht,hend⟩ := repeats_exec params input (s.natReg 501) (s.realReg 507)
    s.realMem (s.natReg 501) 0 u hi
  have hcount : u.natReg 400=s.natReg 501 := by simp [u,setup,runCode,step]
  refine ⟨t,?_,by simpa using hend.2.2.2.2.2.2.2,by simpa using hend.2.2.2.2.2.2.1,hend.2.2.2.2.2.1⟩
  have hp := Exec.repeat (show Repeats params input (code body) (u.natReg 400) u
    (30*s.natReg 501+3) t by simpa only [hcount] using ht)
  convert Exec.seq hu hp using 1 <;> first | rfl | omega

theorem program_frame (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input program s c t) :
    (∀ r, 407 ≤ r → t.natReg r=s.natReg r) ∧
    (∀ r, r ≠ 510 → r ≠ 511 → t.realReg r=s.realReg r) := by
  refine ⟨?_,?_⟩
  · intro r hr
    apply he.natReg_frame
    simp [program,setup,body,code,Program.All,Instruction.natDestination]; omega
  · intro r h510 h511
    apply he.realReg_frame
    simp [program,setup,body,code,Program.All,Instruction.realDestination,Ne.symm h510,Ne.symm h511]

end Manuscript.RestrictedInputCache
