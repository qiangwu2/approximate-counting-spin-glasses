import Manuscript.RestrictedDeltaVector

noncomputable section
namespace Manuscript.SKRootStart
open RestrictedMachine

def preludeCode : List Instruction :=
  [.nmul 242 234 200,.nadd 242 242 231,.nsub 243 234 230,
   .ncopy 10 242,.ncopy 11 242,.ncopy 12 232,.nconst 13 1,
   .ncopy 14 200,.ncopy 15 243,.nle 244 230 234]
def program : Program := .seq (code preludeCode)
  (.branch 244 RestrictedDeltaVector.program (RestrictedArrays.program .copy))

def startValue (s : State) (j : ℕ) : ℝ :=
  if s.natReg 230≤s.natReg 234 then
    if j=s.natReg 234-s.natReg 230 then 1 else 0
  else s.realMem (s.natReg 231+s.natReg 234*s.natReg 200+j)

def Frame (s t : State) : Prop :=
  t.natMem=s.natMem ∧
  (∀a,(a<s.natReg 232 ∨ s.natReg 232+s.natReg 200≤a) → t.realMem a=s.realMem a) ∧
  (∀r,(200≤r ∧ r≤241) ∨ 244<r → t.natReg r=s.natReg r)

theorem execution (params : Parameters) (input : Inputs) (s : State)
    (hsource : s.natReg 234<s.natReg 230 →
      s.natReg 231+s.natReg 234*s.natReg 200+s.natReg 200≤s.natReg 232) :
    ∃c t,Exec params input program s c t ∧ c≤30*s.natReg 200+40 ∧
      (∀j,j<s.natReg 200 → t.realMem (s.natReg 232+j)=startValue s j) ∧ Frame s t := by
  let a := runCode params input preludeCode s
  have am : a.realMem=s.realMem := by simp [a,preludeCode,runCode,step]
  have an : a.natMem=s.natMem := by simp [a,preludeCode,runCode,step]
  have a10 : a.natReg 10=s.natReg 231+s.natReg 234*s.natReg 200 := by simp [a,preludeCode,runCode,step,Nat.add_comm]
  have a11 : a.natReg 11=s.natReg 231+s.natReg 234*s.natReg 200 := by simp [a,preludeCode,runCode,step,Nat.add_comm]
  have a12 : a.natReg 12=s.natReg 232 := by simp [a,preludeCode,runCode,step]
  have a14 : a.natReg 14=s.natReg 200 := by simp [a,preludeCode,runCode,step]
  have a15 : a.natReg 15=s.natReg 234-s.natReg 230 := by simp [a,preludeCode,runCode,step]
  have a13 : a.natReg 13=1 := by simp [a,preludeCode,runCode,step]
  have apre := exec_code params input preludeCode s
  have apc : codeCost preludeCode=27 := by simp [preludeCode,codeCost,instrCost]
  rw [apc] at apre
  have nf (t : State) (c : ℕ) (he : Exec params input program s c t)
      (r : ℕ) (hr : (200≤r ∧ r≤241) ∨ 244<r) : t.natReg r=s.natReg r := by
    apply he.natReg_frame
    simp [program,preludeCode,RestrictedDeltaVector.program,RestrictedDeltaVector.bodyCode,
      RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
      code,Program.All,Instruction.natDestination]
    omega
  by_cases hout : s.natReg 230≤s.natReg 234
  · obtain ⟨c,t,he,hc,hi⟩ := RestrictedDeltaVector.program_exec params input a a13
    have hb : a.natReg 244≠0 := by simp [a,preludeCode,runCode,step,hout]
    have hrun : Exec params input program s (27+(c+3)) t :=
      Exec.seq apre (Exec.branchNonzero hb he)
    refine ⟨_,t,hrun,?_,?_,hi.2.1.trans an,?_,nf t _ hrun⟩
    · rw [a14] at hc; omega
    · intro j hj
      rw [hi.1]
      simpa [a12,a14,a15,am,startValue,hout] using
        RestrictedDeltaVector.values (a.natReg 12) (a.natReg 15) (a.natReg 14) a.realMem j (by simpa [a14] using hj)
    · intro address haway
      rw [hi.1,RestrictedDeltaVector.frame]
      · rw [am]
      · intro j hj
        rw [a12]
        rw [a14] at hj
        omega
  · obtain ⟨c,t,he,hc,hi,hv⟩ := RestrictedArrays.pointwise_realized .copy params input a a13 (by
      intro i j hi hj
      rw [a10,a11,a12]
      have hs := hsource (by omega)
      rw [a14] at hi
      constructor <;> omega)
    have hb : a.natReg 244=0 := by simp [a,preludeCode,runCode,step,hout]
    have hrun : Exec params input program s (27+(c+3)) t :=
      Exec.seq apre (Exec.branchZero hb he)
    refine ⟨_,t,hrun,?_,?_,hi.2.1.trans an,?_,nf t _ hrun⟩
    · rw [a14] at hc; omega
    · intro j hj
      simpa [a12,a10,am,RestrictedArrays.Operation.eval,startValue,hout] using
        hv j (by simpa [a14] using hj)
    · intro address haway
      rw [hi.1,RestrictedArrays.loop_frame]
      · rw [am]
      · intro j hj
        rw [a12]
        rw [a14] at hj
        omega

end Manuscript.SKRootStart
