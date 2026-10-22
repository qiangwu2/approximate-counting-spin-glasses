import Manuscript.SKPhysicalMatrix

noncomputable section
namespace Manuscript.SKPhysicalMatrix
open RestrictedMachine

theorem natReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (he : Exec params input program s c t)
    (hr : r<130 ∨ (132<r ∧ r<380) ∨ (396≤r ∧ r<420) ∨ 430<r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [program,initCode,body,preludeCode,tailCode,
    SKPhysicalPair.program,SKPhysicalPair.checkCode,SKPhysicalPair.physical,
    SKPhysicalPair.firstCode,SKPhysicalPair.secondCode,SKPhysicalPair.lookupCode,
    IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
    SKPhysicalLookup.program,SKPhysicalLookup.initCode,SKPhysicalLookup.bodyCode,
    code,Program.All,Instruction.natDestination]
  omega

theorem realReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (he : Exec params input program s c t) (hr : 391≤r) : t.realReg r=s.realReg r := by
  apply he.realReg_frame
  simp [program,initCode,body,preludeCode,tailCode,
    SKPhysicalPair.program,SKPhysicalPair.checkCode,SKPhysicalPair.physical,
    SKPhysicalPair.firstCode,SKPhysicalPair.secondCode,SKPhysicalPair.lookupCode,
    IndexGeneration.powerProgram,IndexGeneration.powerInit,IndexGeneration.powerBody,
    SKPhysicalLookup.program,SKPhysicalLookup.initCode,SKPhysicalLookup.bodyCode,
    code,Program.All,Instruction.realDestination]
  omega

theorem pairValue_congr (a s : State)
    (hn : a.natReg 500=s.natReg 500) (hm : a.natReg 501=s.natReg 501)
    (hmem : a.natMem=s.natMem) (hmean : a.realReg 504=s.realReg 504)
    (hw : ∀i,i<s.natReg 501 → a.realMem (2*i)=s.realMem (2*i)) (u v : ℕ) :
    pairValue a u v=pairValue s u v := by
  apply value_congr (writeNatReg (writeNatReg a 390 u) 391 v) s u v
  · simp
  · simp
  · simpa using hn
  · simpa using hm
  · simpa using hmem
  · simpa using hmean
  · simpa using hw

theorem entry_at (s : State) (i j : ℕ) (hj : j<s.natReg 423) :
    entry s (i*s.natReg 423+j)=
      pairValue s (s.natMem (s.natReg 420+i)) (s.natMem (s.natReg 421+j)) := by
  have hc : 0<s.natReg 423 := by omega
  have hd : (i*s.natReg 423+j)/s.natReg 423=i := by
    rw [Nat.mul_comm i,Nat.mul_add_div hc,Nat.div_eq_of_lt hj,Nat.add_zero]
  simp [entry,hd,Nat.add_mod,Nat.mod_eq_of_lt hj]

theorem computed_at (s t : State) (hi : Invariant s (s.natReg 422*s.natReg 423) t)
    (i j : ℕ) (hirow : i<s.natReg 422) (hjcol : j<s.natReg 423) :
    t.realMem (s.natReg 424+i*s.natReg 423+j)=
      pairValue s (s.natMem (s.natReg 420+i)) (s.natMem (s.natReg 421+j)) := by
  have hindex : i*s.natReg 423+j<s.natReg 422*s.natReg 423 := by nlinarith
  have hv := hi.computed (i*s.natReg 423+j) hindex
  rw [entry_at s i j hjcol] at hv
  simpa [Nat.add_assoc] using hv

end Manuscript.SKPhysicalMatrix
