import Manuscript.SKRestrictedMemoCell
import Manuscript.SKIndexSpecifications

/-! Uniform runtime construction of the colorful-path recurrence addresses,
singleton/membership tests, and cardinality-layer test. -/
noncomputable section
namespace Manuscript.SKMemoMetadata
open RestrictedMachine RestrictedMachine.IndexGeneration SKBasisEncoding

/-- Inputs: N200,K201,mask202,endpoint203,colorBase204,oldBase205,
newBase206,weightBase207,startBase208,layer209. -/
def preludeCode : List Instruction :=
  [.nadd 210 204 203, .loadNat 131 210, .nconst 130 2]
def middle : List Instruction :=
  [.ncopy 211 132, .ncopy 120 202, .ncopy 121 202, .ncopy 123 201]
def suffix : List Instruction :=
  [.nconst 2 1, .ncopy 3 200, .ncopy 4 200,
   .nsub 212 202 211, .nmul 0 212 200, .nadd 0 205 0,
   .nadd 1 207 203, .nmul 213 202 200, .nadd 213 213 203,
   .nadd 8 206 213, .nadd 10 208 203, .neq 7 202 211,
   .ndiv 9 202 211, .nconst 214 2, .nmod 9 9 214,
   .neq 11 122 209, .nadd 12 205 213]

def program : Program := .seq (code preludeCode)
  (.seq powerProgram (.seq (code middle) (.seq overlapProgram (code suffix))))

def Spec (s t : State) : Prop :=
  let color := s.natMem (s.natReg 204+s.natReg 203)
  let power := 2^color
  t.natReg 0 = s.natReg 205+(s.natReg 202-power)*s.natReg 200 ∧
  t.natReg 1 = s.natReg 207+s.natReg 203 ∧
  t.natReg 2 = 1 ∧ t.natReg 3 = s.natReg 200 ∧ t.natReg 4 = s.natReg 200 ∧
  t.natReg 8 = s.natReg 206+s.natReg 202*s.natReg 200+s.natReg 203 ∧
  t.natReg 10 = s.natReg 208+s.natReg 203 ∧
  t.natReg 7 = (if s.natReg 202=power then 1 else 0) ∧
  t.natReg 9 = s.natReg 202/power%2 ∧
  t.natReg 11 = (if overlapFold (s.natReg 201) (s.natReg 202) (s.natReg 202) 0 =
      s.natReg 209 then 1 else 0) ∧
  t.natReg 12 = s.natReg 205+s.natReg 202*s.natReg 200+s.natReg 203 ∧
  t.realMem = s.realMem ∧ t.natMem = s.natMem

theorem realReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (h : Exec params input program s c t) : t.realReg r = s.realReg r := by
  apply h.realReg_frame
  simp [program, preludeCode, middle, suffix, powerProgram, powerInit, powerBody,
    overlapProgram, overlapInit, overlapBody, code, Program.All, Instruction.realDestination]

theorem natReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (h : Exec params input program s c t) (hr : 200 ≤ r ∧ r ≤ 209) :
    t.natReg r = s.natReg r := by
  apply h.natReg_frame
  simp [program, preludeCode, middle, suffix, powerProgram, powerInit, powerBody,
    overlapProgram, overlapInit, overlapBody, code, Program.All, Instruction.natDestination]
  omega

/-- Every address and branch flag needed for a recurrence cell is computed
from the runtime mask, endpoint, color cache and layer number. -/
theorem metadata_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 9*s.natMem (s.natReg 204+s.natReg 203)+29*s.natReg 201+100 ∧ Spec s t := by
  let a := runCode params input preludeCode s
  obtain ⟨cp,b,hp,bp,vp⟩ := power_execution params input a
  have bf (r : ℕ) (hr : r ≠ 132) : b.natReg r = a.natReg r := by
    apply hp.natReg_frame
    simpa [powerProgram, powerInit, powerBody, code, Program.All, Instruction.natDestination, ne_comm] using hr
  have bm : b.natMem = a.natMem := by
    apply hp.natMem_frame
    simp [powerProgram, powerInit, powerBody, code, Program.All, Instruction.writesNatMemory]
  have br : b.realMem = a.realMem := by
    apply hp.realMem_frame
    simp [powerProgram, powerInit, powerBody, code, Program.All, Instruction.writesRealMemory]
  let d := runCode params input middle b
  obtain ⟨co,u,ho,bo,vo⟩ := overlap_execution params input d
  have uf (r : ℕ) (hr : 131 ≤ r) : u.natReg r=d.natReg r :=
    overlap_natReg_frame params input d u co r ho (by omega)
  have um := (overlap_memory_frame params input d u co ho).2
  have ur := (overlap_memory_frame params input d u co ho).1
  have fixed (r : ℕ) (hr : 200 ≤ r ∧ r ≤ 209) : u.natReg r = s.natReg r := by
    rw [uf r (by omega)]
    have hn : r ≠ 211 ∧ r ≠ 120 ∧ r ≠ 121 ∧ r ≠ 123 ∧ r ≠ 130 ∧ r ≠ 131 ∧ r ≠ 210 := by omega
    simp [d, middle, runCode, step, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
      hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2, bf r (by omega), a, preludeCode]
  have power : u.natReg 211 = 2^s.natMem (s.natReg 204+s.natReg 203) := by
    rw [uf 211 (by omega)]
    simp [d, middle, runCode, step, vp, a, preludeCode]
  have card : u.natReg 122 = overlapFold (s.natReg 201) (s.natReg 202) (s.natReg 202) 0 := by
    rw [vo]
    simp [d, middle, runCode, step, bf 201 (by omega), bf 202 (by omega), a, preludeCode]
  have nm : u.natMem = s.natMem := by simpa [d, middle, runCode, step, a, preludeCode] using um.trans bm
  have rm : u.realMem = s.realMem := by simpa [d, middle, runCode, step, a, preludeCode] using ur.trans br
  let t := runCode params input suffix u
  refine ⟨8+cp+(8+(co+58)),t,?_,?_,?_⟩
  · convert Exec.seq (exec_code params input preludeCode s)
      (Exec.seq hp (Exec.seq (exec_code params input middle b)
        (Exec.seq ho (exec_code params input suffix u)))) using 1 <;>
      simp [program, preludeCode, middle, suffix, codeCost, instrCost, Nat.add_assoc]
  · have bpower : cp ≤ 9*s.natMem (s.natReg 204+s.natReg 203)+6 := by
      simpa [a, preludeCode, runCode, step] using bp
    have boverlap : co ≤ 29*s.natReg 201+7 := by
      simpa [d, middle, runCode, step, bf 201 (by omega), a, preludeCode] using bo
    omega
  · simp [Spec, t, suffix, runCode, step, power, card, nm, rm,
      fixed 200 (by omega), fixed 202 (by omega),
      fixed 203 (by omega), fixed 205 (by omega),
      fixed 206 (by omega), fixed 207 (by omega), fixed 208 (by omega),
      fixed 209 (by omega), Nat.add_assoc]

end Manuscript.SKMemoMetadata
