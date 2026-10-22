import Manuscript.RestrictedIndices

noncomputable section
namespace Manuscript.RestrictedMachine
namespace IndexGeneration

structure PairRecord where
  accepted : ℕ
  left : ℕ
  right : ℕ
  target : ℕ

def pairRecord (s : State) : PairRecord :=
  let q := s.natReg 142
  let p := s.natReg 143
  let l := s.natReg 140
  let r := s.natReg 141
  let charge := (l/q)/p+(r/q)/p
  let maskL := (l/q)%p
  let maskR := (r/q)%p
  let overlap := overlapFold (s.natReg 146) maskL maskR 0
  let degree := degreeFold (s.natReg 145) (l%q) (r%q) 0 1
  ⟨(if charge ≤ s.natReg 144 then 1 else 0)*(if overlap=0 then 1 else 0),
    s.natReg 148+l, s.natReg 149+r,
    s.natReg 150+((charge*p+(maskL+maskR))*q+degree)⟩

def pairDecode : List Instruction :=
  [.nmod 100 140 142, .nmod 101 141 142,
   .ndiv 151 140 142, .nmod 120 151 143, .ndiv 152 151 143,
   .ndiv 153 141 142, .nmod 121 153 143, .ndiv 154 153 143,
   .nadd 155 120 121, .nadd 156 152 154, .ncopy 104 145, .ncopy 123 146]
def pairAddress : List Instruction :=
  [.nle 157 156 144, .nconst 158 0, .neq 159 122 158, .nmul 160 157 159,
   .nmul 161 156 143, .nadd 161 161 155, .nmul 161 161 142, .nadd 161 161 103,
   .nadd 162 148 140, .nadd 163 149 141, .nadd 164 150 161]
def pairEmit : List Instruction :=
  [.nconst 165 1, .storeNat 147 160, .nadd 147 147 165,
   .storeNat 147 162, .nadd 147 147 165,
   .storeNat 147 163, .nadd 147 147 165,
   .storeNat 147 164, .nadd 147 147 165]

/-- Uniform generation of one multiplication record. nat140/141 are basis
indices, nat142/143 are the previously computed radix powers, nat144 is the
charge capacity, nat145/146 the degree/mask lengths, nat147 the output pointer,
and nat148/149/150 the real-table bases. No record is supplied as raw input. -/
def pairProgram : Program := .seq (code pairDecode)
  (.seq degreeProgram (.seq overlapProgram (.seq (code pairAddress) (code pairEmit))))

def writeRecord (memory : ℕ → ℕ) (address : ℕ) (record : PairRecord) : ℕ → ℕ :=
  Function.update
    (Function.update
      (Function.update
        (Function.update memory address record.accepted)
        (address+1) record.left)
      (address+2) record.right)
    (address+3) record.target

theorem pair_emit_spec (p : Parameters) (i : Inputs) (s : State) :
    let t := runCode p i pairEmit s
    t.natReg 147=s.natReg 147+4 ∧
    t.natMem=writeRecord s.natMem (s.natReg 147)
      ⟨s.natReg 160,s.natReg 162,s.natReg 163,s.natReg 164⟩ := by
  simp [pairEmit, runCode, step, writeNatMem, writeRecord, Nat.add_assoc]

theorem pair_decode_frame (p : Parameters) (i : Inputs) (s : State) (r : ℕ)
    (hr : 140 ≤ r ∧ r ≤ 150) : (runCode p i pairDecode s).natReg r = s.natReg r := by
  apply (exec_code p i pairDecode s).natReg_frame
  simp [pairDecode, code, Program.All, Instruction.natDestination]
  omega

theorem pair_execution (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i pairProgram s c t ∧
      c ≤ 52*s.natReg 145+29*s.natReg 146+140 ∧
      t.natReg 147=s.natReg 147+4 ∧
      t.natMem=writeRecord s.natMem (s.natReg 147) (pairRecord s) := by
  let d := runCode p i pairDecode s
  obtain ⟨cd,m,hd,bd,vd⟩ := degree_execution p i d
  obtain ⟨co,u,ho,bo,vo⟩ := overlap_execution p i m
  let a := runCode p i pairAddress u
  let t := runCode p i pairEmit a
  have dm : d.natMem=s.natMem := by simp [d, pairDecode, runCode, step]
  have mm := (degree_memory_frame p i d m cd hd).2
  have um := (overlap_memory_frame p i m u co ho).2
  have uf (r : ℕ) (hr : 140 ≤ r) : u.natReg r=d.natReg r :=
    (overlap_natReg_frame p i m u co r ho (by omega)).trans
      (degree_natReg_frame p i d m cd r hd (by omega))
  have mf (r : ℕ) (hr : 120 ≤ r) : m.natReg r=d.natReg r :=
    degree_natReg_frame p i d m cd r hd (by omega)
  have ux : u.natReg 103 = degreeFold (s.natReg 145)
      (s.natReg 140%s.natReg 142) (s.natReg 141%s.natReg 142) 0 1 := by
    rw [overlap_natReg_frame p i m u co 103 ho (by omega), vd]
    simp [d, pairDecode, runCode, step]
  have uo : u.natReg 122 = overlapFold (s.natReg 146)
      ((s.natReg 140/s.natReg 142)%s.natReg 143)
      ((s.natReg 141/s.natReg 142)%s.natReg 143) 0 := by
    rw [vo, mf 123 (by omega), mf 120 (by omega), mf 121 (by omega)]
    simp [d, pairDecode, runCode, step]
  have ur (r : ℕ) (hr : 140 ≤ r ∧ r ≤ 150) : u.natReg r=s.natReg r :=
    (uf r hr.1).trans (pair_decode_frame p i s r hr)
  have u155 : u.natReg 155 =
      (s.natReg 140/s.natReg 142)%s.natReg 143+(s.natReg 141/s.natReg 142)%s.natReg 143 := by
    rw [uf 155 (by omega)]
    simp [d, pairDecode, runCode, step]
  have u156 : u.natReg 156 =
      (s.natReg 140/s.natReg 142)/s.natReg 143+(s.natReg 141/s.natReg 142)/s.natReg 143 := by
    rw [uf 156 (by omega)]
    simp [d, pairDecode, runCode, step]
  have av : (⟨a.natReg 160,a.natReg 162,a.natReg 163,a.natReg 164⟩ : PairRecord)=pairRecord s := by
    simp [a, pairAddress, pairRecord, runCode, step, ux, uo, u155, u156,
      ur 140 (by omega), ur 141 (by omega), ur 142 (by omega), ur 143 (by omega),
      ur 144 (by omega), ur 148 (by omega), ur 149 (by omega), ur 150 (by omega)]
  have ap : a.natReg 147=s.natReg 147 := by
    simpa [a,pairAddress,runCode,step] using ur 147 (by omega)
  have am : a.natMem=s.natMem := by
    simpa [a,pairAddress,runCode,step] using um.trans (mm.trans dm)
  have out := pair_emit_spec p i a
  refine ⟨44+cd+(co+(41+29)),t,?_,?_,?_,?_⟩
  · convert Exec.seq (exec_code p i pairDecode s)
      (Exec.seq hd (Exec.seq ho (Exec.seq (exec_code p i pairAddress u) (exec_code p i pairEmit a)))) using 1 <;>
      simp [pairProgram, pairDecode, pairAddress, pairEmit, codeCost, instrCost, Nat.add_assoc]
  · have bdegree : cd ≤ 52*s.natReg 145+10 := by simpa [d,pairDecode,runCode,step] using bd
    have boverlap : co ≤ 29*s.natReg 146+7 := by
      rw [mf 123 (by omega)] at bo
      simpa [d,pairDecode,runCode,step] using bo
    omega
  · exact out.1.trans (congrArg (·+4) ap)
  · simpa only [am,ap,av] using out.2

theorem pair_natReg_frame (p : Parameters) (i : Inputs) (s t : State) (c r : ℕ)
    (h : Exec p i pairProgram s c t)
    (hr : r < 100 ∨ 165 < r ∨ (140 ≤ r ∧ r ≤ 150 ∧ r ≠ 147)) : t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [pairProgram,pairDecode,pairAddress,pairEmit,degreeProgram,degreeInit,degreeBody,
    degreePrefix,degreeHigh,degreeLow,degreeTail,overlapProgram,overlapInit,overlapBody,
    code, Program.All, Instruction.natDestination]
  omega

theorem pair_realMem_frame (p : Parameters) (i : Inputs) (s t : State) (c : ℕ)
    (h : Exec p i pairProgram s c t) : t.realMem=s.realMem := by
  apply h.realMem_frame
  simp [pairProgram,pairDecode,pairAddress,pairEmit,degreeProgram,degreeInit,degreeBody,
    degreePrefix,degreeHigh,degreeLow,degreeTail,overlapProgram,overlapInit,overlapBody,
    code, Program.All, Instruction.writesRealMemory]

end IndexGeneration
end Manuscript.RestrictedMachine
