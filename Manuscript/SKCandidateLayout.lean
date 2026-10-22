import Manuscript.SKPrimitiveFrames
import Mathlib.Tactic.IntervalCases
import Manuscript.SKRootCacheCanonical
import Manuscript.SKRootCacheFrames

/-! Runtime allocation arithmetic for one SK candidate. All powers and
addresses are produced by the restricted machine. -/
noncomputable section
namespace Manuscript.SKCandidateLayout
open RestrictedMachine IndexGeneration SKBasisEncoding

structure Layout where
  root : SKRootCache.Layout
  chargeBase : ℕ
  branchWeightBase : ℕ
  metadataBase : ℕ
  ghost : Fin root.B
  retained : ℕ
  branchWeightFit : branchWeightBase+root.B*root.B≤root.arena

def Layout.M (d : Layout) := (d.root.K+1)*2^d.root.K*6^d.root.B
def Layout.base (d : Layout) := d.root.cache+(d.root.B+d.root.N)*d.root.T
def Layout.primitiveBase (d : Layout) := d.base+d.M
def Layout.bank (d : Layout) := d.base+4*d.M

def expected (d : Layout) (r : ℕ) : ℕ :=
  if r=400 then d.chargeBase else if r=401 then d.branchWeightBase else
  if r=402 then d.metadataBase else if r=403 then d.ghost.val else
  if r=404 then d.M else if r=405 then 2^d.root.K else if r=406 then 6^d.root.B else
  if r=407 then d.base else if r=408 then d.bank else if r=409 then d.root.K else
  if r=410 then d.root.B else if r=411 then d.root.N else if r=412 then d.root.arena else
  if r=413 then d.root.cache else if r=414 then d.root.T else if r=415 then d.root.branchBase else
  if r=416 then d.root.weightBase else d.retained

def Shape (d : Layout) (s : State) : Prop := ∀r,400≤r → r≤417 → s.natReg r=expected d r
structure Inputs (d : Layout) (s : State) : Prop where
  chargeBase : s.natReg 400=d.chargeBase
  branchBase : s.natReg 401=d.branchWeightBase
  metadataBase : s.natReg 402=d.metadataBase
  ghost : s.natReg 403=d.ghost.val
  retained : s.natReg 417=d.retained

def first : List Instruction := [.nconst 130 2,.ncopy 131 201]
def second : List Instruction := [.ncopy 405 132,.nconst 130 6,.ncopy 131 230]
def finish : List Instruction :=
  [.ncopy 406 132,.nconst 419 1,.nadd 404 201 419,.nmul 404 404 405,.nmul 404 404 406,
   .nmul 407 233 236,.nadd 407 407 240,.nconst 418 4,.nmul 408 404 418,.nadd 408 407 408,
   .ncopy 409 201,.ncopy 410 230,.ncopy 411 200,.ncopy 412 232,.ncopy 413 240,
   .ncopy 414 236,.ncopy 415 231,.ncopy 416 207,
   .ncopy 220 414,.ncopy 253 413,.ncopy 255 415,.ncopy 256 410,.ncopy 257 416,
   .ncopy 273 409,.ncopy 274 405,.ncopy 275 406,.nadd 276 407 404,.ncopy 282 400,.nconst 292 1]
def program : Program := .seq (code first) (.seq powerProgram
  (.seq (code second) (.seq powerProgram (code finish))))

def PrimitiveRegisters (d : Layout) (s : State) : Prop :=
  s.natReg 200=d.root.N ∧ s.natReg 201=d.root.K ∧ s.natReg 220=d.root.T ∧
  s.natReg 253=d.root.cache ∧ s.natReg 255=d.root.branchBase ∧ s.natReg 256=d.root.B ∧
  s.natReg 257=d.root.weightBase ∧ s.natReg 273=d.root.K ∧ s.natReg 274=2^d.root.K ∧
  s.natReg 275=6^d.root.B ∧ s.natReg 276=d.primitiveBase ∧ s.natReg 282=d.chargeBase ∧ s.natReg 292=1

theorem program_exec (p : Parameters) (i : RestrictedMachine.Inputs) (d : Layout) (s : State)
    (hr : SKRootCache.Registers d.root (d.root.B+d.root.N) s) (hs : Inputs d s) :
    ∃ c t, Exec p i program s c t ∧ c≤9*(d.root.K+d.root.B)+100 ∧
      Shape d t ∧ PrimitiveRegisters d t ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem ∧
      (∀r,t.realReg r=s.realReg r) := by
  let a := runCode p i first s
  obtain ⟨c1,b,he1,bc1,hp1⟩ := power_execution p i a
  have bf (r) (hr : r≠132) := (SKDirectIndex.power_frames p i he1).1 r hr
  let e := runCode p i second b
  obtain ⟨c2,f,he2,bc2,hp2⟩ := power_execution p i e
  have ff (r) (hr : r≠132) := (SKDirectIndex.power_frames p i he2).1 r hr
  have fhigh (r : ℕ) (h : 200≤r ∧ r≠405) : f.natReg r=s.natReg r := by
    have hn : r≠130 ∧ r≠131 := by omega
    rw [ff r (by omega)]
    simp [e,second,runCode,step,h.2,hn.1,hn.2,bf r (by omega),a,first]
  have fp : f.natReg 405=2^d.root.K := by
    rw [ff 405 (by omega)]
    simpa [e,second,runCode,step,a,first,hr.colors] using hp1
  have fq : f.natReg 132=6^d.root.B := by
    simpa [e,second,runCode,step,bf 230 (by omega),a,first,hr.branches] using hp2
  let t := runCode p i finish f
  have heall : Exec p i program s (3+(c1+(5+(c2+71)))) t :=
    Exec.seq (exec_code p i first s) (Exec.seq he1
      (Exec.seq (exec_code p i second b) (Exec.seq he2 (exec_code p i finish f))))
  refine ⟨_,t,heall,?_,?_,?_,?_,?_,?_⟩
  · have b1 : c1≤9*d.root.K+6 := by simpa [a,first,runCode,step,hr.colors] using bc1
    have b2 : c2≤9*d.root.B+6 := by simpa [e,second,runCode,step,bf 230 (by omega),a,first,hr.branches] using bc2
    omega
  · intro r hlo hhi
    interval_cases r <;>
      simp [t,finish,runCode,step,expected,fp,fq,fhigh,hr.colors,hr.branches,hr.size,hr.arena,
        hr.cache,hr.tableSize,hr.branchBase,hr.weightBase,hr.roots,
        hs.chargeBase,hs.branchBase,hs.metadataBase,hs.ghost,hs.retained,
        Layout.M,Layout.base,Layout.bank] <;> ring
  · simp [PrimitiveRegisters,t,finish,runCode,step,fp,fq,fhigh,hr.colors,hr.branches,hr.size,hr.arena,
      hr.cache,hr.tableSize,hr.branchBase,hr.weightBase,hr.roots,hs.chargeBase,
      Layout.M,Layout.base,Layout.primitiveBase] <;> ring
  · apply heall.realMem_frame
    simp [program,first,second,finish,powerProgram,powerInit,powerBody,code,Program.All,Instruction.writesRealMemory]
  · apply heall.natMem_frame
    simp [program,first,second,finish,powerProgram,powerInit,powerBody,code,Program.All,Instruction.writesNatMemory]
  · intro r; apply heall.realReg_frame
    simp [program,first,second,finish,powerProgram,powerInit,powerBody,code,Program.All,Instruction.realDestination]

theorem natReg_frame {p : Parameters} {i : RestrictedMachine.Inputs} {s t : State} {c r : ℕ}
    (he : Exec p i program s c t) (hr : 420≤r) : t.natReg r=s.natReg r := by
  apply he.natReg_frame
  simp [program,first,second,finish,powerProgram,powerInit,powerBody,code,Program.All,Instruction.natDestination]
  omega

theorem Layout.arena_le_base (d : Layout) : d.root.arena≤d.base := by
  simp [Layout.base,SKRootCache.Layout.cache]; omega

theorem Layout.base_lt_primitive (d : Layout) : d.base<d.primitiveBase := by
  have hp : 0<d.M := by unfold Layout.M; positivity
  unfold Layout.primitiveBase; omega

end Manuscript.SKCandidateLayout
