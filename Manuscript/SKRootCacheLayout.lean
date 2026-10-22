import Manuscript.SKMemoInitialization
import Manuscript.SKRootStart

noncomputable section
namespace Manuscript.SKRootCache
open RestrictedMachine SKMemoUpdate SKMemoPass SKMemoLayers

/-- Input-dependent dimensions and RAM addresses are held in registers, not
embedded as literals in the fixed program. -/
structure Layout where
  N : ℕ
  K : ℕ
  B : ℕ
  colorBase : ℕ
  weightBase : ℕ
  branchBase : ℕ
  arena : ℕ
  weightFit : weightBase+N*N≤arena
  branchFit : branchBase+B*N≤arena

def Layout.T (d : Layout) := 2^d.K*d.N
def Layout.left (d : Layout) := d.arena+d.N
def Layout.right (d : Layout) := d.arena+d.N+d.T
def Layout.cache (d : Layout) := d.arena+d.N+2*d.T

def start {N B : ℕ} (branch : Fin B→Fin N→ℝ) (r : ℕ) (j : Fin N) : ℝ :=
  if h : r<B then branch ⟨r,h⟩ j else if j.val=r-B then 1 else 0

structure Registers (d : Layout) (r : ℕ) (s : State) : Prop where
  size : s.natReg 200=d.N
  colors : s.natReg 201=d.K
  colorBase : s.natReg 204=d.colorBase
  weightBase : s.natReg 207=d.weightBase
  branches : s.natReg 230=d.B
  branchBase : s.natReg 231=d.branchBase
  arena : s.natReg 232=d.arena
  roots : s.natReg 233=d.B+d.N
  counter : s.natReg 234=r
  one : s.natReg 235=1
  tableSize : s.natReg 236=d.T
  left : s.natReg 238=d.left
  right : s.natReg 239=d.right
  cache : s.natReg 240=d.cache

theorem row_bounds (N K base : ℕ) (S : Finset (Fin K)) (j : Fin N) :
    base≤rowAddress N base S j.val ∧ rowAddress N base S j.val<base+2^K*N := by
  have h := (cellEquiv N K (S,j)).isLt
  rw [←cellIndex_eq] at h
  simp only [rowAddress,cellIndex] at *
  omega

theorem Layout.weight_lt (d : Layout) (i j : Fin d.N) :
    d.weightBase+i.val*d.N+j.val<d.arena := by
  have hi := i.isLt
  have hj := j.isLt
  have h := d.weightFit
  nlinarith

theorem Layout.branch_lt (d : Layout) (r : Fin d.B) (j : Fin d.N) :
    d.branchBase+r.val*d.N+j.val<d.arena := by
  have hi := r.isLt
  have hj := j.isLt
  have h := d.branchFit
  nlinarith

theorem Layout.separation (d : Layout) :
    Separation d.N d.K d.left d.right d.weightBase d.arena := by
  constructor
  · intro S T i j
    have ha := row_bounds d.N d.K d.left S i
    have hb := row_bounds d.N d.K d.right T j
    simp only [Layout.left,Layout.right,Layout.T] at *
    omega
  · intro S j i k
    have ha := row_bounds d.N d.K d.left S j
    have hb := d.weight_lt i k
    simp only [Layout.left] at *
    omega
  · intro S j i k
    have ha := row_bounds d.N d.K d.right S j
    have hb := d.weight_lt i k
    simp only [Layout.right] at *
    omega
  · intro S j i
    have ha := row_bounds d.N d.K d.left S j
    have hi := i.isLt
    simp only [Layout.left] at *
    omega
  · intro S j i
    have ha := row_bounds d.N d.K d.right S j
    have hi := i.isLt
    simp only [Layout.right] at *
    omega

theorem Layout.outside (d : Layout) (s : State)
    (hl : s.natReg 205=d.left) (hr : s.natReg 206=d.right)
    (a : ℕ) (ha : a<d.arena ∨ d.cache≤a) : Outside d.N d.K s a := by
  intro S j
  have h1 := row_bounds d.N d.K d.left S j
  have h2 := row_bounds d.N d.K d.right S j
  simp only [hl,hr]
  simp only [Layout.left,Layout.right,Layout.cache,Layout.T] at *
  constructor <;> omega

end Manuscript.SKRootCache
