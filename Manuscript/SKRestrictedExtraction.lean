import Manuscript.SKExtractionCell

/-! A uniform scan of every actual coefficient coordinate, with a machine
computed acceptance test and color correction at each coordinate. -/
noncomputable section
namespace Manuscript.SKRestrictedExtraction
open RestrictedMachine SKBasisEncoding SKExtractionCell
open SpinGlass.SKCoefficient (Basis Coefficients)
open scoped BigOperators

def width (b K : ℕ) := (K+1)*2^K*6^b
def contribution {b K : ℕ} (f : Coefficients b K) (g : Fin b) (L : ℕ) (x : Basis b K) : ℝ :=
  if x.1.val≤L ∧ x.2.2∈accepted g then
    (SpinGlass.ColoringProbability.probability K x.2.1.card)⁻¹*f x else 0
def term {b K : ℕ} (f : Coefficients b K) (g : Fin b) (L j : ℕ) : ℝ :=
  if h : j<width b K then contribution f g L ((basisEquiv b K).symm ⟨j,h⟩) else 0

def setupCode : List Instruction := [.nconst 350 0,.nconst 359 1,.rconst 310 0]
def program : Program := .seq (code setupCode) (.repeat 358 SKExtractionCell.program)

structure Shape (b K : ℕ) (g : Fin b) (L base : ℕ) (s : State) : Prop where
  degreeSize : s.natReg 351=6^b
  maskSize : s.natReg 352=2^K
  palette : s.natReg 353=K
  branches : s.natReg 354=b
  ghost : s.natReg 355=g.val
  retained : s.natReg 356=L
  baseAddr : s.natReg 357=base
  bound : s.natReg 358=width b K

structure Invariant {b K : ℕ} (f : Coefficients b K) (g : Fin b) (L base n : ℕ) (s : State) : Prop where
  shape : Shape b K g L base s
  index : s.natReg 350=n
  one : s.natReg 359=1
  memory : ∀ x, s.realMem (base+encode x)=f x
  total : s.realReg 310=∑ j∈Finset.range n,term f g L j

theorem shape_frame {b K : ℕ} {g : Fin b} {L base : ℕ}
    {p : Parameters} {i : Inputs} {s t : State} {c : ℕ}
    (h : Exec p i SKExtractionCell.program s c t) (hs : Shape b K g L base s) :
    Shape b K g L base t := by
  have hf (r) (hr : 350<r ∧ r≠360 ∧ r≠361 ∧ r≠362 ∧ r≠363) := SKExtractionCell.natReg_frame h hr
  exact ⟨(hf 351 (by omega)).trans hs.degreeSize,(hf 352 (by omega)).trans hs.maskSize,
    (hf 353 (by omega)).trans hs.palette,(hf 354 (by omega)).trans hs.branches,
    (hf 355 (by omega)).trans hs.ghost,(hf 356 (by omega)).trans hs.retained,
    (hf 357 (by omega)).trans hs.baseAddr,(hf 358 (by omega)).trans hs.bound⟩

theorem step_realized {b K : ℕ} (p : Parameters) (i : Inputs) (f : Coefficients b K)
    (g : Fin b) (L base n : ℕ) (s : State) (hs : Invariant f g L base n s)
    (hn : n<width b K) :
    ∃ c t, Exec p i SKExtractionCell.program s c t ∧ c≤40*b+53*K+105 ∧
      Invariant f g L base (n+1) t ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let x := (basisEquiv b K).symm ⟨n,hn⟩
  have hx : encode x=n := congrArg Fin.val ((basisEquiv b K).apply_symm_apply _)
  have hr : SKExtractionCell.Registers x g L s :=
    ⟨hs.index.trans hx.symm,hs.shape.degreeSize,hs.shape.maskSize,hs.shape.palette,
      hs.shape.branches,hs.shape.ghost,hs.shape.retained,hs.one⟩
  obtain ⟨c,t,he,bc,hindex,hv,hm,hnm⟩ := cell_realized p i s x g L hr
  refine ⟨c,t,he,bc,?_,hm,hnm⟩
  refine ⟨shape_frame he hs.shape,by simpa [hs.index] using hindex,
    (SKExtractionCell.natReg_frame he (by omega : 350<359 ∧ 359≠360 ∧ 359≠361 ∧ 359≠362 ∧ 359≠363)).trans hs.one,
    ?_,?_⟩
  · intro y; rw [hm]; exact hs.memory y
  · rw [hv,hs.total,Finset.sum_range_succ]
    congr 1
    simp [term,hn,contribution,x,hs.shape.baseAddr,hs.memory]

theorem scan_realized {b K : ℕ} (p : Parameters) (i : Inputs) (f : Coefficients b K)
    (g : Fin b) (L base j n : ℕ) (s : State) (hs : Invariant f g L base j s)
    (hn : j+n≤width b K) :
    ∃ c t, Repeats p i SKExtractionCell.program n s c t ∧
      c≤n*(40*b+53*K+110)+3 ∧ Invariant f g L base (j+n) t ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  induction n generalizing j s with
  | zero => exact ⟨3,s,Repeats.zero _ _,by simp,by simpa using hs,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨c,a,hea,bc,ha,ham,han⟩ := step_realized p i f g L base j s hs (by omega)
    obtain ⟨d,t,het,bd,ht,htm,htn⟩ := ih (j+1) a ha (by omega)
    refine ⟨c+d+5,t,Repeats.succ hea het,?_,?_,htm.trans ham,htn.trans han⟩
    · calc
        c+d+5 ≤ (40*b+53*K+105)+(n*(40*b+53*K+110)+3)+5 := by omega
        _ = (n+1)*(40*b+53*K+110)+3 := by ring
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem sum_term {b K : ℕ} (f : Coefficients b K) (g : Fin b) (L : ℕ) :
    (∑ j∈Finset.range (width b K),term f g L j)=
      (SKChargedExtractionExecution.extract f L (accepted g)).value := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [term,Fin.isLt,dif_pos]
  have he := (basisEquiv b K).symm.sum_comp (contribution f g L)
  change (∑ j : Fin ((K+1)*2^K*6^b), contribution f g L ((basisEquiv b K).symm j)) = _
  rw [he]
  simp [SKChargedExtractionExecution.extract,SpinGlass.ArithmeticEvaluation.sumFinset,
    SpinGlass.ArithmeticEvaluation.mul,SpinGlass.ArithmeticEvaluation.literal,
    SKChargedExtractionExecution.colorReciprocal_value,contribution]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

theorem extraction_realized {b K : ℕ} (p : Parameters) (i : Inputs) (f : Coefficients b K)
    (g : Fin b) (L base : ℕ) (s : State) (hs : Shape b K g L base s)
    (hm : ∀ x,s.realMem (base+encode x)=f x) :
    ∃ c t, Exec p i program s c t ∧ c≤width b K*(40*b+53*K+110)+8 ∧
      t.realReg 310=(SKChargedExtractionExecution.extract f L (accepted g)).value ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let a := runCode p i setupCode s
  have ha : Invariant f g L base 0 a := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · rcases hs with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
      constructor <;> simp [a,setupCode,runCode,step,h1,h2,h3,h4,h5,h6,h7,h8]
    · simp [a,setupCode,runCode,step]
    · simp [a,setupCode,runCode,step]
    · simpa [a,setupCode,runCode,step] using hm
    · simp [a,setupCode,runCode,step]
  obtain ⟨c,t,he,bc,hv,htm,htn⟩ := scan_realized p i f g L base 0 (width b K) a ha (by simp)
  have hh : a.natReg 358=width b K := ha.shape.bound
  have her : Exec p i (.repeat 358 SKExtractionCell.program) a (c+2) t :=
    Exec.repeat (by rw [hh]; exact he)
  refine ⟨3+(c+2),t,Exec.seq (exec_code p i setupCode s) her,by omega,?_,?_,?_⟩
  · rw [hv.total]; simpa using sum_term f g L
  · simpa [a,setupCode,runCode,step] using htm
  · simpa [a,setupCode,runCode,step] using htn

/-- The label selected by the actual branch enumeration is the only ghost.
Consequently the executable test agrees with the manuscript's accepted set. -/
theorem accepted_eq {V : Type*} [Fintype V] [DecidableEq V] (A : Finset V)
    (g : Fin (SKGhostAdmissible.distinguished A).card)
    (hg : SpinGlass.SKActualEvaluator.branch (SKGhostAdmissible.distinguished A) g=none) :
    accepted g=SKGhostAdmissible.accepted A := by
  ext d
  simp only [accepted,SKGhostAdmissible.accepted,Finset.mem_filter,Finset.mem_univ,true_and]
  apply forall_congr'
  intro j
  have hj : SpinGlass.SKActualEvaluator.branch (SKGhostAdmissible.distinguished A) j=none ↔ j=g := by
    constructor
    · intro h; exact SpinGlass.SKActualEvaluator.branch_injective _ (h.trans hg.symm)
    · intro h; simpa [h] using hg
  simp [hj]
end Manuscript.SKRestrictedExtraction
