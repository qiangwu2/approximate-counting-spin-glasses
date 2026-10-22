import Manuscript.SKMemoMetadata

/-! A complete addressed path-table update: metadata is computed by actual
natural instructions, then the actual scalar/cache program is executed. -/
noncomputable section
namespace Manuscript.SKMemoUpdate
open RestrictedMachine SKBasisEncoding SKIndexSpecifications
open scoped BigOperators

def program : Program := .seq SKMemoMetadata.program
  (.branch 11 SKRestrictedMemoCell.program (code [.loadReal 0 12, .storeReal 8 0]))

def rowAddress {K : ℕ} (N base : ℕ) (S : Finset (Fin K)) (j : ℕ) : ℕ :=
  base+(maskEquiv K S).val*N+j

def Registers {N K : ℕ} (colorBase oldBase newBase weightBase startBase layer : ℕ)
    (S : Finset (Fin K)) (j : Fin N) (s : State) : Prop :=
  s.natReg 200=N ∧ s.natReg 201=K ∧ s.natReg 202=(maskEquiv K S).val ∧
  s.natReg 203=j.val ∧ s.natReg 204=colorBase ∧ s.natReg 205=oldBase ∧
  s.natReg 206=newBase ∧ s.natReg 207=weightBase ∧ s.natReg 208=startBase ∧
  s.natReg 209=layer

theorem natReg_frame (params : Parameters) (input : Inputs) (s t : State) (c r : ℕ)
    (h : Exec params input program s c t) (hr : 200 ≤ r ∧ r ≤ 209) :
    t.natReg r=s.natReg r := by
  apply h.natReg_frame
  simp [program, SKMemoMetadata.program, SKMemoMetadata.preludeCode, SKMemoMetadata.middle,
    SKMemoMetadata.suffix, RestrictedMachine.IndexGeneration.powerProgram,
    RestrictedMachine.IndexGeneration.powerInit, RestrictedMachine.IndexGeneration.powerBody,
    RestrictedMachine.IndexGeneration.overlapProgram, RestrictedMachine.IndexGeneration.overlapInit,
    RestrictedMachine.IndexGeneration.overlapBody, SKRestrictedMemoCell.program,
    SKRestrictedKernels.dotProgram, SKRestrictedKernels.dotBody, code, Program.All,
    Instruction.natDestination]
  omega

/-- The concrete, uniformly generated cell update implements one entire
increasing-cardinality memo pass, including copies of all other layers. -/
theorem update_realized {N K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (χ : Fin N → Fin K) (start : Fin N → ℝ) (w : Fin N → Fin N → ℝ)
    (old : Finset (Fin K) → Fin N → ℝ) (S : Finset (Fin K)) (j : Fin N)
    (colorBase oldBase newBase weightBase startBase layer : ℕ)
    (hreg : Registers colorBase oldBase newBase weightBase startBase layer S j s)
    (hcolor : s.natMem (colorBase+j.val) = (χ j).val)
    (hprev : ∀ T i, s.realMem (rowAddress N oldBase T i.val) = old T i)
    (hweight : ∀ i, s.realMem (weightBase+i.val*N+j.val) = w i j)
    (hstart : s.realMem (startBase+j.val) = start j) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 38*K+27*N+120 ∧
      t.realMem = Function.update s.realMem (rowAddress N newBase S j.val)
        (if S.card=layer then SpinGlass.ColorMemoExecution.update χ start w old S j else old S j) ∧
      t.natMem=s.natMem ∧ (∀ r, 4 ≤ r → t.realReg r=s.realReg r) := by
  rcases hreg with ⟨hN,hK,hS,hj,hc,ho,hn,hw,hs,hl⟩
  obtain ⟨cm,m,hem,hcm,hm⟩ := SKMemoMetadata.metadata_realized params input s
  have hcolor' : s.natMem (s.natReg 204+s.natReg 203) = (χ j).val := by simpa [hc,hj] using hcolor
  dsimp only [SKMemoMetadata.Spec] at hm
  rw [hcolor',hN,hK,hS,hj,ho,hn,hw,hs,hl] at hm
  rcases hm with ⟨h0,h1,h2,h3,h4,h8,h10,h7,h9,h11,h12,hrm,hnm⟩
  have hsingle : m.natReg 7 = if S={χ j} then 1 else 0 := by
    simpa [mask_eq_singleton_iff] using h7
  have hmember : m.natReg 9 = if χ j ∈ S then 1 else 0 := by
    simpa [mask_digit] using h9
  have hlayer : m.natReg 11 = if S.card=layer then 1 else 0 := by
    simpa [overlapFold_self] using h11
  have hmstart : m.realMem (m.natReg 10)=start j := by rw [hrm,h10]; exact hstart
  have hmprev : χ j ∈ S → ∀ i : Fin N,
      m.realMem (m.natReg 0+i.val*m.natReg 2)=old (S.erase (χ j)) i := by
    intro hc i
    rw [hrm,h0,h2,mask_erase S (χ j) hc,Nat.mul_one]
    exact hprev _ _
  have hmweight : ∀ i : Fin N,
      m.realMem (m.natReg 1+i.val*m.natReg 3)=w i j := by
    intro i
    rw [hrm,h1,h3]
    convert hweight i using 1 <;> congr 1 <;> omega
  have hcm' : cm ≤ 38*K+100 := by
    rw [hcolor',hK] at hcm
    have hlt := (χ j).isLt
    omega
  by_cases hc : S.card=layer
  · have hflag : m.natReg 11 ≠ 0 := by rw [hlayer]; simp [hc]
    obtain ⟨ct,t,het,hct,hmem,hnat,hreal⟩ := SKRestrictedMemoCell.cell_realized params input m
      χ start w old S j h4 hsingle hmember hmstart hmprev hmweight
    refine ⟨cm+(ct+3),t,Exec.seq hem (Exec.branchNonzero hflag het),by omega,?_,hnat.trans hnm,?_⟩
    · rw [hmem,hrm,h8]
      simp [rowAddress,hc]
    · intro r hr
      exact (hreal r hr).trans (SKMemoMetadata.realReg_frame params input s m cm r hem)
  · have hflag : m.natReg 11=0 := by rw [hlayer]; simp [hc]
    let t := runCode params input [.loadReal 0 12, .storeReal 8 0] m
    have het : Exec params input (code [.loadReal 0 12, .storeReal 8 0]) m 6 t := by
      simpa [t,codeCost,instrCost] using exec_code params input [.loadReal 0 12, .storeReal 8 0] m
    refine ⟨cm+9,t,?_,by omega,?_,?_,?_⟩
    · exact Exec.seq hem (Exec.branchZero hflag het)
    · have hread := hprev S j
      simp only [rowAddress] at hread
      simp [t,runCode,step,writeRealMem,hrm,h8,h12,rowAddress,hc,hread]
    · simp [t,runCode,step,writeRealMem,hnm]
    · intro r hr
      have hr0 : r ≠ 0 := by omega
      simp [t,runCode,step,writeRealMem,hr0,SKMemoMetadata.realReg_frame params input s m cm r hem]

end Manuscript.SKMemoUpdate
