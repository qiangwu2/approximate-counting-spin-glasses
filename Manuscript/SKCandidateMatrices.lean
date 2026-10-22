import Manuscript.SKPhysicalMatrixStage
import Manuscript.SKPhysicalPairCanonical

noncomputable section
namespace Manuscript.SKCandidateMatrices
open RestrictedMachine SKPhysicalMatrixStage

def setupCode : List Instruction :=
  [.nconst 431 2,.nmul 207 431 501,.nmul 432 200 200,.nadd 231 207 432,
   .nmul 432 230 200,.nadd 445 231 432,.nmul 432 230 230,.nadd 232 445 432,
   .ncopy 400 532,.ncopy 401 445,.nconst 431 1,.nsub 403 230 431,
   .nadd 402 533 500,.nadd 402 402 431,.ncopy 417 512]
def program : Program := .seq (code setupCode) (.seq (SKPhysicalMatrixStage.program .outside)
  (.seq (SKPhysicalMatrixStage.program .branch) (SKPhysicalMatrixStage.program .direct)))

def outsideBase (s : State) := 2*s.natReg 501
def branchBase (s : State) := outsideBase s+s.natReg 200*s.natReg 200
def directBase (s : State) := branchBase s+s.natReg 230*s.natReg 200
def arena (s : State) := directBase s+s.natReg 230*s.natReg 230

def RootRegisters (s t : State) : Prop :=
  t.natReg 200=s.natReg 200 ∧ t.natReg 201=s.natReg 201 ∧
  t.natReg 204=s.natReg 204 ∧ t.natReg 230=s.natReg 230 ∧
  t.natReg 207=outsideBase s ∧ t.natReg 231=branchBase s ∧ t.natReg 232=arena s ∧
  t.natReg 400=s.natReg 532 ∧ t.natReg 401=directBase s ∧
  t.natReg 402=s.natReg 533+s.natReg 500+1 ∧ t.natReg 403=s.natReg 230-1 ∧
  t.natReg 417=s.natReg 512

structure PhysicalSame (s t : State) : Prop where
  size : t.natReg 500=s.natReg 500
  count : t.natReg 501=s.natReg 501
  mean : t.realReg 504=s.realReg 504
  natMem : t.natMem=s.natMem
  weights : ∀i,i<s.natReg 501 → t.realMem (2*i)=s.realMem (2*i)

theorem PhysicalSame.pairValue {s t : State} (h : PhysicalSame s t) (u v : ℕ) :
    SKPhysicalMatrix.pairValue t u v=SKPhysicalMatrix.pairValue s u v :=
  SKPhysicalMatrix.pairValue_congr t s h.size h.count h.natMem h.mean h.weights u v

theorem PhysicalSame.trans {s t u : State} (h : PhysicalSame s t) (g : PhysicalSame t u) :
    PhysicalSame s u := by
  refine ⟨g.size.trans h.size,g.count.trans h.count,g.mean.trans h.mean,g.natMem.trans h.natMem,?_⟩
  intro i hi
  exact (g.weights i (by rw [h.count]; exact hi)).trans (h.weights i hi)

theorem physicalSame_stage (k : Kind) (s t : State)
    (hfit : 2*s.natReg 501≤s.natReg (outputReg k))
    (hn : t.natMem=s.natMem)
    (hf : ∀a,(a<s.natReg (outputReg k) ∨
      s.natReg (outputReg k)+s.natReg (rowsReg k)*s.natReg (colsReg k)≤a) → t.realMem a=s.realMem a)
    (hr : ∀r,StableNat r → t.natReg r=s.natReg r)
    (hreal : ∀r,391≤r → t.realReg r=s.realReg r) : PhysicalSame s t := by
  refine ⟨hr 500 (by simp [StableNat]),hr 501 (by simp [StableNat]),hreal 504 (by omega),hn,?_⟩
  intro i hi
  apply hf
  left
  omega

theorem execution (params : Parameters) (input : Inputs) (s : State)
    (hbranch : ∀i,i<s.natReg 230 → s.natMem (s.natReg 530+i)≤s.natReg 500)
    (houtside : ∀i,i<s.natReg 200 → s.natMem (s.natReg 531+i)≤s.natReg 500) :
    ∃c t,Exec params input program s c t ∧
      c≤(s.natReg 200*s.natReg 200+s.natReg 230*s.natReg 200+s.natReg 230*s.natReg 230)*
        (SKPhysicalMatrix.cost s+5)+111 ∧ RootRegisters s t ∧ t.natMem=s.natMem ∧
      (∀i j,i<s.natReg 200 → j<s.natReg 200 →
        t.realMem (outsideBase s+i*s.natReg 200+j)=
          SKPhysicalMatrix.pairValue s (s.natMem (s.natReg 531+i)) (s.natMem (s.natReg 531+j))) ∧
      (∀i j,i<s.natReg 230 → j<s.natReg 200 →
        t.realMem (branchBase s+i*s.natReg 200+j)=
          SKPhysicalMatrix.pairValue s (s.natMem (s.natReg 530+i)) (s.natMem (s.natReg 531+j))) ∧
      (∀i j,i<s.natReg 230 → j<s.natReg 230 →
        t.realMem (directBase s+i*s.natReg 230+j)=
          SKPhysicalMatrix.pairValue s (s.natMem (s.natReg 530+i)) (s.natMem (s.natReg 530+j))) ∧
      (∀a,a<2*s.natReg 501 → t.realMem a=s.realMem a) ∧
      (∀r,500≤r → t.natReg r=s.natReg r) ∧
      (∀r,391≤r → t.realReg r=s.realReg r) := by
  let a := runCode params input setupCode s
  have af (r : ℕ) (hr : r=200 ∨ r=201 ∨ r=204 ∨ r=230 ∨ 500≤r) : a.natReg r=s.natReg r := by
    have h207 : r≠207 := by omega
    have h231 : r≠231 := by omega
    have h232 : r≠232 := by omega
    have h400 : r≠400 := by omega
    have h401 : r≠401 := by omega
    have h402 : r≠402 := by omega
    have h403 : r≠403 := by omega
    have h417 : r≠417 := by omega
    have h431 : r≠431 := by omega
    have h432 : r≠432 := by omega
    have h445 : r≠445 := by omega
    simp [a,setupCode,runCode,step,h207,h231,h232,h400,h401,h402,h403,h417,h431,h432,h445]
  have am : a.realMem=s.realMem := by simp [a,setupCode,runCode,step]
  have an : a.natMem=s.natMem := by simp [a,setupCode,runCode,step]
  have ar : a.realReg=s.realReg := by simp [a,setupCode,runCode,step]
  have abase : a.natReg 207=outsideBase s ∧ a.natReg 231=branchBase s ∧
      a.natReg 445=directBase s ∧ a.natReg 232=arena s := by
    simp [a,setupCode,runCode,step,outsideBase,branchBase,directBase,arena]
  have aps : PhysicalSame s a := ⟨af 500 (by omega),af 501 (by omega),by rw [ar],an,by intro i _;rw [am]⟩
  have fit1 : 2*a.natReg 501≤a.natReg (outputReg .outside) := by rw [af 501 (by omega),outputReg,abase.1];rfl
  obtain ⟨c1,b,he1,hb1,hv1,hn1,hf1,hr1,rr1⟩ := SKPhysicalMatrixStage.execution .outside params input a fit1
    (by simpa [rowLabelReg,rowsReg,af 200 (by omega),af 531 (by omega),af 500 (by omega),an] using houtside)
    (by simpa [colLabelReg,colsReg,af 200 (by omega),af 531 (by omega),af 500 (by omega),an] using houtside)
  have bf (r : ℕ) (hr : StableNat r) : b.natReg r=a.natReg r := hr1 r hr
  have bp := physicalSame_stage .outside a b fit1 hn1 hf1 hr1 rr1
  have bps := aps.trans bp
  have fit2 : 2*b.natReg 501≤b.natReg (outputReg .branch) := by
    rw [bf 501 (by simp [StableNat]),af 501 (by omega),outputReg,bf 231 (by simp [StableNat]),abase.2.1]
    simp [branchBase,outsideBase]
  obtain ⟨c2,d,he2,hb2,hv2,hn2,hf2,hr2,rr2⟩ := SKPhysicalMatrixStage.execution .branch params input b fit2
    (by simpa [rowLabelReg,rowsReg,bf 230 (by simp [StableNat]),bf 530 (by simp [StableNat]),bf 500 (by simp [StableNat]),
      af 230 (by omega),af 530 (by omega),af 500 (by omega),bps.natMem] using hbranch)
    (by simpa [colLabelReg,colsReg,bf 200 (by simp [StableNat]),bf 531 (by simp [StableNat]),bf 500 (by simp [StableNat]),
      af 200 (by omega),af 531 (by omega),af 500 (by omega),bps.natMem] using houtside)
  have df (r : ℕ) (hr : StableNat r) : d.natReg r=a.natReg r := (hr2 r hr).trans (bf r hr)
  have dp := physicalSame_stage .branch b d fit2 hn2 hf2 hr2 rr2
  have dps := bps.trans dp
  have fit3 : 2*d.natReg 501≤d.natReg (outputReg .direct) := by
    rw [df 501 (by simp [StableNat]),af 501 (by omega),outputReg,df 445 (by simp [StableNat]),abase.2.2.1]
    simp only [directBase,branchBase,outsideBase]
    omega
  obtain ⟨c3,t,he3,hb3,hv3,hn3,hf3,hr3,rr3⟩ := SKPhysicalMatrixStage.execution .direct params input d fit3
    (by simpa [rowLabelReg,rowsReg,df 230 (by simp [StableNat]),df 530 (by simp [StableNat]),df 500 (by simp [StableNat]),
      af 230 (by omega),af 530 (by omega),af 500 (by omega),dps.natMem] using hbranch)
    (by simpa [colLabelReg,colsReg,df 230 (by simp [StableNat]),df 530 (by simp [StableNat]),df 500 (by simp [StableNat]),
      af 230 (by omega),af 530 (by omega),af 500 (by omega),dps.natMem] using hbranch)
  have tf (r : ℕ) (hr : StableNat r) : t.natReg r=a.natReg r := (hr3 r hr).trans (df r hr)
  have tp := physicalSame_stage .direct d t fit3 hn3 hf3 hr3 rr3
  have tps := dps.trans tp
  have hepre := exec_code params input setupCode s
  have hpre : codeCost setupCode=48 := by simp [setupCode,codeCost,instrCost]
  rw [hpre] at hepre
  refine ⟨48+(c1+(c2+c3)),t,Exec.seq hepre (Exec.seq he1 (Exec.seq he2 he3)),?_,?_,tps.natMem,?_,?_,?_,?_,?_,?_⟩
  · simp only [rowsReg,colsReg,SKPhysicalMatrix.cost,bf 200 (by simp [StableNat]),bf 230 (by simp [StableNat]),
      bf 500 (by simp [StableNat]),bf 501 (by simp [StableNat]),df 230 (by simp [StableNat]),
      df 500 (by simp [StableNat]),df 501 (by simp [StableNat]),af 200 (by omega),af 230 (by omega),
      af 500 (by omega),af 501 (by omega)] at hb1 hb2 hb3
    simp only [SKPhysicalMatrix.cost,Nat.add_mul]
    omega
  · simp [RootRegisters,tf 200 (by simp [StableNat]),tf 201 (by simp [StableNat]),tf 204 (by simp [StableNat]),
      tf 230 (by simp [StableNat]),tf 207 (by simp [StableNat]),tf 231 (by simp [StableNat]),tf 232 (by simp [StableNat]),
      tf 400 (by simp [StableNat]),tf 401 (by simp [StableNat]),tf 402 (by simp [StableNat]),tf 403 (by simp [StableNat]),
      tf 417 (by simp [StableNat]),a,setupCode,runCode,step,outsideBase,branchBase,directBase,arena]
  · intro i j hi hj
    have hab : outsideBase s+i*s.natReg 200+j<branchBase s := by
      simp only [branchBase]; nlinarith
    have hac : outsideBase s+i*s.natReg 200+j<directBase s := by simp only [directBase];omega
    rw [hf3 _ (Or.inl (by simpa [outputReg,df 445 (by simp [StableNat]),abase.2.2.1] using hac)),
      hf2 _ (Or.inl (by simpa [outputReg,bf 231 (by simp [StableNat]),abase.2.1] using hab))]
    have hh := hv1 i j (by simpa [rowsReg,af 200 (by omega)] using hi) (by simpa [colsReg,af 200 (by omega)] using hj)
    simpa [outputReg,colsReg,rowLabelReg,colLabelReg,abase.1,af 200 (by omega),af 531 (by omega),an,aps.pairValue] using hh
  · intro i j hi hj
    have hab : branchBase s+i*s.natReg 200+j<directBase s := by simp only [directBase];nlinarith
    rw [hf3 _ (Or.inl (by simpa [outputReg,df 445 (by simp [StableNat]),abase.2.2.1] using hab))]
    have hh := hv2 i j (by simpa [rowsReg,bf 230 (by simp [StableNat]),af 230 (by omega)] using hi)
      (by simpa [colsReg,bf 200 (by simp [StableNat]),af 200 (by omega)] using hj)
    simpa [outputReg,colsReg,rowLabelReg,colLabelReg,bf 231 (by simp [StableNat]),bf 200 (by simp [StableNat]),
      bf 530 (by simp [StableNat]),bf 531 (by simp [StableNat]),abase.2.1,af 200 (by omega),af 530 (by omega),
      af 531 (by omega),bps.natMem,bps.pairValue] using hh
  · intro i j hi hj
    have hh := hv3 i j (by simpa [rowsReg,df 230 (by simp [StableNat]),af 230 (by omega)] using hi)
      (by simpa [colsReg,df 230 (by simp [StableNat]),af 230 (by omega)] using hj)
    simpa [outputReg,colsReg,rowLabelReg,colLabelReg,df 445 (by simp [StableNat]),df 230 (by simp [StableNat]),
      df 530 (by simp [StableNat]),abase.2.2.1,af 230 (by omega),af 530 (by omega),dps.natMem,dps.pairValue] using hh
  · intro address haddr
    rw [hf3 _ (Or.inl (by simp only [outputReg,df 445 (by simp [StableNat]),abase.2.2.1,directBase,branchBase,outsideBase];omega)),
      hf2 _ (Or.inl (by simp only [outputReg,bf 231 (by simp [StableNat]),abase.2.1,branchBase,outsideBase];omega)),
      hf1 _ (Or.inl (by simpa only [outputReg,abase.1,outsideBase] using haddr)),am]
  · intro r hr; rw [tf r (by simp only [StableNat];omega),af r (by omega)]
  · intro r hr; rw [rr3 r hr,rr2 r hr,rr1 r hr,ar]

end Manuscript.SKCandidateMatrices
