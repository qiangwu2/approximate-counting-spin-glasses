import Manuscript.SKRestrictedCopy
import Manuscript.SKRestrictedMultiply
import Manuscript.SKRestrictedOne

noncomputable section
namespace Manuscript.SKRestrictedDirectStep
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays SKRestrictedAlgebra

def first : List Instruction := [.ncopy 40 37,.ncopy 38 30,.nadd 38 38 31]
def addOne : List Instruction :=
  [.ncopy 12 30,.nadd 12 12 31,.loadReal 0 12,.rconst 1 1,.radd 0 1 0,.storeReal 12 0]
def second : List Instruction :=
  [.ncopy 37 30,.nadd 37 37 31,.nadd 37 37 31,.ncopy 38 30]
def finish : List Instruction := [.nadd 37 40 31]
def program : Program := .seq (code first) (.seq SKRestrictedCopy.program
  (.seq (code addOne) (.seq SKRestrictedMultiply.program
    (.seq (code second) (.seq SKRestrictedCopy.program (code finish))))))

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset bank : ℕ) (acc edge : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1) (hbank : s.natReg 37=bank)
    (hseparate : base+3*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hacc : SKRestrictedArrays.Represents base acc s.realMem)
    (hedge : SKRestrictedArrays.Represents bank edge s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+106 ∧
      SKRestrictedArrays.Represents base (SKCoefficient.mul acc (one b K+edge)) t.realMem ∧
      t.natReg 37=bank+(K+1)*2^K*6^b ∧
      (∀ r, 15 ≤ r → r ≠ 37 → r ≠ 38 → r ≠ 40 → t.natReg r=s.natReg r) ∧
      t.natMem=s.natMem ∧
      (∀ address, base+3*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  let M := (K+1)*2^K*6^b
  let a := runCode params input first s
  have ha : Exec params input (code first) s 8 a := exec_code _ _ _ _
  have an (r : ℕ) (h38 : r ≠ 38) (h40 : r ≠ 40) : a.natReg r=s.natReg r := by
    simp [a,first,runCode,step,h38,h40]
  have ap : a.natReg 38=base+M := by simp [a,first,runCode,step,hbase,hM,M]
  have ab : a.natReg 40=bank := by simp [a,first,runCode,step,hbank]
  obtain ⟨c₁,d,hd,bc₁,de,dm⟩ := SKRestrictedCopy.program_exec params input a bank (base+M) edge
    ((an 37 (by decide) (by decide)).trans hbank) ap
    ((an 31 (by decide) (by decide)).trans hM) ((an 36 (by decide) (by decide)).trans hone)
    hedge (by intro i j hi hj; dsimp [M] at *; omega)
  have dn (r : ℕ) (hr : 15 ≤ r) (h38 : r ≠ 38) (h40 : r ≠ 40) : d.natReg r=s.natReg r :=
    ((SKRestrictedCopy.program_frame params input hd).1 r hr).trans (an r h38 h40)
  have db : d.natReg 40=bank := ((SKRestrictedCopy.program_frame params input hd).1 40 (by omega)).trans ab
  have dnm : d.natMem=s.natMem := (SKRestrictedCopy.program_frame params input hd).2
  let e := runCode params input addOne d
  have he : Exec params input (code addOne) d 17 e := exec_code _ _ _ _
  have en (r : ℕ) (hr : 15 ≤ r) : e.natReg r=d.natReg r := by
    apply he.natReg_frame
    simp [addOne,code,Program.All,Instruction.natDestination]; omega
  have em : e.realMem=Function.update d.realMem (base+M) (1+d.realMem (base+M)) := by
    simp [e,addOne,runCode,step,writeRealMem,dn 30 (by omega) (by omega) (by omega),
      dn 31 (by omega) (by omega) (by omega),hbase,hM,M]
  have ef : SKRestrictedArrays.Represents (base+M) (one b K+edge) e.realMem := by
    intro x
    rw [em,Pi.add_apply,SKRestrictedOne.one_formula]
    by_cases hx : encode x=0
    · simpa [hx] using congrArg (fun v : ℝ => 1+v) (de x)
    · rw [Function.update_of_ne (by omega : base+M+encode x ≠ base+M)]
      simpa [hx] using de x
  have ea : SKRestrictedArrays.Represents base acc e.realMem := by
    intro x
    have hx := encode_lt x
    rw [em,Function.update_of_ne (by dsimp [M]; omega)]
    rw [dm _ (by intro i hi; dsimp [M] at *; omega)]
    exact hacc x
  obtain ⟨c₂,g,hg,bc₂,gprod,gm⟩ := SKRestrictedMultiply.program_exec params input e base offset acc
    (one b K+edge)
    ((en 30 (by omega)).trans ((dn 30 (by omega) (by omega) (by omega)).trans hbase))
    ((en 31 (by omega)).trans ((dn 31 (by omega) (by omega) (by omega)).trans hM))
    ((en 32 (by omega)).trans ((dn 32 (by omega) (by omega) (by omega)).trans hoff))
    ((en 33 (by omega)).trans ((dn 33 (by omega) (by omega) (by omega)).trans hpairs))
    ((en 36 (by omega)).trans ((dn 36 (by omega) (by omega) (by omega)).trans hone)) ea ef
    (by change ScheduleMatches _ d.natMem _ _; rwa [dnm])
  have gn (r : ℕ) (hr : 15 ≤ r) : g.natReg r=d.natReg r :=
    ((SKRestrictedMultiply.program_frame params input hg).1 r hr).trans (en r hr)
  have gnm : g.natMem=s.natMem := (SKRestrictedMultiply.program_frame params input hg).2.trans dnm
  let h := runCode params input second g
  have hh : Exec params input (code second) g 12 h := exec_code _ _ _ _
  have hn (r : ℕ) (h37 : r ≠ 37) (h38 : r ≠ 38) : h.natReg r=g.natReg r := by
    simp [h,second,runCode,step,h37,h38]
  have hp : h.natReg 37=base+2*M := by
    simp [h,second,runCode,step,gn 30 (by omega),gn 31 (by omega),
      dn 30 (by omega) (by omega) (by omega),dn 31 (by omega) (by omega) (by omega),hbase,hM,M]; omega
  have hdest : h.natReg 38=base := by
    simp [h,second,runCode,step,gn 30 (by omega),dn 30 (by omega) (by omega) (by omega),hbase]
  obtain ⟨c₃,j,hj,bc₃,ja,jm⟩ := SKRestrictedCopy.program_exec params input h (base+2*M) base
    (SKCoefficient.mul acc (one b K+edge)) hp hdest
    ((hn 31 (by omega) (by omega)).trans ((gn 31 (by omega)).trans ((dn 31 (by omega) (by omega) (by omega)).trans hM)))
    ((hn 36 (by omega) (by omega)).trans ((gn 36 (by omega)).trans ((dn 36 (by omega) (by omega) (by omega)).trans hone)))
    gprod.2.2 (by intro i k hi hk; dsimp [M] at *; omega)
  have jn (r : ℕ) (hr : 15 ≤ r) : j.natReg r=h.natReg r :=
    (SKRestrictedCopy.program_frame params input hj).1 r hr
  let t := runCode params input finish j
  have ht : Exec params input (code finish) j 4 t := exec_code _ _ _ _
  have tm : t.realMem=j.realMem := rfl
  refine ⟨8+(c₁+(17+(c₂+(12+(c₃+4))))),t,
    Exec.seq ha (Exec.seq hd (Exec.seq he (Exec.seq hg (Exec.seq hh (Exec.seq hj ht))))),
    by omega,ja,?_,?_,?_,?_⟩
  · simp [t,finish,runCode,step,jn 40 (by omega),jn 31 (by omega),hn 40 (by omega) (by omega),
      hn 31 (by omega) (by omega),gn 40 (by omega),gn 31 (by omega),db,
      dn 31 (by omega) (by omega) (by omega),hM]
  · intro r hr h37 h38 h40
    simp only [t,finish,runCode,step,writeNatReg_natReg,if_neg h37]
    exact (jn r hr).trans ((hn r h37 h38).trans ((gn r hr).trans (dn r hr h38 h40)))
  · change j.natMem=s.natMem
    rw [(SKRestrictedCopy.program_frame params input hj).2]
    exact gnm
  · intro address haddr
    rw [tm,jm _ (by intro i hi; dsimp [M] at *; omega)]
    change g.realMem address=s.realMem address
    rw [gm _ (by intro i hi; dsimp [M] at *; omega),em]
    have Mpos : 0 < M := by dsimp [M]; positivity
    rw [Function.update_of_ne (by dsimp [M] at *; omega)]
    rw [dm _ (by intro i hi; dsimp [M] at *; omega)]
    rfl

theorem program_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset bank : ℕ) (acc edge : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1) (hbank : s.natReg 37=bank)
    (hseparate : base+3*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hacc : SKRestrictedArrays.Represents base acc s.realMem)
    (hedge : SKRestrictedArrays.Represents bank edge s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+106 ∧
      SKRestrictedArrays.Represents base (SKCoefficient.mul acc (one b K+edge)) t.realMem ∧
      t.natReg 37=bank+(K+1)*2^K*6^b ∧
      (∀ r, 15 ≤ r → r ≠ 37 → r ≠ 38 → r ≠ 40 → t.natReg r=s.natReg r) ∧
      t.natMem=s.natMem ∧
      (∀ address, address<base ∨ base+3*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  let M := (K+1)*2^K*6^b
  let a := runCode params input first s
  have ha : Exec params input (code first) s 8 a := exec_code _ _ _ _
  have an (r : ℕ) (h38 : r ≠ 38) (h40 : r ≠ 40) : a.natReg r=s.natReg r := by
    simp [a,first,runCode,step,h38,h40]
  have ap : a.natReg 38=base+M := by simp [a,first,runCode,step,hbase,hM,M]
  have ab : a.natReg 40=bank := by simp [a,first,runCode,step,hbank]
  obtain ⟨c₁,d,hd,bc₁,de,dm⟩ := SKRestrictedCopy.program_exec params input a bank (base+M) edge
    ((an 37 (by decide) (by decide)).trans hbank) ap
    ((an 31 (by decide) (by decide)).trans hM) ((an 36 (by decide) (by decide)).trans hone)
    hedge (by intro i j hi hj; dsimp [M] at *; omega)
  have dn (r : ℕ) (hr : 15 ≤ r) (h38 : r ≠ 38) (h40 : r ≠ 40) : d.natReg r=s.natReg r :=
    ((SKRestrictedCopy.program_frame params input hd).1 r hr).trans (an r h38 h40)
  have db : d.natReg 40=bank := ((SKRestrictedCopy.program_frame params input hd).1 40 (by omega)).trans ab
  have dnm : d.natMem=s.natMem := (SKRestrictedCopy.program_frame params input hd).2
  let e := runCode params input addOne d
  have he : Exec params input (code addOne) d 17 e := exec_code _ _ _ _
  have en (r : ℕ) (hr : 15 ≤ r) : e.natReg r=d.natReg r := by
    apply he.natReg_frame
    simp [addOne,code,Program.All,Instruction.natDestination]; omega
  have em : e.realMem=Function.update d.realMem (base+M) (1+d.realMem (base+M)) := by
    simp [e,addOne,runCode,step,writeRealMem,dn 30 (by omega) (by omega) (by omega),
      dn 31 (by omega) (by omega) (by omega),hbase,hM,M]
  have ef : SKRestrictedArrays.Represents (base+M) (one b K+edge) e.realMem := by
    intro x
    rw [em,Pi.add_apply,SKRestrictedOne.one_formula]
    by_cases hx : encode x=0
    · simpa [hx] using congrArg (fun v : ℝ => 1+v) (de x)
    · rw [Function.update_of_ne (by omega : base+M+encode x ≠ base+M)]
      simpa [hx] using de x
  have ea : SKRestrictedArrays.Represents base acc e.realMem := by
    intro x
    have hx := encode_lt x
    rw [em,Function.update_of_ne (by dsimp [M]; omega)]
    rw [dm _ (by intro i hi; dsimp [M] at *; omega)]
    exact hacc x
  obtain ⟨c₂,g,hg,bc₂,gprod,gm⟩ := SKRestrictedMultiply.program_exec params input e base offset acc
    (one b K+edge)
    ((en 30 (by omega)).trans ((dn 30 (by omega) (by omega) (by omega)).trans hbase))
    ((en 31 (by omega)).trans ((dn 31 (by omega) (by omega) (by omega)).trans hM))
    ((en 32 (by omega)).trans ((dn 32 (by omega) (by omega) (by omega)).trans hoff))
    ((en 33 (by omega)).trans ((dn 33 (by omega) (by omega) (by omega)).trans hpairs))
    ((en 36 (by omega)).trans ((dn 36 (by omega) (by omega) (by omega)).trans hone)) ea ef
    (by change ScheduleMatches _ d.natMem _ _; rwa [dnm])
  have gn (r : ℕ) (hr : 15 ≤ r) : g.natReg r=d.natReg r :=
    ((SKRestrictedMultiply.program_frame params input hg).1 r hr).trans (en r hr)
  have gnm : g.natMem=s.natMem := (SKRestrictedMultiply.program_frame params input hg).2.trans dnm
  let h := runCode params input second g
  have hh : Exec params input (code second) g 12 h := exec_code _ _ _ _
  have hn (r : ℕ) (h37 : r ≠ 37) (h38 : r ≠ 38) : h.natReg r=g.natReg r := by
    simp [h,second,runCode,step,h37,h38]
  have hp : h.natReg 37=base+2*M := by
    simp [h,second,runCode,step,gn 30 (by omega),gn 31 (by omega),
      dn 30 (by omega) (by omega) (by omega),dn 31 (by omega) (by omega) (by omega),hbase,hM,M]; omega
  have hdest : h.natReg 38=base := by
    simp [h,second,runCode,step,gn 30 (by omega),dn 30 (by omega) (by omega) (by omega),hbase]
  obtain ⟨c₃,j,hj,bc₃,ja,jm⟩ := SKRestrictedCopy.program_exec params input h (base+2*M) base
    (SKCoefficient.mul acc (one b K+edge)) hp hdest
    ((hn 31 (by omega) (by omega)).trans ((gn 31 (by omega)).trans ((dn 31 (by omega) (by omega) (by omega)).trans hM)))
    ((hn 36 (by omega) (by omega)).trans ((gn 36 (by omega)).trans ((dn 36 (by omega) (by omega) (by omega)).trans hone)))
    gprod.2.2 (by intro i k hi hk; dsimp [M] at *; omega)
  have jn (r : ℕ) (hr : 15 ≤ r) : j.natReg r=h.natReg r :=
    (SKRestrictedCopy.program_frame params input hj).1 r hr
  let t := runCode params input finish j
  have ht : Exec params input (code finish) j 4 t := exec_code _ _ _ _
  have tm : t.realMem=j.realMem := rfl
  refine ⟨8+(c₁+(17+(c₂+(12+(c₃+4))))),t,
    Exec.seq ha (Exec.seq hd (Exec.seq he (Exec.seq hg (Exec.seq hh (Exec.seq hj ht))))),
    by omega,ja,?_,?_,?_,?_⟩
  · simp [t,finish,runCode,step,jn 40 (by omega),jn 31 (by omega),hn 40 (by omega) (by omega),
      hn 31 (by omega) (by omega),gn 40 (by omega),gn 31 (by omega),db,
      dn 31 (by omega) (by omega) (by omega),hM]
  · intro r hr h37 h38 h40
    simp only [t,finish,runCode,step,writeNatReg_natReg,if_neg h37]
    exact (jn r hr).trans ((hn r h37 h38).trans ((gn r hr).trans (dn r hr h38 h40)))
  · change j.natMem=s.natMem
    rw [(SKRestrictedCopy.program_frame params input hj).2]
    exact gnm
  · intro address haddr
    rw [tm,jm _ (by intro i hi; dsimp [M] at *; omega)]
    change g.realMem address=s.realMem address
    rw [gm _ (by intro i hi; dsimp [M] at *; omega),em]
    have Mpos : 0 < M := by dsimp [M]; positivity
    rw [Function.update_of_ne (by dsimp [M] at *; omega)]
    rw [dm _ (by intro i hi; dsimp [M] at *; omega)]
    rfl

end Manuscript.SKRestrictedDirectStep
