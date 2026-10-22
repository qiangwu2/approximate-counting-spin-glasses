import Manuscript.SKRestrictedInitialize
import Manuscript.SKRestrictedDirect

noncomputable section
namespace Manuscript.SKRestrictedCombination
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays SKRestrictedAlgebra

def copySetup : List Instruction :=
  [.ncopy 37 30,.nadd 37 37 31,.nadd 37 37 31,.nadd 37 37 31,.ncopy 38 30]
def directSetup : List Instruction := [.ncopy 37 41]
def program : Program := .seq SKRestrictedInitialize.program (.seq SKRestrictedExponential.program
  (.seq (code copySetup) (.seq SKRestrictedCopy.program (.seq (code directSetup) SKRestrictedDirect.program))))

theorem initializer_safe (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) (h37 : r ≠ 37) :
    SKRestrictedInitialize.program.All (fun op => op.natDestination ≠ some r) := by
  simp [SKRestrictedInitialize.program,SKRestrictedInitialize.first,SKRestrictedInitialize.second,
    SKRestrictedOne.program,SKRestrictedOne.setup,SKRestrictedOne.finish,
    RestrictedArrays.program,RestrictedArrays.bodyCode,RestrictedArrays.arithmetic,
    code,Program.All,Instruction.natDestination]
  omega

theorem exponential_safe (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) :
    SKRestrictedExponential.program.All (fun op => op.natDestination ≠ some r) := by
  simp [SKRestrictedExponential.program,SKRestrictedExponential.body,
    SKRestrictedMultiply.program,SKRestrictedMultiply.clearSetup,SKRestrictedMultiply.scatterSetup,
    SKRestrictedScaleAdd.program,SKRestrictedScaleAdd.scaleSetup,SKRestrictedScaleAdd.sumSetup,
    SKRestrictedScatter.program,SKRestrictedScatter.body,SKRestrictedScatter.header,
    SKRestrictedKernels.accumulateBody,RestrictedArrays.program,RestrictedArrays.bodyCode,
    RestrictedArrays.arithmetic,code,Program.All,Instruction.natDestination]
  omega

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset bank iterations : ℕ) (f : Coefficients b K)
    (es : List (Coefficients b K))
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hit : s.natReg 34=iterations) (hone : s.natReg 36=1)
    (hcount : s.natReg 39=es.length) (hbank : s.natReg 41=bank)
    (hseparate : base+4*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hf : SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) f s.realMem)
    (hdata : SKRestrictedDirect.Bank bank es s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ (iterations+es.length)*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+
        90*((K+1)*2^K*6^b)+104 ∧
      SKRestrictedArrays.Represents base
        (SKExponential.directLoop es (SKExponential.expLoop f iterations).2) t.realMem := by
  obtain ⟨c₁,a,ha,bc₁,aready,am⟩ := SKRestrictedInitialize.program_exec params input s base offset f
    hbase hM hoff hpairs hone hrecords hf
  have an (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) (h37 : r ≠ 37) : a.natReg r=s.natReg r :=
    ha.natReg_frame (initializer_safe r hr h35 h37)
  obtain ⟨c₂,d,hd,bc₂,dready,dm⟩ := SKRestrictedExponential.program_exec params input a base offset iterations f
    aready ((an 34 (by omega) (by omega) (by omega)).trans hit)
  have dn (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) (h37 : r ≠ 37) : d.natReg r=s.natReg r :=
    (hd.natReg_frame (exponential_safe r hr h35)).trans (an r hr h35 h37)
  have dbank : SKRestrictedDirect.Bank bank es d.realMem :=
    SKRestrictedDirect.bank_frame _ es s.realMem d.realMem
      (fun address haddress => (dm address (by omega)).trans (am address (by omega))) hdata
  rcases dready with ⟨dbase,dM,doff,dpairs,_,done,drecords,_,_,dsum⟩
  let e := runCode params input copySetup d
  have he : Exec params input (code copySetup) d 16 e := exec_code _ _ _ _
  have en (r : ℕ) (h37 : r ≠ 37) (h38 : r ≠ 38) : e.natReg r=d.natReg r := by
    simp [e,copySetup,runCode,step,h37,h38]
  have esource : e.natReg 37=base+3*((K+1)*2^K*6^b) := by
    simp [e,copySetup,runCode,step,dbase,dM]; omega
  have edest : e.natReg 38=base := by simp [e,copySetup,runCode,step,dbase]
  obtain ⟨c₃,g,hg,bc₃,gacc,gm⟩ := SKRestrictedCopy.program_exec params input e
    (base+3*((K+1)*2^K*6^b)) base (SKExponential.expLoop f iterations).2
    esource edest ((en 31 (by omega) (by omega)).trans dM)
    ((en 36 (by omega) (by omega)).trans done) dsum (by intro i j hi hj; omega)
  have gn (r : ℕ) (hr : 15 ≤ r) (h37 : r ≠ 37) (h38 : r ≠ 38) : g.natReg r=d.natReg r :=
    ((SKRestrictedCopy.program_frame params input hg).1 r hr).trans (en r h37 h38)
  have gnm : g.natMem=d.natMem := (SKRestrictedCopy.program_frame params input hg).2
  have gbank : SKRestrictedDirect.Bank bank es g.realMem :=
    SKRestrictedDirect.bank_frame _ es d.realMem g.realMem
      (fun address haddress => gm address (by intro i hi; omega)) dbank
  let h := runCode params input directSetup g
  have hh : Exec params input (code directSetup) g 2 h := exec_code _ _ _ _
  have hn (r : ℕ) (hr : r ≠ 37) : h.natReg r=g.natReg r := by simp [h,directSetup,runCode,step,hr]
  have hb : h.natReg 37=bank := by
    simp [h,directSetup,runCode,step,gn 41 (by omega) (by omega) (by omega),
      dn 41 (by omega) (by omega) (by omega),hbank]
  obtain ⟨c₄,t,ht,bc₄,tout⟩ := SKRestrictedDirect.program_exec params input base offset es h bank
    (SKExponential.expLoop f iterations).2
    ((hn 30 (by omega)).trans ((gn 30 (by omega) (by omega) (by omega)).trans dbase))
    ((hn 31 (by omega)).trans ((gn 31 (by omega) (by omega) (by omega)).trans dM))
    ((hn 32 (by omega)).trans ((gn 32 (by omega) (by omega) (by omega)).trans doff))
    ((hn 33 (by omega)).trans ((gn 33 (by omega) (by omega) (by omega)).trans dpairs))
    ((hn 36 (by omega)).trans ((gn 36 (by omega) (by omega) (by omega)).trans done)) hb
    ((hn 39 (by omega)).trans ((gn 39 (by omega) (by omega) (by omega)).trans
      ((dn 39 (by omega) (by omega) (by omega)).trans hcount)))
    (by omega) (by change ScheduleMatches _ g.natMem _ _; rwa [gnm]) gacc gbank
  refine ⟨c₁+(c₂+(16+(c₃+(2+c₄)))),t,
    Exec.seq ha (Exec.seq hd (Exec.seq he (Exec.seq hg (Exec.seq hh ht)))),?_,tout⟩
  have hmul : iterations*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102) ≤
      iterations*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul]
  omega

theorem program_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset bank iterations : ℕ) (f : Coefficients b K)
    (es : List (Coefficients b K))
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hit : s.natReg 34=iterations) (hone : s.natReg 36=1)
    (hcount : s.natReg 39=es.length) (hbank : s.natReg 41=bank)
    (hseparate : base+4*((K+1)*2^K*6^b) ≤ bank)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hf : SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) f s.realMem)
    (hdata : SKRestrictedDirect.Bank bank es s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ (iterations+es.length)*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111)+
        90*((K+1)*2^K*6^b)+104 ∧
      SKRestrictedArrays.Represents base
        (SKExponential.directLoop es (SKExponential.expLoop f iterations).2) t.realMem ∧
      (∀ address, address<base → t.realMem address=s.realMem address) := by
  obtain ⟨c₁,a,ha,bc₁,aready,am⟩ := SKRestrictedInitialize.program_exec_framed params input s base offset f
    hbase hM hoff hpairs hone hrecords hf
  have an (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) (h37 : r ≠ 37) : a.natReg r=s.natReg r :=
    ha.natReg_frame (initializer_safe r hr h35 h37)
  obtain ⟨c₂,d,hd,bc₂,dready,dm⟩ := SKRestrictedExponential.program_exec_framed params input a base offset iterations f
    aready ((an 34 (by omega) (by omega) (by omega)).trans hit)
  have dn (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) (h37 : r ≠ 37) : d.natReg r=s.natReg r :=
    (hd.natReg_frame (exponential_safe r hr h35)).trans (an r hr h35 h37)
  have dbank : SKRestrictedDirect.Bank bank es d.realMem :=
    SKRestrictedDirect.bank_frame _ es s.realMem d.realMem
      (fun address haddress => (dm address (by omega)).trans (am address (by omega))) hdata
  rcases dready with ⟨dbase,dM,doff,dpairs,_,done,drecords,_,_,dsum⟩
  let e := runCode params input copySetup d
  have he : Exec params input (code copySetup) d 16 e := exec_code _ _ _ _
  have en (r : ℕ) (h37 : r ≠ 37) (h38 : r ≠ 38) : e.natReg r=d.natReg r := by
    simp [e,copySetup,runCode,step,h37,h38]
  have esource : e.natReg 37=base+3*((K+1)*2^K*6^b) := by
    simp [e,copySetup,runCode,step,dbase,dM]; omega
  have edest : e.natReg 38=base := by simp [e,copySetup,runCode,step,dbase]
  obtain ⟨c₃,g,hg,bc₃,gacc,gm⟩ := SKRestrictedCopy.program_exec params input e
    (base+3*((K+1)*2^K*6^b)) base (SKExponential.expLoop f iterations).2
    esource edest ((en 31 (by omega) (by omega)).trans dM)
    ((en 36 (by omega) (by omega)).trans done) dsum (by intro i j hi hj; omega)
  have gn (r : ℕ) (hr : 15 ≤ r) (h37 : r ≠ 37) (h38 : r ≠ 38) : g.natReg r=d.natReg r :=
    ((SKRestrictedCopy.program_frame params input hg).1 r hr).trans (en r h37 h38)
  have gnm : g.natMem=d.natMem := (SKRestrictedCopy.program_frame params input hg).2
  have gbank : SKRestrictedDirect.Bank bank es g.realMem :=
    SKRestrictedDirect.bank_frame _ es d.realMem g.realMem
      (fun address haddress => gm address (by intro i hi; omega)) dbank
  let h := runCode params input directSetup g
  have hh : Exec params input (code directSetup) g 2 h := exec_code _ _ _ _
  have hn (r : ℕ) (hr : r ≠ 37) : h.natReg r=g.natReg r := by simp [h,directSetup,runCode,step,hr]
  have hb : h.natReg 37=bank := by
    simp [h,directSetup,runCode,step,gn 41 (by omega) (by omega) (by omega),
      dn 41 (by omega) (by omega) (by omega),hbank]
  obtain ⟨c₄,t,ht,bc₄,tout,tm⟩ := SKRestrictedDirect.program_exec_framed params input base offset es h bank
    (SKExponential.expLoop f iterations).2
    ((hn 30 (by omega)).trans ((gn 30 (by omega) (by omega) (by omega)).trans dbase))
    ((hn 31 (by omega)).trans ((gn 31 (by omega) (by omega) (by omega)).trans dM))
    ((hn 32 (by omega)).trans ((gn 32 (by omega) (by omega) (by omega)).trans doff))
    ((hn 33 (by omega)).trans ((gn 33 (by omega) (by omega) (by omega)).trans dpairs))
    ((hn 36 (by omega)).trans ((gn 36 (by omega) (by omega) (by omega)).trans done)) hb
    ((hn 39 (by omega)).trans ((gn 39 (by omega) (by omega) (by omega)).trans
      ((dn 39 (by omega) (by omega) (by omega)).trans hcount)))
    (by omega) (by change ScheduleMatches _ g.natMem _ _; rwa [gnm]) gacc gbank
  refine ⟨c₁+(c₂+(16+(c₃+(2+c₄)))),t,
    Exec.seq ha (Exec.seq hd (Exec.seq he (Exec.seq hg (Exec.seq hh ht)))),?_,tout,?_⟩
  swap
  · intro address haddr
    rw [tm address haddr]
    change g.realMem address=s.realMem address
    rw [gm address (by intro i hi; omega)]
    change d.realMem address=s.realMem address
    rw [dm address (Or.inl haddr),am address (Or.inl haddr)]
  have hmul : iterations*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+102) ≤
      iterations*(56*((K+1)*2^K*6^b)^2+90*((K+1)*2^K*6^b)+111) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul]
  omega

end Manuscript.SKRestrictedCombination
