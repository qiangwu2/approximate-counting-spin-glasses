import Manuscript.SKRestrictedOne
import Manuscript.SKRestrictedExponential

noncomputable section
namespace Manuscript.SKRestrictedInitialize
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays SKRestrictedAlgebra

def first : List Instruction := [.ncopy 37 30]
def second : List Instruction :=
  [.ncopy 37 30, .nadd 37 37 31, .nadd 37 37 31, .nadd 37 37 31]
def program : Program := .seq (code first) (.seq SKRestrictedOne.program
  (.seq (code second) (.seq SKRestrictedOne.program (.atom (.nconst 35 0)))))

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset : ℕ) (f : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hf : SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) f s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 60*((K+1)*2^K*6^b)+61 ∧
      SKRestrictedExponential.Ready base offset 0 f t ∧
      (∀ address, base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  let u := runCode params input first s
  have hu : Exec params input (code first) s 2 u := exec_code _ _ _ _
  have up : u.natReg 37=base := by simp [u,first,runCode,step,hbase]
  have un (r : ℕ) (hr : r ≠ 37) : u.natReg r=s.natReg r := by simp [u,first,runCode,step,hr]
  obtain ⟨c₁,v,hv,bc₁,vpower,vm⟩ := SKRestrictedOne.program_exec (b:=b) (K:=K) params input u base up
    ((un 31 (by decide)).trans hM) ((un 36 (by decide)).trans hone)
  have vn (r : ℕ) (hr : 15 ≤ r) (hr37 : r ≠ 37) : v.natReg r=s.natReg r :=
    ((SKRestrictedOne.program_frame params input hv).1 r hr).trans (un r hr37)
  have vnm : v.natMem=s.natMem := (SKRestrictedOne.program_frame params input hv).2
  let w := runCode params input second v
  have hw : Exec params input (code second) v 14 w := exec_code _ _ _ _
  have wp : w.natReg 37=base+3*((K+1)*2^K*6^b) := by
    simp [w,second,runCode,step,vn 30 (by omega) (by omega),vn 31 (by omega) (by omega),hbase,hM]; omega
  have wn (r : ℕ) (hr : 15 ≤ r) (hr37 : r ≠ 37) : w.natReg r=s.natReg r := by
    have hframe := hw.natReg_frame (r:=r) (by simp [second,code,Program.All,Instruction.natDestination,Ne.symm hr37])
    exact hframe.trans (vn r hr hr37)
  obtain ⟨c₂,z,hz,bc₂,zsum,zm⟩ := SKRestrictedOne.program_exec (b:=b) (K:=K) params input w
    (base+3*((K+1)*2^K*6^b)) wp ((wn 31 (by omega) (by omega)).trans hM)
    ((wn 36 (by omega) (by omega)).trans hone)
  let t := step params input (.nconst 35 0) z
  have ht : Exec params input (.atom (.nconst 35 0)) z 1 t := Exec.atom _ _
  have tn (r : ℕ) (hr : 15 ≤ r) (hr37 : r ≠ 37) (hr35 : r ≠ 35) : t.natReg r=s.natReg r := by
    simp only [t,step,writeNatReg_natReg,if_neg hr35]
    exact ((SKRestrictedOne.program_frame params input hz).1 r hr).trans (wn r hr hr37)
  have tnm : t.natMem=s.natMem := by
    change z.natMem=s.natMem
    rw [(SKRestrictedOne.program_frame params input hz).2]
    exact vnm
  refine ⟨2+(c₁+(14+(c₂+1))),t,
    Exec.seq hu (Exec.seq hv (Exec.seq hw (Exec.seq hz ht))),by omega,?_,?_⟩
  swap
  · intro address ha
    change z.realMem address=s.realMem address
    rw [zm _ (by intro i hi; omega)]
    change v.realMem address=s.realMem address
    rw [vm _ (by intro i hi; omega)]
    rfl
  refine ⟨(tn 30 (by omega) (by omega) (by omega)).trans hbase,
    (tn 31 (by omega) (by omega) (by omega)).trans hM,
    (tn 32 (by omega) (by omega) (by omega)).trans hoff,
    (tn 33 (by omega) (by omega) (by omega)).trans hpairs,
    by simp [t,step],(tn 36 (by omega) (by omega) (by omega)).trans hone,
    by rwa [tnm],?_,?_,zsum⟩
  · intro x
    change z.realMem (base+encode x)=one b K x
    rw [zm _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact vpower x
  · intro x
    change z.realMem (base+(K+1)*2^K*6^b+encode x)=f x
    rw [zm _ (by intro i hi; have hx:=encode_lt x; omega)]
    change v.realMem (base+(K+1)*2^K*6^b+encode x)=f x
    rw [vm _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact hf x

theorem program_exec_framed {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base offset : ℕ) (f : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hoff : s.natReg 32=offset) (hpairs : s.natReg 33=((K+1)*2^K*6^b)^2)
    (hone : s.natReg 36=1)
    (hrecords : ScheduleMatches (denseLayout b K base) s.natMem offset (pairList b K))
    (hf : SKRestrictedArrays.Represents (base+(K+1)*2^K*6^b) f s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 60*((K+1)*2^K*6^b)+61 ∧
      SKRestrictedExponential.Ready base offset 0 f t ∧
      (∀ address, address<base ∨ base+4*((K+1)*2^K*6^b) ≤ address → t.realMem address=s.realMem address) := by
  let u := runCode params input first s
  have hu : Exec params input (code first) s 2 u := exec_code _ _ _ _
  have up : u.natReg 37=base := by simp [u,first,runCode,step,hbase]
  have un (r : ℕ) (hr : r ≠ 37) : u.natReg r=s.natReg r := by simp [u,first,runCode,step,hr]
  obtain ⟨c₁,v,hv,bc₁,vpower,vm⟩ := SKRestrictedOne.program_exec (b:=b) (K:=K) params input u base up
    ((un 31 (by decide)).trans hM) ((un 36 (by decide)).trans hone)
  have vn (r : ℕ) (hr : 15 ≤ r) (hr37 : r ≠ 37) : v.natReg r=s.natReg r :=
    ((SKRestrictedOne.program_frame params input hv).1 r hr).trans (un r hr37)
  have vnm : v.natMem=s.natMem := (SKRestrictedOne.program_frame params input hv).2
  let w := runCode params input second v
  have hw : Exec params input (code second) v 14 w := exec_code _ _ _ _
  have wp : w.natReg 37=base+3*((K+1)*2^K*6^b) := by
    simp [w,second,runCode,step,vn 30 (by omega) (by omega),vn 31 (by omega) (by omega),hbase,hM]; omega
  have wn (r : ℕ) (hr : 15 ≤ r) (hr37 : r ≠ 37) : w.natReg r=s.natReg r := by
    have hframe := hw.natReg_frame (r:=r) (by simp [second,code,Program.All,Instruction.natDestination,Ne.symm hr37])
    exact hframe.trans (vn r hr hr37)
  obtain ⟨c₂,z,hz,bc₂,zsum,zm⟩ := SKRestrictedOne.program_exec (b:=b) (K:=K) params input w
    (base+3*((K+1)*2^K*6^b)) wp ((wn 31 (by omega) (by omega)).trans hM)
    ((wn 36 (by omega) (by omega)).trans hone)
  let t := step params input (.nconst 35 0) z
  have ht : Exec params input (.atom (.nconst 35 0)) z 1 t := Exec.atom _ _
  have tn (r : ℕ) (hr : 15 ≤ r) (hr37 : r ≠ 37) (hr35 : r ≠ 35) : t.natReg r=s.natReg r := by
    simp only [t,step,writeNatReg_natReg,if_neg hr35]
    exact ((SKRestrictedOne.program_frame params input hz).1 r hr).trans (wn r hr hr37)
  have tnm : t.natMem=s.natMem := by
    change z.natMem=s.natMem
    rw [(SKRestrictedOne.program_frame params input hz).2]
    exact vnm
  refine ⟨2+(c₁+(14+(c₂+1))),t,
    Exec.seq hu (Exec.seq hv (Exec.seq hw (Exec.seq hz ht))),by omega,?_,?_⟩
  swap
  · intro address ha
    change z.realMem address=s.realMem address
    rw [zm _ (by intro i hi; omega)]
    change v.realMem address=s.realMem address
    rw [vm _ (by intro i hi; omega)]
    rfl
  refine ⟨(tn 30 (by omega) (by omega) (by omega)).trans hbase,
    (tn 31 (by omega) (by omega) (by omega)).trans hM,
    (tn 32 (by omega) (by omega) (by omega)).trans hoff,
    (tn 33 (by omega) (by omega) (by omega)).trans hpairs,
    by simp [t,step],(tn 36 (by omega) (by omega) (by omega)).trans hone,
    by rwa [tnm],?_,?_,zsum⟩
  · intro x
    change z.realMem (base+encode x)=one b K x
    rw [zm _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact vpower x
  · intro x
    change z.realMem (base+(K+1)*2^K*6^b+encode x)=f x
    rw [zm _ (by intro i hi; have hx:=encode_lt x; omega)]
    change v.realMem (base+(K+1)*2^K*6^b+encode x)=f x
    rw [vm _ (by intro i hi; have hx:=encode_lt x; omega)]
    exact hf x

end Manuscript.SKRestrictedInitialize
