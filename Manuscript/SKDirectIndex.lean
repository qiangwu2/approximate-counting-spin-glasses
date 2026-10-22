import Manuscript.RestrictedIndices
import Manuscript.SKChargedExecution
import Manuscript.SKBasisEncoding

noncomputable section
set_option maxHeartbeats 1600000
namespace Manuscript.SKDirectIndex
open RestrictedMachine IndexGeneration SpinGlass SKCoefficient SKBasisEncoding
open scoped BigOperators

def first : List Instruction := [.nconst 130 6,.ncopy 131 442]
def second : List Instruction := [.ncopy 450 132,.ncopy 131 443]
def finish : List Instruction :=
  [.nadd 451 444 442,.loadNat 452 451,.nadd 451 444 443,.loadNat 453 451,
   .nconst 454 0,.neq 452 452 454,.neq 453 453 454,
   .nconst 455 1,.nsub 452 455 452,.nsub 453 455 453,.nmul 456 452 453,
   .nmul 456 456 447,.nmul 456 456 448,.nadd 42 456 450,.nadd 42 42 132,
   .nmul 457 442 440,.nadd 457 457 443,.nadd 457 445 457,.loadReal 42 457]
def program : Program := .seq (code first) (.seq powerProgram
  (.seq (code second) (.seq powerProgram (code finish))))

theorem power_frames (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input powerProgram s c t) :
    (∀ r, r≠132 → t.natReg r=s.natReg r) ∧ t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  refine ⟨?_,?_,?_⟩
  · intro r hr; apply he.natReg_frame
    simp [powerProgram,powerInit,powerBody,code,Program.All,Instruction.natDestination,Ne.symm hr]
  · apply he.realMem_frame
    simp [powerProgram,powerInit,powerBody,code,Program.All,Instruction.writesRealMemory]
  · apply he.natMem_frame
    simp [powerProgram,powerInit,powerBody,code,Program.All,Instruction.writesNatMemory]

theorem program_exec (params : Parameters) (input : Inputs) (s : State) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 9*(s.natReg 442+s.natReg 443)+86 ∧
      t.natReg 42=(if s.natMem (s.natReg 444+s.natReg 442)=0 ∨
          s.natMem (s.natReg 444+s.natReg 443)=0 then 0 else 1)*
          s.natReg 447*s.natReg 448+6^s.natReg 442+6^s.natReg 443 ∧
      t.realReg 42=s.realMem (s.natReg 445+s.natReg 442*s.natReg 440+s.natReg 443) ∧
      t.realMem=s.realMem ∧ t.natMem=s.natMem := by
  let u := runCode params input first s
  have hu : Exec params input (code first) s 3 u := exec_code _ _ _ _
  obtain ⟨c,v,hv,hc,hpow⟩ := power_execution params input u
  have vn (r : ℕ) (hr : r≠132) : v.natReg r=u.natReg r := (power_frames params input hv).1 r hr
  have vm := (power_frames params input hv).2.1
  have vnm := (power_frames params input hv).2.2
  have vp : v.natReg 132=6^s.natReg 442 := by simpa [u,first,runCode,step] using hpow
  let w := runCode params input second v
  have hw : Exec params input (code second) v 4 w := exec_code _ _ _ _
  obtain ⟨d,x,hx,hd,hpow2⟩ := power_execution params input w
  have xn (r : ℕ) (hr : r≠132) : x.natReg r=w.natReg r := (power_frames params input hx).1 r hr
  have xm : x.realMem=s.realMem := (power_frames params input hx).2.1.trans vm
  have xnm : x.natMem=s.natMem := (power_frames params input hx).2.2.trans vnm
  have xp : x.natReg 132=6^s.natReg 443 := by
    simpa [w,second,runCode,step,vn 130 (by omega),vn 443 (by omega),u,first] using hpow2
  have xsave : x.natReg 450=6^s.natReg 442 := by
    simpa [w,second,runCode,step,vp] using xn 450 (by omega)
  have xhigh (r : ℕ) (hr : 440≤r) (h450 : r≠450) : x.natReg r=s.natReg r := by
    rw [xn r (by omega)]
    change (runCode params input second v).natReg r=s.natReg r
    have hh : w.natReg r=v.natReg r := hw.natReg_frame (by
      simp [second,code,Program.All,Instruction.natDestination]; omega)
    rw [hh,vn r (by omega)]
    exact hu.natReg_frame (by simp [first,code,Program.All,Instruction.natDestination]; omega)
  let t := runCode params input finish x
  have ht : Exec params input (code finish) x 67 t := exec_code _ _ _ _
  refine ⟨3+(c+(4+(d+67))),t,Exec.seq hu (Exec.seq hv (Exec.seq hw (Exec.seq hx ht))),?_,?_,?_,?_,?_⟩
  · have c' : c≤9*s.natReg 442+6 := by simpa [u,first,runCode,step] using hc
    have d' : d≤9*s.natReg 443+6 := by
      simpa [w,second,runCode,step,vn 443 (by omega),u,first] using hd
    omega
  · by_cases ha : s.natMem (s.natReg 444+s.natReg 442)=0 <;>
      by_cases hb : s.natMem (s.natReg 444+s.natReg 443)=0 <;>
      simp [t,finish,runCode,step,xnm,xp,xsave,xhigh 444 (by omega) (by omega),
        xhigh 442 (by omega) (by omega),xhigh 443 (by omega) (by omega),
        xhigh 447 (by omega) (by omega),xhigh 448 (by omega) (by omega),ha,hb,Nat.add_assoc]
  · simp [t,finish,runCode,step,xm,xhigh 442 (by omega) (by omega),
      xhigh 443 (by omega) (by omega),xhigh 440 (by omega) (by omega),
      xhigh 445 (by omega) (by omega),Nat.add_assoc]
  · simpa [t,finish,runCode,step] using xm
  · simpa [t,finish,runCode,step] using xnm

theorem path_degree_index {b : ℕ} (a c : Fin b) (hac : a≠c) :
    (degreeEquiv b (SKFastEvaluator.pathDegrees a c)).val=6^a.val+6^c.val := by
  rw [degree_formula]
  have term (i : Fin b) : (SKFastEvaluator.pathDegrees a c i).val*6^i.val =
      (if i=a then 6^i.val else 0)+(if i=c then 6^i.val else 0) := by
    by_cases ha : i=a <;> by_cases hc : i=c
    · exact False.elim (hac (ha.symm.trans hc))
    all_goals simp [SKFastEvaluator.pathDegrees,ha,hc,hac,Ne.symm hac,
      CappedDegree.ofNat,CappedDegree.val,SpinGlass.rho]
  simp_rw [term]
  rw [Finset.sum_add_distrib]
  simp

end Manuscript.SKDirectIndex
