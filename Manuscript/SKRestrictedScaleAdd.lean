import Manuscript.SKRestrictedArrays
import SpinGlass.SKExponential

noncomputable section
namespace Manuscript.SKRestrictedScaleAdd
open RestrictedMachine SpinGlass SKCoefficient SKBasisEncoding SKRestrictedArrays

def scaleSetup : List Instruction :=
  [.ncopy 10 30, .nadd 10 10 31, .nadd 10 10 31,
   .ncopy 11 10, .ncopy 12 30, .ncopy 13 36, .ncopy 14 31,
   .nadd 35 35 36, .natToReal 4 35, .rconst 5 1, .rdiv 4 5 4]
def sumSetup : List Instruction :=
  [.ncopy 10 30, .nadd 10 10 31, .nadd 10 10 31, .nadd 10 10 31,
   .ncopy 11 30, .ncopy 12 10, .ncopy 13 36, .ncopy 14 31]
def program : Program := .seq (code scaleSetup)
  (.seq (RestrictedArrays.program .scale)
    (.seq (code sumSetup) (RestrictedArrays.program .add)))

theorem setup_costs : codeCost scaleSetup=30 ∧ codeCost sumSetup=22 := by
  norm_num [scaleSetup,sumSetup,codeCost,instrCost]

theorem program_frame (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input program s c t) :
    (∀ r, 15 ≤ r → r ≠ 35 → t.natReg r=s.natReg r) ∧
    t.natMem=s.natMem := by
  refine ⟨?_,?_⟩
  · intro r hr h35
    apply he.natReg_frame
    simp [program,scaleSetup,sumSetup,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.natDestination]
    omega
  · apply he.natMem_frame
    simp [program,scaleSetup,sumSetup,RestrictedArrays.program,RestrictedArrays.bodyCode,
      RestrictedArrays.arithmetic,code,Program.All,Instruction.writesNatMemory]

theorem program_exec {b K : ℕ} (params : Parameters) (input : Inputs)
    (s : State) (base n : ℕ) (prod acc : Coefficients b K)
    (hbase : s.natReg 30=base) (hM : s.natReg 31=(K+1)*2^K*6^b)
    (hn : s.natReg 35=n) (hone : s.natReg 36=1)
    (hprod : Represents (base+2*((K+1)*2^K*6^b)) prod s.realMem)
    (hacc : Represents (base+3*((K+1)*2^K*6^b)) acc s.realMem) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 60*((K+1)*2^K*6^b)+62 ∧
      Represents base (SKCoefficient.scale ((n+1:ℕ):ℝ)⁻¹ prod) t.realMem ∧
      Represents (base+3*((K+1)*2^K*6^b))
        (acc+SKCoefficient.scale ((n+1:ℕ):ℝ)⁻¹ prod) t.realMem ∧
      t.natReg 35=n+1 ∧
      (∀ address, (∀ i, i < (K+1)*2^K*6^b → address ≠ base+i ∧
        address ≠ base+3*((K+1)*2^K*6^b)+i) → t.realMem address=s.realMem address) := by
  let M := (K+1)*2^K*6^b
  let u := runCode params input scaleSetup s
  have hu : Exec params input (code scaleSetup) s 30 u := by
    simpa only [setup_costs.1] using exec_code params input scaleSetup s
  have um : u.realMem=s.realMem := by simp [u,scaleSetup,runCode,step]
  have un (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) : u.natReg r=s.natReg r := by
    apply hu.natReg_frame
    simp [scaleSetup,code,Program.All,Instruction.natDestination]
    omega
  have scalar : u.realReg 4=((n+1:ℕ):ℝ)⁻¹ := by
    simp [u,scaleSetup,runCode,step,hn,hone,one_div]
  obtain ⟨c₁,v,hv,bc₁,vprod,vi⟩ := coefficient_array .scale params input u
    (base+2*M) (base+2*M) base prod prod
    (by simp [u,scaleSetup,runCode,step,hbase,hM,M]; omega)
    (by simp [u,scaleSetup,runCode,step,hbase,hM,M]; omega)
    (by simp [u,scaleSetup,runCode,step,hbase])
    (by simp [u,scaleSetup,runCode,step,hone])
    (by simp [u,scaleSetup,runCode,step,hM])
    (by simpa only [um,M] using hprod) (by simpa only [um,M] using hprod)
    (by intro i j hi hj; dsimp [M]; omega)
  have vn (r : ℕ) (hr : 15 ≤ r) (h35 : r ≠ 35) : v.natReg r=s.natReg r :=
    ((array_frame .scale params input hv).1 r hr).trans (un r hr h35)
  have vacc : Represents (base+3*M) acc v.realMem := by
    intro x
    rw [preserved_outside .scale params input vi (base+3*M+encode x) (by
      intro i hi
      have hx := encode_lt x
      have hp : u.natReg 12=base := by simp [u,scaleSetup,runCode,step,hbase]
      have hl : u.natReg 14=M := by simp [u,scaleSetup,runCode,step,hM,M]
      rw [hp]; rw [hl] at hi; omega),um]
    exact hacc x
  let w := runCode params input sumSetup v
  have hw : Exec params input (code sumSetup) v 22 w := by
    simpa only [setup_costs.2] using exec_code params input sumSetup v
  have wm : w.realMem=v.realMem := by simp [w,sumSetup,runCode,step]
  have vp : Represents base (SKCoefficient.scale ((n+1:ℕ):ℝ)⁻¹ prod) v.realMem := by
    simpa [Represents,scalar,RestrictedArrays.Operation.eval,SKCoefficient.scale] using vprod
  obtain ⟨c₂,t,ht,bc₂,tsum,ti⟩ := coefficient_array .add params input w
    (base+3*M) base (base+3*M) acc (SKCoefficient.scale ((n+1:ℕ):ℝ)⁻¹ prod)
    (by simp [w,sumSetup,runCode,step,vn 30 (by omega) (by omega),vn 31 (by omega) (by omega),hbase,hM,M]; omega)
    (by simp [w,sumSetup,runCode,step,vn 30 (by omega) (by omega),hbase])
    (by simp [w,sumSetup,runCode,step,vn 30 (by omega) (by omega),vn 31 (by omega) (by omega),hbase,hM,M]; omega)
    (by simp [w,sumSetup,runCode,step,vn 36 (by omega) (by omega),hone])
    (by simp [w,sumSetup,runCode,step,vn 31 (by omega) (by omega),hM])
    (by rwa [wm]) (by rwa [wm]) (by intro i j hi hj; dsimp [M]; omega)
  have tp : Represents base (SKCoefficient.scale ((n+1:ℕ):ℝ)⁻¹ prod) t.realMem := by
    intro x
    rw [preserved_outside .add params input ti (base+encode x) (by
      intro i hi
      have hx := encode_lt x
      have hp : w.natReg 12=base+3*M := by
        simp [w,sumSetup,runCode,step,vn 30 (by omega) (by omega),vn 31 (by omega) (by omega),hbase,hM,M]; omega
      rw [hp]; dsimp [M] at *; omega),wm]
    exact vp x
  refine ⟨30+(c₁+(22+c₂)),t,Exec.seq hu (Exec.seq hv (Exec.seq hw ht)),by omega,
    tp,?_,?_,?_⟩
  · simpa [Represents,RestrictedArrays.Operation.eval,Pi.add_apply,M] using tsum
  · rw [(array_frame .add params input ht).1 35 (by omega)]
    have hw35 := hw.natReg_frame (r := 35) (by simp [sumSetup,code,Program.All,Instruction.natDestination])
    rw [hw35,(array_frame .scale params input hv).1 35 (by omega)]
    simp [u,scaleSetup,runCode,step,hn,hone]
  · intro address haddress
    have hdest1 : u.natReg 12=base := by simp [u,scaleSetup,runCode,step,hbase]
    have hlen1 : u.natReg 14=M := by simp [u,scaleSetup,runCode,step,hM,M]
    have hdest2 : w.natReg 12=base+3*M := by
      simp [w,sumSetup,runCode,step,vn 30 (by omega) (by omega),vn 31 (by omega) (by omega),hbase,hM,M]; omega
    have hlen2 : w.natReg 14=M := by simp [w,sumSetup,runCode,step,vn 31 (by omega) (by omega),hM,M]
    rw [preserved_outside .add params input ti address (by
      intro i hi; rw [hdest2]; exact (haddress i (by simpa only [hlen2,M] using hi)).2),wm]
    rw [preserved_outside .scale params input vi address (by
      intro i hi; rw [hdest1]; exact (haddress i (by simpa only [hlen1,M] using hi)).1),um]

end Manuscript.SKRestrictedScaleAdd
