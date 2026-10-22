import Manuscript.SKBasisEncoding
import Manuscript.RestrictedFrames
import Manuscript.SKChargedPrimitiveExecution

/-! Executed sparse coefficient insertion. The mixed-radix address is
computed by primitive natural arithmetic and the old coefficient is read. -/
noncomputable section
namespace Manuscript.SKPrimitiveInsert
open RestrictedMachine SKBasisEncoding
open SpinGlass.SKCoefficient (Basis Coefficients)

def checkCode : List Instruction := [.nle 278 270 273,.nmul 279 277 278]
def updateCode : List Instruction :=
  [.nmul 280 270 274,.nadd 280 280 271,.nmul 280 280 275,
   .nadd 280 280 272,.nadd 280 280 276,.loadReal 1 280,.radd 1 1 0,.storeReal 280 1]
def program : Program := .seq (code checkCode) (.branch 279 (code updateCode) .skip)

def address (s : State) : ℕ := s.natReg 276+
  (s.natReg 270*s.natReg 274+s.natReg 271)*s.natReg 275+s.natReg 272

theorem insert_realized (p : Parameters) (i : Inputs) (s : State) :
    ∃ c t, Exec p i program s c t ∧ c≤43 ∧
      t.realMem=(if s.natReg 277≠0 ∧ s.natReg 270≤s.natReg 273 then
        Function.update s.realMem (address s) (s.realMem (address s)+s.realReg 0) else s.realMem) ∧
      t.natMem=s.natMem := by
  let a := runCode p i checkCode s
  by_cases h : s.natReg 277≠0 ∧ s.natReg 270≤s.natReg 273
  · have hf : a.natReg 279≠0 := by simp [a,checkCode,runCode,step,h.1,h.2]
    let t := runCode p i updateCode a
    refine ⟨8+(30+3),t,Exec.seq (exec_code p i checkCode s)
      (Exec.branchNonzero hf (exec_code p i updateCode a)),by decide,?_,?_⟩
    · simp [t,a,checkCode,updateCode,runCode,step,writeRealMem,address,h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [t,a,checkCode,updateCode,runCode,step,writeRealMem]
  · have hf : a.natReg 279=0 := by
      by_cases hz : s.natReg 277=0
      · simp [a,checkCode,runCode,step,hz]
      · have hk : ¬s.natReg 270≤s.natReg 273 := fun hh => h ⟨hz,hh⟩
        simp [a,checkCode,runCode,step,hk]
    refine ⟨8+3,a,Exec.seq (exec_code p i checkCode s) (Exec.branchZero hf (Exec.skip a)),by decide,?_,?_⟩
    · simp [a,checkCode,runCode,step,h]
    · simp [a,checkCode,runCode,step,writeRealMem]

theorem insert_basis_realized {b K : ℕ} (p : Parameters) (i : Inputs) (s : State)
    (f : Coefficients b K) (x : Basis b K) (base : ℕ)
    (hcharge : s.natReg 270=x.1.val) (hmask : s.natReg 271=(maskEquiv K x.2.1).val)
    (hdegree : s.natReg 272=(degreeEquiv b x.2.2).val)
    (hK : s.natReg 273=K) (hp : s.natReg 274=2^K) (hq : s.natReg 275=6^b)
    (hbase : s.natReg 276=base) (hvalid : s.natReg 277≠0)
    (hm : ∀ y,s.realMem (base+encode y)=f y) :
    ∃ c t, Exec p i program s c t ∧ c≤43 ∧
      (∀ y,t.realMem (base+encode y)=
        (Function.update f x (f x+s.realReg 0)) y) ∧
      (∀ a,(∀ y : Basis b K,a≠base+encode y) → t.realMem a=s.realMem a) ∧ t.natMem=s.natMem := by
  obtain ⟨c,t,he,bc,hv,hn⟩ := insert_realized p i s
  have hk : s.natReg 270≤s.natReg 273 := by rw [hcharge,hK]; exact Nat.le_of_lt_succ x.1.isLt
  have ha : address s=base+encode x := by
    rw [address,hbase,hcharge,hp,hmask,hq,hdegree,encode_formula]; omega
  rw [if_pos ⟨hvalid,hk⟩,ha,hm x] at hv
  refine ⟨c,t,he,bc,?_,?_,hn⟩
  · intro y
    by_cases hy : y=x
    · subst y; simp [hv]
    · have hi : base+encode y≠base+encode x := fun h => hy (encode_injective b K (Nat.add_left_cancel h))
      have hx : encode y≠encode x := fun h => hy (encode_injective b K h)
      simp [hv,Function.update,hx,hy,hm]
  · intro a h
    simp [hv,Function.update,h x]
end Manuscript.SKPrimitiveInsert
