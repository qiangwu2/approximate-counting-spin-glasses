import Manuscript.SKPrimitiveLoops

/-! The complete uniform primitive constructor: allocate its dense array by
an executed zero fill, scan all endpoint/color keys, then all cycle masks. -/
noncomputable section
namespace Manuscript.SKPrimitiveAssembly
open RestrictedMachine SKBasisEncoding SKPrimitiveScan SKPrimitiveLoops SKPrimitiveTerms
open SpinGlass SKCoefficient SKCountedExecution
open scoped BigOperators

def fillSetup : List Instruction :=
  [.ncopy 10 276,.ncopy 11 276,.ncopy 12 276,.nconst 13 1,
   .nadd 293 273 292,.nmul 293 293 274,.nmul 14 293 275,.rconst 4 0]
def initProgram : Program := .seq (code fillSetup) (RestrictedArrays.program .fill)
def program : Program := .seq initProgram
  (.seq (SKPrimitiveLoops.program true) (SKPrimitiveLoops.program false))

def operationBound (N b K : ℕ) : ℕ :=
  30*((K+1)*2^K*6^b)+(b*b)*2^K*(27*N+58*K+18*b+229)+
    2^K*(N*(27*N+18)+58*K+147)+55

theorem initialize_exec {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (hs : Data q branch outside f cache s) :
    ∃ count t, Exec p i initProgram s count t ∧ count≤30*((K+1)*2^K*6^b)+25 ∧
      Stable s t ∧ (∀ y : Basis b K,t.realMem (s.natReg 276+encode y)=0) := by
  let a := runCode p i fillSetup s
  have ha14 : a.natReg 14=(K+1)*2^K*6^b := by
    simp [a,fillSetup,runCode,step,hs.capacity,hs.one,hs.colors,hs.degrees]
  obtain ⟨c,t,he,bc,hv,hi⟩ := SKRestrictedArrays.fill_array p i a (s.natReg 276)
    (by simp [a,fillSetup,runCode,step]) (by simp [a,fillSetup,runCode,step])
    (by simp [a,fillSetup,runCode,step]) (by simp [a,fillSetup,runCode,step]) ha14
  have heall : Exec p i initProgram s (20+c) t := Exec.seq (exec_code p i fillSetup s) he
  refine ⟨_,t,heall,by omega,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro r hr
      have hrr : 15≤r ∧ r≠293 := by simp only [stableRegs,Finset.mem_insert,Finset.mem_singleton] at hr; omega
      rw [(SKRestrictedArrays.array_frame .fill p i he).1 r hrr.1]
      apply (exec_code p i fillSetup s).natReg_frame
      simp [fillSetup,code,Program.All,Instruction.natDestination]
      omega
    · simpa [a,fillSetup,runCode,step] using (SKRestrictedArrays.array_frame .fill p i he).2.2
    · intro address hlt
      have hh := SKRestrictedArrays.preserved_outside .fill p i hi address (by
        intro j hj
        have ha12 : a.natReg 12=s.natReg 276 := by simp [a,fillSetup,runCode,step]
        rw [ha12]; omega)
      simpa [a,fillSetup,runCode,step] using hh
  · intro y
    simpa [a,fillSetup,runCode,step] using hv y

theorem assembly_exec {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (f : Finset V → ℝ)
    (cache : Root (Fin N) b → Table (Fin N) K) (hs : Data q branch outside f cache s) :
    ∃ count t, Exec p i program s count t ∧ count≤operationBound N b K ∧
      Stable s t ∧
      (∀ y,t.realMem (s.natReg 276+encode y)=
        (SKChargedPrimitiveExecution.assemble
          (SKChargedPrimitiveExecution.primitiveInstruction q branch outside f cache)).value y) := by
  obtain ⟨c0,a,he0,bc0,hsa,ha⟩ := initialize_exec p i s q branch outside f cache hs
  obtain ⟨c1,d,he1,bc1,had,hd⟩ := SKPrimitiveLoops.program_exec true p i a q branch outside f cache 0
    (hs.stable hsa) (by intro y; rw [hsa.1 276 (by simp [stableRegs])]; exact ha y)
  let accumulated := cumulative (0 : Coefficients b K) (entry true q branch outside f cache) (limit true b K)
  obtain ⟨c2,t,he2,bc2,hdt,ht⟩ := SKPrimitiveLoops.program_exec false p i d q branch outside f cache accumulated
    ((hs.stable hsa).stable had) (by intro y; rw [had.1 276 (by simp [stableRegs])]; exact hd y)
  refine ⟨c0+(c1+c2),t,Exec.seq he0 (Exec.seq he1 he2),?_,hsa.trans (had.trans hdt),?_⟩
  · simp [limit,cost,Nat.add_assoc] at bc1 bc2
    dsimp [operationBound]
    simp only [Nat.add_assoc] at *
    omega
  · intro y
    have hh := ht y
    rw [had.1 276 (by simp [stableRegs]),hsa.1 276 (by simp [stableRegs])] at hh
    rw [hh]
    have heq := congrFun (SKPrimitiveTerms.total_eq q branch outside f cache) y
    rw [← pair_sum q branch outside f cache,← cycle_sum outside f cache] at heq
    simpa [accumulated,cumulative,entry,limit,Finset.sum_apply] using heq

/-- The saved-cache constructor is connected directly to the existing
charged primitive polynomial once the actual root-cache value is supplied. -/
theorem actual_primitives_exec {V : Type*} [DecidableEq V] {N b K : ℕ}
    (p : Parameters) (i : Inputs) (s : State) (q : Fin b → ℕ)
    (branch : Fin b → V) (outside : Fin N → V) (color : Fin N → Fin K) (f : Finset V → ℝ)
    (hs : Data q branch outside f (rootCache branch outside color f).value s) :
    ∃ count t, Exec p i program s count t ∧ count≤operationBound N b K ∧
      Stable s t ∧
      (∀ y,t.realMem (s.natReg 276+encode y)=
        (SKChargedExecution.primitives q branch outside color f).coeff y) := by
  obtain ⟨c,t,he,bc,hst,hv⟩ := assembly_exec p i s q branch outside f _ hs
  refine ⟨c,t,he,bc,hst,?_⟩
  intro y
  rw [hv]
  have hh := congrFun (SKChargedPrimitiveExecution.primitives_value q branch outside color f) y
  exact hh
end Manuscript.SKPrimitiveAssembly
