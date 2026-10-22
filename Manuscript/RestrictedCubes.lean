import Manuscript.RestrictedSubsets

/-! A fixed recursive procedure emits all spin masks on the selected support.
The recursion examines N bits and branches twice only at a selected vertex;
unselected vertices have one child. Consequently its count depends on the
local cube size, not the ambient cube size. -/
noncomputable section
namespace Manuscript.RestrictedCubes
open RestrictedMachine
open RestrictedSubsets (writeList output)

private theorem state_ext {s t : State}
    (hR : s.realReg=t.realReg) (hN : s.natReg=t.natReg)
    (hmR : s.realMem=t.realMem) (hmN : s.natMem=t.natMem) : s=t := by
  cases s; cases t; simp_all

def masks : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, a, _ => [a]
  | n+1, u, a, b =>
      if u%2=0 then masks n (u/2) a (2*b)
      else masks n (u/2) a (2*b) ++ masks n (u/2) (a+b) (2*b)

def supportSize : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, u => supportSize n (u/2) + if u%2=0 then 0 else 1

def work : ℕ → ℕ → ℕ
  | 0, _ => 43
  | n+1, u => if u%2=0 then 55+work n (u/2) else 67+2*work n (u/2)

def firstCode : List Instruction := [.neq 228 220 205]
def leafCode : List Instruction := [.storeNat 204 222, .nadd 204 204 206]
def beforeCode : List Instruction :=
  [.nmod 229 221 207, .ndiv 221 221 207, .nsub 220 220 206, .nmul 223 223 207]
def betweenCode : List Instruction :=
  [.ndiv 223 223 207, .nadd 222 222 223, .nmul 223 223 207]

def recursiveBody : RestrictedRecursiveMachine.Program 1 :=
  .seq (.base (code firstCode))
    (.branch 228 (.base (code leafCode))
      (.seq (.base (code beforeCode))
        (.seq (.call 0)
          (.branch 229 (.seq (.base (code betweenCode)) (.call 0)) (.base .skip)))))

def procedure : RestrictedRecursiveMachine.Procedure 1 :=
  ⟨recursiveBody, [], [220,221,222,223,228,229]⟩
def table : Fin 1 → RestrictedRecursiveMachine.Procedure 1 := fun _ => procedure

@[simp] theorem restore_output (s t : State) (xs : List ℕ) :
    RestrictedRecursiveMachine.restore procedure s (output t xs) =
      output (RestrictedRecursiveMachine.restore procedure s t) xs := by
  apply state_ext
  · funext r; simp [procedure]
  · funext r
    by_cases hr : r ∈ ([220,221,222,223,228,229] : List ℕ)
    · have h204 : r ≠ 204 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; omega
      simp [procedure, hr, h204]
    · by_cases h204 : r=204 <;> simp [procedure, hr, h204]
  · simp
  · simp [procedure]

theorem runCode_between_output (params : Parameters) (input : Inputs) (s : State) (xs : List ℕ) :
    runCode params input betweenCode (output s xs) = output (runCode params input betweenCode s) xs := by
  simp [betweenCode,runCode,step,← RestrictedSubsets.output_writeNatReg]

/-- Exact operational refinement of the local-cube recursion. -/
theorem generate (params : Parameters) (input : Inputs) (n : ℕ) :
    ∀ s : State, s.natReg 220=n →
      s.natReg 205=0 → s.natReg 206=1 → s.natReg 207=2 →
      RestrictedRecursiveMachine.Exec table params input (.call 0) s (work n (s.natReg 221))
        (output s (masks n (s.natReg 221) (s.natReg 222) (s.natReg 223))) := by
  induction n with
  | zero =>
      intro s hn h0 h1 h2
      let a := runCode params input firstCode s
      have ha : a.natReg 228≠0 := by simp [a,firstCode,runCode,step,hn,h0]
      have he := RestrictedRecursiveMachine.Exec.call (table := table) 0
        (RestrictedRecursiveMachine.Exec.seq
          (RestrictedRecursiveMachine.Exec.base (exec_code params input firstCode s))
          (RestrictedRecursiveMachine.Exec.branchNonzero ha
            (RestrictedRecursiveMachine.Exec.base (exec_code params input leafCode a))))
      convert he using 1
      · norm_num [work,table,procedure,RestrictedRecursiveMachine.callCost,firstCode,leafCode,codeCost,instrCost]
      · apply state_ext
        · funext r; simp [table,procedure,output,a,firstCode,leafCode,runCode,step,writeNatMem]
        · funext r
          simp [table,procedure,output,a,firstCode,leafCode,runCode,step,masks,hn,h0,h1,
            RestrictedRecursiveMachine.restore,RestrictedRecursiveMachine.restoreReal,
            RestrictedRecursiveMachine.restoreNat,writeNatMem,Function.update_apply]
          split_ifs <;> simp_all
        · simp [table,procedure,output,a,firstCode,leafCode,runCode,step,writeNatMem]
        · simp [table,procedure,output,a,firstCode,leafCode,runCode,step,masks,hn,h0,h1,
            RestrictedRecursiveMachine.restore,RestrictedRecursiveMachine.restoreReal,
            RestrictedRecursiveMachine.restoreNat,writeNatMem,writeList]
  | succ n ih =>
      intro s hn h0 h1 h2
      let a := runCode params input firstCode s
      let b := runCode params input beforeCode a
      let c := runCode params input betweenCode b
      let xs := masks n (s.natReg 221/2) (s.natReg 222) (2*s.natReg 223)
      let ys := masks n (s.natReg 221/2) (s.natReg 222+s.natReg 223) (2*s.natReg 223)
      have ha : a.natReg 228=0 := by simp [a,firstCode,runCode,step,hn,h0]
      have hb0 : b.natReg 220=n := by simp [b,a,beforeCode,firstCode,runCode,step,hn,h1]
      have hb1 : b.natReg 221=s.natReg 221/2 := by simp [b,a,beforeCode,firstCode,runCode,step,h2]
      have hb2 : b.natReg 222=s.natReg 222 := by simp [b,a,beforeCode,firstCode,runCode,step]
      have hb3 : b.natReg 223=2*s.natReg 223 := by simp [b,a,beforeCode,firstCode,runCode,step,h2,Nat.mul_comm]
      have hb5 : b.natReg 205=0 := by simp [b,a,beforeCode,firstCode,runCode,step,h0]
      have hb6 : b.natReg 206=1 := by simp [b,a,beforeCode,firstCode,runCode,step,h1]
      have hb7 : b.natReg 207=2 := by simp [b,a,beforeCode,firstCode,runCode,step,h2]
      have hb9 : b.natReg 229=s.natReg 221%2 := by simp [b,a,beforeCode,firstCode,runCode,step,h2]
      have hex : RestrictedRecursiveMachine.Exec table params input (.call 0) b
          (work n (s.natReg 221/2)) (output b xs) := by
        simpa only [hb1,hb2,hb3,xs] using ih b hb0 hb5 hb6 hb7
      have restore_b : RestrictedRecursiveMachine.restore procedure s b=s := by
        apply state_ext
        · funext r; simp [procedure,b,a,beforeCode,firstCode,runCode,step]
        · funext r; simp [procedure,b,a,beforeCode,firstCode,runCode,step]; split_ifs <;> simp_all
        · simp [procedure,b,a,beforeCode,firstCode,runCode,step]
        · simp [procedure,b,a,beforeCode,firstCode,runCode,step]
      by_cases hbit : s.natReg 221%2=0
      · have hf : (output b xs).natReg 229=0 := by simp [hb9,hbit]
        have he := RestrictedRecursiveMachine.Exec.call (table := table) 0
          (RestrictedRecursiveMachine.Exec.seq
            (RestrictedRecursiveMachine.Exec.base (exec_code params input firstCode s))
            (RestrictedRecursiveMachine.Exec.branchZero ha
              (RestrictedRecursiveMachine.Exec.seq
                (RestrictedRecursiveMachine.Exec.base (exec_code params input beforeCode a))
                (RestrictedRecursiveMachine.Exec.seq hex
                  (RestrictedRecursiveMachine.Exec.branchZero hf
                    (RestrictedRecursiveMachine.Exec.base (RestrictedMachine.Exec.skip (output b xs))))))))
        convert he using 1
        · simp only [work,if_pos hbit,table,procedure,RestrictedRecursiveMachine.callCost,
            firstCode,beforeCode,codeCost,instrCost,List.length_cons,List.length_nil]
          omega
        · simp only [table,restore_output,restore_b,masks,if_pos hbit,xs]
      · have hf : (output b xs).natReg 229≠0 := by simp [hb9,hbit]
        have hc0 : c.natReg 220=n := by simp [c,betweenCode,runCode,step,hb0]
        have hc1 : c.natReg 221=s.natReg 221/2 := by simp [c,betweenCode,runCode,step,hb1]
        have hc2 : c.natReg 222=s.natReg 222+s.natReg 223 := by simp [c,betweenCode,runCode,step,hb2,hb3,hb7]
        have hc3 : c.natReg 223=2*s.natReg 223 := by simp [c,betweenCode,runCode,step,hb3,hb7,Nat.mul_comm]
        have hc5 : c.natReg 205=0 := by simp [c,betweenCode,runCode,step,hb5]
        have hc6 : c.natReg 206=1 := by simp [c,betweenCode,runCode,step,hb6]
        have hc7 : c.natReg 207=2 := by simp [c,betweenCode,runCode,step,hb7]
        have hin : RestrictedRecursiveMachine.Exec table params input (.call 0) (output c xs)
            (work n (s.natReg 221/2)) (output (output c xs) ys) := by
          have hh := ih (output c xs) (by simpa using hc0) (by simpa using hc5)
            (by simpa using hc6) (by simpa using hc7)
          simpa only [RestrictedSubsets.output_natReg,show (221:ℕ)≠204 by decide,
            show (222:ℕ)≠204 by decide,show (223:ℕ)≠204 by decide,if_false,hc1,hc2,hc3,ys] using hh
        have hbetween : RestrictedMachine.Exec params input (code betweenCode) (output b xs)
            (codeCost betweenCode) (output c xs) := by
          simpa only [runCode_between_output,c] using exec_code params input betweenCode (output b xs)
        have he := RestrictedRecursiveMachine.Exec.call (table := table) 0
          (RestrictedRecursiveMachine.Exec.seq
            (RestrictedRecursiveMachine.Exec.base (exec_code params input firstCode s))
            (RestrictedRecursiveMachine.Exec.branchZero ha
              (RestrictedRecursiveMachine.Exec.seq
                (RestrictedRecursiveMachine.Exec.base (exec_code params input beforeCode a))
                (RestrictedRecursiveMachine.Exec.seq hex
                  (RestrictedRecursiveMachine.Exec.branchNonzero hf
                    (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hbetween) hin))))))
        have restore_c : RestrictedRecursiveMachine.restore procedure s c=s := by
          apply state_ext
          · funext r; simp [procedure,c,b,a,betweenCode,beforeCode,firstCode,runCode,step]
          · funext r; simp [procedure,c,b,a,betweenCode,beforeCode,firstCode,runCode,step]; split_ifs <;> simp_all
          · simp [procedure,c,b,a,betweenCode,beforeCode,firstCode,runCode,step]
          · simp [procedure,c,b,a,betweenCode,beforeCode,firstCode,runCode,step]
        convert he using 1
        · simp only [work,if_neg hbit,table,procedure,RestrictedRecursiveMachine.callCost,
            firstCode,beforeCode,betweenCode,codeCost,instrCost,List.length_cons,List.length_nil]
          omega
        · simp only [RestrictedSubsets.output_append,table,restore_output,restore_c,masks,if_neg hbit,xs,ys]

def selectedPlaces : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | n+1, u, b => if u%2=0 then selectedPlaces n (u/2) (2*b)
      else b :: selectedPlaces n (u/2) (2*b)

@[simp] theorem selectedPlaces_length (n u b : ℕ) :
    (selectedPlaces n u b).length = supportSize n u := by
  induction n generalizing u b with
  | zero => rfl
  | succ n ih => by_cases h : u%2=0 <;> simp [selectedPlaces,supportSize,h,ih]

theorem masks_as_subsets (n u a b : ℕ) :
    masks n u a b = (SupportIndices.allExecution (selectedPlaces n u b)).values.map (fun xs => a+xs.sum) := by
  induction n generalizing u a b with
  | zero => simp [masks,selectedPlaces,SupportIndices.allExecution]
  | succ n ih =>
      by_cases h : u%2=0
      · simp [masks,selectedPlaces,h,ih]
      · simp [masks,selectedPlaces,h,ih,SupportIndices.allExecution,List.map_map,
          Function.comp_def,Nat.add_assoc]

@[simp] theorem masks_length (n u a b : ℕ) :
    (masks n u a b).length=2^supportSize n u := by
  simp [masks_as_subsets]

theorem work_bound (n u : ℕ) : work n u ≤ 67*(2*n+1)*2^supportSize n u := by
  induction n generalizing u with
  | zero => norm_num [work,supportSize]
  | succ n ih =>
      have hh := ih (u/2)
      have hp : 1≤2^supportSize n (u/2) := Nat.one_le_pow _ _ (by omega)
      by_cases h : u%2=0
      · simp only [work,supportSize,if_pos h,Nat.add_zero]
        nlinarith
      · simp only [work,supportSize,if_neg h,pow_succ]
        nlinarith

def initCode : List Instruction :=
  [.nconst 222 0, .nconst 223 1, .nconst 205 0, .nconst 206 1, .nconst 207 2]
def program : RestrictedRecursiveMachine.Program 1 :=
  .seq (.base (code initCode)) (.call 0)

/-- A single fixed program generates every local-spin mask and its output
count. It branches only on selected support bits. -/
theorem program_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ count final,
      RestrictedRecursiveMachine.Exec table params input program s count final ∧
      count ≤ 67*(2*s.natReg 220+1)*2^supportSize (s.natReg 220) (s.natReg 221)+5 ∧
      final.natReg 204=s.natReg 204+2^supportSize (s.natReg 220) (s.natReg 221) ∧
      (∀ (i : ℕ) (hi : i<2^supportSize (s.natReg 220) (s.natReg 221)),
        final.natMem (s.natReg 204+i)=
          (masks (s.natReg 220) (s.natReg 221) 0 1)[i]'(by simpa using hi)) := by
  let start := runCode params input initCode s
  have hh := generate params input (s.natReg 220) start
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
  have hstart : start.natReg 221=s.natReg 221 ∧ start.natReg 222=0 ∧ start.natReg 223=1 ∧
      start.natReg 204=s.natReg 204 := by simp [start,initCode,runCode,step]
  let xs := masks (s.natReg 220) (s.natReg 221) 0 1
  refine ⟨5+work (s.natReg 220) (s.natReg 221),output start xs,?_,?_,?_,?_⟩
  · have he := RestrictedRecursiveMachine.Exec.seq
      (RestrictedRecursiveMachine.Exec.base (exec_code params input initCode s)) hh
    simpa [program,initCode,codeCost,instrCost,hstart.1,hstart.2.1,hstart.2.2.1,xs] using he
  · have hb := work_bound (s.natReg 220) (s.natReg 221); omega
  · simp [xs,hstart.2.2.2]
  · intro i hi
    simpa [xs,hstart.2.2.2] using RestrictedSubsets.writeList_get start.natMem xs
      (start.natReg 204) i (by simpa [xs] using hi)

theorem program_exact (params : Parameters) (input : Inputs) (s : State) :
    RestrictedRecursiveMachine.Exec table params input program s
      (5+work (s.natReg 220) (s.natReg 221))
      (output (runCode params input initCode s) (masks (s.natReg 220) (s.natReg 221) 0 1)) := by
  let start := runCode params input initCode s
  have hh := generate params input (s.natReg 220) start
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
  have he := RestrictedRecursiveMachine.Exec.seq
    (RestrictedRecursiveMachine.Exec.base (exec_code params input initCode s)) hh
  simpa [program,start,initCode,codeCost,instrCost,runCode,step] using he

end Manuscript.RestrictedCubes
