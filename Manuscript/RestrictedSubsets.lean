import Manuscript.RestrictedRecursiveMachine
import Manuscript.SupportIndices

/-! A uniform output-sensitive subset generator. The state carries n remaining
vertices, k required vertices, a partial bit mask, and the current binary
place value. The fixed one-procedure table branches only after integer tests;
leaves append the generated mask to RAM. No input-dependent syntax is built. -/
noncomputable section
namespace Manuscript.RestrictedSubsets
open RestrictedMachine
private theorem state_ext {s t : State}
    (hR : s.realReg=t.realReg) (hN : s.natReg=t.natReg)
    (hmR : s.realMem=t.realMem) (hmN : s.natMem=t.natMem) : s=t := by
  cases s; cases t; simp_all

/-- Masks are emitted in the same exclude/include order as `chooseExecution`. -/
def masks : ℕ → ℕ → ℕ → ℕ → List ℕ
  | _, 0, a, b => [a]
  | 0, _+1, _, _ => []
  | n+1, k+1, a, b =>
      if n < k then [] else masks n (k+1) a (2*b) ++ masks n k (a+b) (2*b)

def work : ℕ → ℕ → ℕ
  | _, 0 => 39
  | 0, _+1 => 39
  | n+1, k+1 => if n < k then 39 else 63+work n (k+1)+work n k

def firstCode : List Instruction := [.neq 208 201 205]
def secondCode : List Instruction := [.nle 208 201 200]
def leafCode : List Instruction := [.storeNat 204 202, .nadd 204 204 206]
def beforeCode : List Instruction := [.nsub 200 200 206, .nmul 203 203 207]
def betweenCode : List Instruction :=
  [.ndiv 203 203 207, .nadd 202 202 203, .nmul 203 203 207, .nsub 201 201 206]

def recursiveBody : RestrictedRecursiveMachine.Program 1 :=
  .seq (.base (code firstCode))
    (.branch 208 (.base (code leafCode))
      (.seq (.base (code secondCode))
        (.branch 208
          (.seq (.base (code beforeCode))
            (.seq (.call 0) (.seq (.base (code betweenCode)) (.call 0))))
          (.base .skip))))

def procedure : RestrictedRecursiveMachine.Procedure 1 :=
  ⟨recursiveBody, [], [200,201,202,203,208]⟩
def table : Fin 1 → RestrictedRecursiveMachine.Procedure 1 := fun _ => procedure

def writeList (memory : ℕ → ℕ) : ℕ → List ℕ → (ℕ → ℕ)
  | _, [] => memory
  | start, x::xs => writeList (Function.update memory start x) (start+1) xs

def output (s : State) (xs : List ℕ) : State :=
  { s with
    natReg := Function.update s.natReg 204 (s.natReg 204+xs.length)
    natMem := writeList s.natMem (s.natReg 204) xs }

@[simp] theorem writeList_nil (memory : ℕ → ℕ) (start : ℕ) :
    writeList memory start [] = memory := rfl

@[simp] theorem writeList_append (memory : ℕ → ℕ) (start : ℕ) (xs ys : List ℕ) :
    writeList memory start (xs++ys) = writeList (writeList memory start xs) (start+xs.length) ys := by
  induction xs generalizing memory start with
  | nil => simp [writeList]
  | cons x xs ih =>
      simp only [List.cons_append, writeList, ih, List.length_cons]
      congr 1 <;> omega

@[simp] theorem output_nil (s : State) : output s [] = s := by
  cases s
  simp [output, writeList, Function.update_eq_self]

@[simp] theorem output_natReg (s : State) (xs : List ℕ) (r : ℕ) :
    (output s xs).natReg r = if r=204 then s.natReg 204+xs.length else s.natReg r := by
  simp [output, Function.update_apply, eq_comm]
@[simp] theorem output_realReg (s : State) (xs : List ℕ) : (output s xs).realReg = s.realReg := rfl
@[simp] theorem output_realMem (s : State) (xs : List ℕ) : (output s xs).realMem = s.realMem := rfl
@[simp] theorem output_natMem (s : State) (xs : List ℕ) :
    (output s xs).natMem = writeList s.natMem (s.natReg 204) xs := rfl

@[simp] theorem output_append (s : State) (xs ys : List ℕ) :
    output (output s xs) ys = output s (xs++ys) := by
  apply state_ext
  · rfl
  · funext r
    by_cases hr : r=204 <;> simp [output_natReg, List.length_append, Nat.add_assoc, hr]
  · rfl
  · simp [writeList_append]

theorem output_writeNatReg (s : State) (xs : List ℕ) (r v : ℕ) (hr : r ≠ 204) :
    output (writeNatReg s r v) xs = writeNatReg (output s xs) r v := by
  apply state_ext
  · rfl
  · funext j
    by_cases h : j=r <;> by_cases h' : j=204 <;> simp [h,h',hr,Ne.symm hr] <;> omega
  · rfl
  · simp [hr, Ne.symm hr]

theorem runCode_before_output (params : Parameters) (input : Inputs) (s : State) (xs : List ℕ) :
    runCode params input betweenCode (output s xs) = output (runCode params input betweenCode s) xs := by
  simp [betweenCode, runCode, step, ← output_writeNatReg]

@[simp] theorem restore_output (s t : State) (xs : List ℕ) :
    RestrictedRecursiveMachine.restore procedure s (output t xs) = output (RestrictedRecursiveMachine.restore procedure s t) xs := by
  apply state_ext
  · funext r; simp [procedure]
  · funext r
    by_cases hr : r ∈ ([200,201,202,203,208] : List ℕ)
    · have h204 : r ≠ 204 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr; omega
      simp [procedure, hr, h204]
    · by_cases h204 : r=204 <;> simp [procedure, hr, h204]
  · simp
  · simp [procedure]

theorem generate_zero (params : Parameters) (input : Inputs) (s : State)
    (hk : s.natReg 201=0) (h0 : s.natReg 205=0) (h1 : s.natReg 206=1) :
    RestrictedRecursiveMachine.Exec table params input (.call 0) s 39
      (output s [s.natReg 202]) := by
  have hfirst := exec_code params input firstCode s
  let a := runCode params input firstCode s
  have ha : a.natReg 208 ≠ 0 := by simp [a,firstCode,runCode,step,hk,h0]
  have hleaf := exec_code params input leafCode a
  have he := RestrictedRecursiveMachine.Exec.call (table := table) 0
    (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hfirst) (RestrictedRecursiveMachine.Exec.branchNonzero ha (RestrictedRecursiveMachine.Exec.base hleaf)))
  convert he using 1
  · norm_num [table,procedure,firstCode,leafCode,codeCost,instrCost,RestrictedRecursiveMachine.callCost]
  · apply state_ext
    · funext r; simp [table,procedure,output,a,firstCode,leafCode,runCode,step,writeNatMem]
    · funext r
      simp [table,procedure,output,a,firstCode,leafCode,runCode,step,hk,h0,h1,
        RestrictedRecursiveMachine.restore,RestrictedRecursiveMachine.restoreReal,RestrictedRecursiveMachine.restoreNat,writeNatMem, Function.update_apply]
      split_ifs <;> simp_all
    · simp [table,procedure,output,a,firstCode,leafCode,runCode,step,writeNatMem]
    · simp [table,procedure,output,a,firstCode,leafCode,runCode,step,hk,h0,h1,
        RestrictedRecursiveMachine.restore,RestrictedRecursiveMachine.restoreReal,RestrictedRecursiveMachine.restoreNat,writeNatMem,writeList]

theorem generate_pruned (params : Parameters) (input : Inputs) (s : State)
    (hk : s.natReg 201≠0) (hlt : s.natReg 200<s.natReg 201) (h0 : s.natReg 205=0) :
    RestrictedRecursiveMachine.Exec table params input (.call 0) s 39 s := by
  have hfirst := exec_code params input firstCode s
  let a := runCode params input firstCode s
  have ha : a.natReg 208 = 0 := by simp [a,firstCode,runCode,step,hk,h0]
  have hsecond := exec_code params input secondCode a
  let b := runCode params input secondCode a
  have hb : b.natReg 208 = 0 := by simp [b,a,firstCode,secondCode,runCode,step,hlt]
  have he := RestrictedRecursiveMachine.Exec.call (table := table) 0
    (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hfirst) (RestrictedRecursiveMachine.Exec.branchZero ha
      (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hsecond) (RestrictedRecursiveMachine.Exec.branchZero hb
        (RestrictedRecursiveMachine.Exec.base (RestrictedMachine.Exec.skip b))))))
  convert he using 1
  · norm_num [table,procedure,firstCode,secondCode,codeCost,instrCost,RestrictedRecursiveMachine.callCost]
  · apply state_ext
    · funext r; simp [table,procedure,b,a,firstCode,secondCode,runCode,step]
    · funext r
      simp [table,procedure,b,a,firstCode,secondCode,runCode,step]
      split_ifs <;> simp_all
    · simp [table,procedure,b,a,firstCode,secondCode,runCode,step]
    · simp [table,procedure,b,a,firstCode,secondCode,runCode,step]

/-- The exact generator trace appends only retained masks, with no ambient
2^N enumeration and no freely supplied generated list. -/
theorem generate (params : Parameters) (input : Inputs) (n k : ℕ) :
    ∀ s : State, s.natReg 200=n → s.natReg 201=k →
      s.natReg 205=0 → s.natReg 206=1 → s.natReg 207=2 →
      RestrictedRecursiveMachine.Exec table params input (.call 0) s (work n k)
        (output s (masks n k (s.natReg 202) (s.natReg 203))) := by
  induction n generalizing k with
  | zero =>
      intro s hn hk h0 h1 h2
      cases k with
      | zero => simpa [work,masks] using generate_zero params input s hk h0 h1
      | succ k =>
          have hp := generate_pruned params input s (by omega) (by omega) h0
          simpa [work,masks] using hp
  | succ n ih =>
      intro s hn hk h0 h1 h2
      cases k with
      | zero => simpa [work,masks] using generate_zero params input s hk h0 h1
      | succ k =>
          by_cases hnk : n < k
          · have hp := generate_pruned params input s (by omega) (by omega) h0
            simpa [work,masks,hnk] using hp
          · let a := runCode params input firstCode s
            let b := runCode params input secondCode a
            let c := runCode params input beforeCode b
            let d := runCode params input betweenCode c
            let xs := masks n (k+1) (s.natReg 202) (2*s.natReg 203)
            let ys := masks n k (s.natReg 202+s.natReg 203) (2*s.natReg 203)
            have ha : a.natReg 208=0 := by simp [a,firstCode,runCode,step,hk,h0]
            have hb : b.natReg 208≠0 := by
              simp [b,a,secondCode,firstCode,runCode,step,hn,hk,show k≤n by omega]
            have hc0 : c.natReg 200=n := by simp [c,b,a,beforeCode,secondCode,firstCode,runCode,step,hn,h1]
            have hc1 : c.natReg 201=k+1 := by simp [c,b,a,beforeCode,secondCode,firstCode,runCode,step,hk]
            have hc2 : c.natReg 202=s.natReg 202 := by simp [c,b,a,beforeCode,secondCode,firstCode,runCode,step]
            have hc3 : c.natReg 203=2*s.natReg 203 := by simp [c,b,a,beforeCode,secondCode,firstCode,runCode,step,h2,Nat.mul_comm]
            have hc5 : c.natReg 205=0 := by simp [c,b,a,beforeCode,secondCode,firstCode,runCode,step,h0]
            have hc6 : c.natReg 206=1 := by simp [c,b,a,beforeCode,secondCode,firstCode,runCode,step,h1]
            have hc7 : c.natReg 207=2 := by simp [c,b,a,beforeCode,secondCode,firstCode,runCode,step,h2]
            have hex : RestrictedRecursiveMachine.Exec table params input (.call 0) c
                (work n (k+1)) (output c xs) := by
              simpa only [hc2,hc3,xs] using ih (k+1) c hc0 hc1 hc5 hc6 hc7
            have hd0 : d.natReg 200=n := by simp [d,betweenCode,runCode,step,hc0]
            have hd1 : d.natReg 201=k := by simp [d,betweenCode,runCode,step,hc1,hc6]
            have hd2 : d.natReg 202=s.natReg 202+s.natReg 203 := by
              simp [d,betweenCode,runCode,step,hc2,hc3,hc7]
            have hd3 : d.natReg 203=2*s.natReg 203 := by
              simp [d,betweenCode,runCode,step,hc3,hc7,Nat.mul_comm]
            have hd5 : d.natReg 205=0 := by simp [d,betweenCode,runCode,step,hc5]
            have hd6 : d.natReg 206=1 := by simp [d,betweenCode,runCode,step,hc6]
            have hd7 : d.natReg 207=2 := by simp [d,betweenCode,runCode,step,hc7]
            have hin : RestrictedRecursiveMachine.Exec table params input (.call 0) (output d xs)
                (work n k) (output (output d xs) ys) := by
              have hh := ih k (output d xs) (by simpa using hd0) (by simpa using hd1)
                (by simpa using hd5) (by simpa using hd6) (by simpa using hd7)
              simpa only [output_natReg,show (202:ℕ)≠204 by decide,
                show (203:ℕ)≠204 by decide,if_false,hd2,hd3,ys] using hh
            have hbetween : RestrictedMachine.Exec params input (code betweenCode) (output c xs)
                (codeCost betweenCode) (output d xs) := by
              simpa only [runCode_before_output,d] using exec_code params input betweenCode (output c xs)
            have he := RestrictedRecursiveMachine.Exec.call (table := table) 0
              (RestrictedRecursiveMachine.Exec.seq
                (RestrictedRecursiveMachine.Exec.base (exec_code params input firstCode s))
                (RestrictedRecursiveMachine.Exec.branchZero ha
                  (RestrictedRecursiveMachine.Exec.seq
                    (RestrictedRecursiveMachine.Exec.base (exec_code params input secondCode a))
                    (RestrictedRecursiveMachine.Exec.branchNonzero hb
                      (RestrictedRecursiveMachine.Exec.seq
                        (RestrictedRecursiveMachine.Exec.base (exec_code params input beforeCode b))
                        (RestrictedRecursiveMachine.Exec.seq hex
                          (RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hbetween) hin)))))))
            have hrestore : RestrictedRecursiveMachine.restore procedure s d = s := by
              apply state_ext
              · funext r; simp [procedure,d,c,b,a,betweenCode,beforeCode,secondCode,firstCode,runCode,step]
              · funext r
                simp [procedure,d,c,b,a,betweenCode,beforeCode,secondCode,firstCode,runCode,step]
                split_ifs <;> simp_all
              · simp [procedure,d,c,b,a,betweenCode,beforeCode,secondCode,firstCode,runCode,step]
              · simp [procedure,d,c,b,a,betweenCode,beforeCode,secondCode,firstCode,runCode,step]
            convert he using 1
            · simp only [work,if_neg hnk,table,procedure,RestrictedRecursiveMachine.callCost,
                List.length_cons,List.length_nil,firstCode,secondCode,beforeCode,betweenCode,
                codeCost,instrCost]
              omega
            · simp only [output_append,table,restore_output,hrestore,masks,if_neg hnk,xs,ys]


def binaryPlaces : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n+1, b => b :: binaryPlaces n (2*b)

@[simp] theorem binaryPlaces_length (n b : ℕ) : (binaryPlaces n b).length=n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [binaryPlaces,ih]

/-- The actual generated integers encode precisely the selected sublists;
this is the list-level bridge to the original verified subset enumeration. -/
theorem masks_as_choices (n k a b : ℕ) :
    masks n k a b =
      (SupportIndices.chooseLists k (binaryPlaces n b)).map (fun xs => a+xs.sum) := by
  induction n generalizing k a b with
  | zero => cases k <;> simp [masks,binaryPlaces,SupportIndices.chooseLists]
  | succ n ih =>
      cases k with
      | zero => simp [masks,binaryPlaces,SupportIndices.chooseLists]
      | succ k =>
          by_cases h : n<k
          · simp [masks,binaryPlaces,SupportIndices.chooseLists,h]
          · simp [masks,binaryPlaces,SupportIndices.chooseLists,h,ih,List.map_map,
              Function.comp_def,Nat.add_assoc]

@[simp] theorem masks_length (n k a b : ℕ) : (masks n k a b).length=n.choose k := by
  simp [masks_as_choices]

theorem work_le_nodes (n k : ℕ) : work n k ≤ 63*SupportIndices.chooseNodes n k := by
  induction n generalizing k with
  | zero => cases k <;> norm_num [work,SupportIndices.chooseNodes]
  | succ n ih =>
      cases k with
      | zero => norm_num [work,SupportIndices.chooseNodes]
      | succ k =>
          by_cases h : n<k
          · simp [work,SupportIndices.chooseNodes,h]
          · simp only [work,SupportIndices.chooseNodes,if_neg h]
            have h1 := ih k
            have h2 := ih (k+1)
            omega

theorem work_bound {n k : ℕ} (hk : k≤n) : work n k ≤ 63*(2*n+1)*n.choose k := by
  have h := Nat.mul_le_mul_left 63 (SupportIndices.chooseNodes_le hk)
  exact (work_le_nodes n k).trans (by simpa [Nat.mul_assoc] using h)

theorem writeList_below (memory : ℕ → ℕ) (xs : List ℕ) (start j : ℕ) (hj : j<start) :
    writeList memory start xs j = memory j := by
  induction xs generalizing memory start with
  | nil => rfl
  | cons x xs ih =>
      rw [writeList,ih _ (start+1) (by omega)]
      simp [Function.update_apply,show j≠start by omega]

theorem writeList_get (memory : ℕ → ℕ) (xs : List ℕ) (start i : ℕ) (hi : i<xs.length) :
    writeList memory start xs (start+i) = xs[i] := by
  induction xs generalizing memory start i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero =>
          simp only [Nat.add_zero,List.getElem_cons_zero,writeList]
          rw [writeList_below _ _ (start+1) start (by omega)]
          simp
      | succ i =>
          have hi' : i<xs.length := by simpa using hi
          have hh := ih (Function.update memory start x) (start+1) i hi'
          simpa [writeList,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

def initCode : List Instruction :=
  [.nconst 202 0, .nconst 203 1, .nconst 205 0, .nconst 206 1, .nconst 207 2]

def program : RestrictedRecursiveMachine.Program 1 :=
  .seq (.base (code initCode)) (.call 0)

/-- Uniformity: `table` and `program` are fixed independently of N,k and of
all raw inputs. The supplied runtime registers contain N,k and the output
base address; all masks and the complete output count are actually generated. -/
theorem program_realized (params : Parameters) (input : Inputs) (s : State)
    (hk : s.natReg 201 ≤ s.natReg 200) :
    ∃ count final,
      RestrictedRecursiveMachine.Exec table params input program s count final ∧
      count ≤ 63*(2*s.natReg 200+1)*(s.natReg 200).choose (s.natReg 201)+5 ∧
      final.natReg 204 = s.natReg 204+(s.natReg 200).choose (s.natReg 201) ∧
      (∀ (i : ℕ) (hi : i < (s.natReg 200).choose (s.natReg 201)),
        final.natMem (s.natReg 204+i) =
          (masks (s.natReg 200) (s.natReg 201) 0 1)[i]'(by simpa using hi)) := by
  let start := runCode params input initCode s
  have hh := generate params input (s.natReg 200) (s.natReg 201) start
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
    (by simp [start,initCode,runCode,step])
  have hstart : start.natReg 202=0 ∧ start.natReg 203=1 ∧ start.natReg 204=s.natReg 204 := by
    simp [start,initCode,runCode,step]
  let xs := masks (s.natReg 200) (s.natReg 201) 0 1
  refine ⟨5+work (s.natReg 200) (s.natReg 201),output start xs,?_,?_,?_,?_⟩
  · have hin := exec_code params input initCode s
    have he := RestrictedRecursiveMachine.Exec.seq (RestrictedRecursiveMachine.Exec.base hin) hh
    simpa [program,initCode,codeCost,instrCost,hstart.1,hstart.2.1,xs] using he
  · have hb := work_bound hk; omega
  · simp [xs,hstart.2.2]
  · intro i hi
    simpa [xs,hstart.2.2] using writeList_get start.natMem xs (start.natReg 204) i (by simpa [xs] using hi)

theorem program_exact (params : Parameters) (input : Inputs) (s : State) :
    RestrictedRecursiveMachine.Exec table params input program s
      (5+work (s.natReg 200) (s.natReg 201))
      (output (runCode params input initCode s) (masks (s.natReg 200) (s.natReg 201) 0 1)) := by
  let start := runCode params input initCode s
  have hh := generate params input (s.natReg 200) (s.natReg 201) start
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
    (by simp [start,initCode,runCode,step]) (by simp [start,initCode,runCode,step])
    (by simp [start,initCode,runCode,step])
  have he := RestrictedRecursiveMachine.Exec.seq
    (RestrictedRecursiveMachine.Exec.base (exec_code params input initCode s)) hh
  simpa [program,start,initCode,codeCost,instrCost,runCode,step] using he

end Manuscript.RestrictedSubsets
