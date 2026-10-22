import Manuscript.RestrictedFrames
import Manuscript.RestrictedCubes

/-! Fixed restricted-machine loops for local-spin terms on integer masks.
They scan exactly N binary places. Every digit extraction, conversion,
arithmetic operation, counter operation, and memory/register operation is
charged by the machine semantics. -/
noncomputable section
namespace Manuscript.RestrictedMaskArithmetic
open RestrictedMachine

def characterFactor (e u t : ℕ) : ℝ :=
  1+(e%2 : ℕ)*((u%2 : ℕ)*(1-2*(t%2 : ℕ))-1)

def character : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, _, _, _ => 1
  | n+1, e, u, t => characterFactor e u t * character n (e/2) (u/2) (t/2)

def fieldFactor (plus minus : ℝ) (u t : ℕ) : ℝ :=
  1+(u%2 : ℕ)*(plus+(t%2 : ℕ)*(minus-plus)-1)

def fieldProduct (plus minus : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | n+1, u, t => fieldFactor plus minus u t * fieldProduct plus minus n (u/2) (t/2)

def initCode : List Instruction :=
  [.nconst 254 2, .rconst 270 1, .rconst 271 (-1), .rconst 272 (-2), .rconst 265 1]

def characterBody : List Instruction :=
  [.nmod 260 251 254, .nmod 261 252 254, .nmod 262 253 254,
   .natToReal 260 260, .natToReal 261 261, .natToReal 262 262,
   .rmul 262 272 262, .radd 262 270 262,
   .rmul 261 261 262, .radd 261 261 271,
   .rmul 260 260 261, .radd 260 270 260, .rmul 265 265 260,
   .ndiv 251 251 254, .ndiv 252 252 254, .ndiv 253 253 254]

def fieldBody : List Instruction :=
  [.nmod 261 252 254, .nmod 262 253 254,
   .natToReal 261 261, .natToReal 262 262,
   .rmul 263 271 250, .radd 263 251 263,
   .rmul 262 262 263, .radd 262 250 262, .radd 262 262 271,
   .rmul 261 261 262, .radd 261 270 261, .rmul 265 265 261,
   .ndiv 252 252 254, .ndiv 253 253 254]

def characterProgram : Program := .seq (code initCode) (.repeat 250 (code characterBody))
def fieldProgram : Program := .seq (code initCode) (.repeat 250 (code fieldBody))

def Constants (s : State) : Prop :=
  s.natReg 254=2 ∧ s.realReg 270=1 ∧ s.realReg 271=-1 ∧ s.realReg 272=-2

@[simp] theorem characterBody_cost : codeCost characterBody=61 := by
  norm_num [characterBody,codeCost,instrCost]
@[simp] theorem fieldBody_cost : codeCost fieldBody=54 := by
  norm_num [fieldBody,codeCost,instrCost]
@[simp] theorem initCode_cost : codeCost initCode=5 := by
  norm_num [initCode,codeCost,instrCost]

theorem characterBody_invariant (params : Parameters) (input : Inputs) (s : State) (hs : Constants s) :
    let final := runCode params input characterBody s
    Constants final ∧ final.natReg 251=s.natReg 251/2 ∧
      final.natReg 252=s.natReg 252/2 ∧ final.natReg 253=s.natReg 253/2 ∧
      final.realReg 265=s.realReg 265*characterFactor (s.natReg 251) (s.natReg 252) (s.natReg 253) := by
  rcases hs with ⟨h2,h1,hn1,hn2⟩
  simp [Constants,characterBody,runCode,step,h2,h1,hn1,hn2,characterFactor]
  ring_nf
  simp

theorem fieldBody_invariant (params : Parameters) (input : Inputs) (s : State) (hs : Constants s) :
    let final := runCode params input fieldBody s
    Constants final ∧ final.natReg 252=s.natReg 252/2 ∧ final.natReg 253=s.natReg 253/2 ∧
      final.realReg 250=s.realReg 250 ∧ final.realReg 251=s.realReg 251 ∧
      final.realReg 265=s.realReg 265*fieldFactor (s.realReg 250) (s.realReg 251) (s.natReg 252) (s.natReg 253) := by
  rcases hs with ⟨h2,h1,hn1,hn2⟩
  simp [Constants,fieldBody,runCode,step,h2,h1,hn1,hn2,fieldFactor]
  ring_nf
  simp

theorem character_repeats (params : Parameters) (input : Inputs) (n : ℕ) :
    ∀ s : State, Constants s → ∃ final,
      Repeats params input (code characterBody) n s (66*n+3) final ∧
      final.realReg 265=s.realReg 265*character n (s.natReg 251) (s.natReg 252) (s.natReg 253) := by
  induction n with
  | zero =>
      intro s hs
      refine ⟨s, ?_, ?_⟩
      · simpa using Repeats.zero (params := params) (input := input) (code characterBody) s
      · simp [character]
  | succ n ih =>
      intro s hs
      let mid := runCode params input characterBody s
      obtain ⟨hm,h251,h252,h253,hvalue⟩ := characterBody_invariant params input s hs
      obtain ⟨final, he, hf⟩ := ih mid hm
      refine ⟨final, ?_, ?_⟩
      · have hb : Exec params input (code characterBody) s 61 mid := by
          simpa [mid] using exec_code params input characterBody s
        convert Repeats.succ hb he using 1 <;> omega
      · rw [hf,hvalue,h251,h252,h253,character]
        ring

theorem field_repeats (params : Parameters) (input : Inputs) (n : ℕ) :
    ∀ s : State, Constants s → ∃ final,
      Repeats params input (code fieldBody) n s (59*n+3) final ∧
      final.realReg 265=s.realReg 265*fieldProduct (s.realReg 250) (s.realReg 251)
        n (s.natReg 252) (s.natReg 253) := by
  induction n with
  | zero =>
      intro s hs
      refine ⟨s, ?_, ?_⟩
      · simpa using Repeats.zero (params := params) (input := input) (code fieldBody) s
      · simp [fieldProduct]
  | succ n ih =>
      intro s hs
      let mid := runCode params input fieldBody s
      obtain ⟨hm,h252,h253,h250,h251,hvalue⟩ := fieldBody_invariant params input s hs
      obtain ⟨final, he, hf⟩ := ih mid hm
      refine ⟨final, ?_, ?_⟩
      · have hb : Exec params input (code fieldBody) s 54 mid := by
          simpa [mid] using exec_code params input fieldBody s
        convert Repeats.succ hb he using 1 <;> omega
      · rw [hf,hvalue,h250,h251,h252,h253,fieldProduct]
        ring

theorem character_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input characterProgram s (66*s.natReg 250+10) final ∧
      final.realReg 265=character (s.natReg 250) (s.natReg 251) (s.natReg 252) (s.natReg 253) := by
  let start := runCode params input initCode s
  have hc : Constants start := by simp [start,Constants,initCode,runCode,step]
  obtain ⟨final, he, hf⟩ := character_repeats params input (s.natReg 250) start hc
  have hh : start.natReg 250=s.natReg 250 := by simp [start,initCode,runCode,step]
  have he' : Repeats params input (code characterBody) (start.natReg 250) start
      (66*s.natReg 250+3) final := by simpa [hh] using he
  refine ⟨final, ?_, ?_⟩
  · have hi := exec_code params input initCode s
    have hl := Exec.repeat he'
    have hx := Exec.seq hi hl
    convert hx using 1
    · rfl
    · simp only [initCode_cost]; omega
  · simpa [start,initCode,runCode,step] using hf

theorem field_realized (params : Parameters) (input : Inputs) (s : State) :
    ∃ final, Exec params input fieldProgram s (59*s.natReg 250+10) final ∧
      final.realReg 265=fieldProduct (s.realReg 250) (s.realReg 251)
        (s.natReg 250) (s.natReg 252) (s.natReg 253) := by
  let start := runCode params input initCode s
  have hc : Constants start := by simp [start,Constants,initCode,runCode,step]
  obtain ⟨final, he, hf⟩ := field_repeats params input (s.natReg 250) start hc
  have hh : start.natReg 250=s.natReg 250 := by simp [start,initCode,runCode,step]
  have he' : Repeats params input (code fieldBody) (start.natReg 250) start
      (59*s.natReg 250+3) final := by simpa [hh] using he
  refine ⟨final, ?_, ?_⟩
  · have hi := exec_code params input initCode s
    have hl := Exec.repeat he'
    have hx := Exec.seq hi hl
    convert hx using 1
    · rfl
    · simp only [initCode_cost]; omega
  · simpa [start,initCode,runCode,step] using hf

end Manuscript.RestrictedMaskArithmetic
