import Manuscript.SKRestrictedScatter

/-! The addressed scatter program computes the actual SK coefficient
convolution.  The only stage assumptions describe RAM layout and generated
natural metadata; there is no assumed arithmetic result or scalar oracle. -/
noncomputable section
namespace Manuscript.SKRestrictedAlgebra
open RestrictedMachine SKRestrictedScatter
open SpinGlass SKCoefficient

structure Layout (b K : ℕ) where
  left : Basis b K → ℕ
  right : Basis b K → ℕ
  out : Basis b K → ℕ
  out_injective : Function.Injective out
  left_ne_out : ∀ x z, left x ≠ out z
  right_ne_out : ∀ y z, right y ≠ out z

def Represents {b K : ℕ} (layout : Layout b K)
    (f g acc : Coefficients b K) (memory : ℕ → ℝ) : Prop :=
  (∀ x, memory (layout.left x) = f x) ∧
  (∀ y, memory (layout.right y) = g y) ∧
  (∀ z, memory (layout.out z) = acc z)

def RecordMatches {b K : ℕ} (layout : Layout b K)
    (metadata : ℕ → ℕ) (p : ℕ) (pair : Basis b K × Basis b K) : Prop :=
  match basisMul pair.1 pair.2 with
  | none => metadata p = 0
  | some z => metadata p ≠ 0 ∧ metadata (p+1) = layout.left pair.1 ∧
      metadata (p+2) = layout.right pair.2 ∧ metadata (p+3) = layout.out z

def ScheduleMatches {b K : ℕ} (layout : Layout b K) (metadata : ℕ → ℕ) :
    ℕ → List (Basis b K × Basis b K) → Prop
  | _, [] => True
  | p, pair :: pairs => RecordMatches layout metadata p pair ∧
      ScheduleMatches layout metadata (p+4) pairs

theorem memoryStep_represents {b K : ℕ} (layout : Layout b K)
    (f g acc : Coefficients b K) (memory : ℕ → ℝ) (metadata : ℕ → ℕ)
    (p : ℕ) (pair : Basis b K × Basis b K)
    (hr : Represents layout f g acc memory)
    (hm : RecordMatches layout metadata p pair) :
    Represents layout f g (SKDenseExecution.pushStep f g pair acc)
      (memoryStep metadata p memory) := by
  rcases hr with ⟨hf, hg, ha⟩
  cases he : basisMul pair.1 pair.2 with
  | none =>
    have hz : metadata p = 0 := by simpa [RecordMatches, he] using hm
    simpa only [Represents, memoryStep, hz, if_true, SKDenseExecution.pushStep, he] using And.intro hf (And.intro hg ha)
  | some z =>
    obtain ⟨hn, hl, hright, ho⟩ : metadata p ≠ 0 ∧
        metadata (p+1) = layout.left pair.1 ∧ metadata (p+2) = layout.right pair.2 ∧
        metadata (p+3) = layout.out z := by simpa [RecordMatches, he] using hm
    simp only [Represents, memoryStep, hn, if_false, hl, hright, ho,
      SKDenseExecution.pushStep, he, hf, hg, ha]
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [Function.update_of_ne (layout.left_ne_out x z), hf]
    · intro y
      rw [Function.update_of_ne (layout.right_ne_out y z), hg]
    · intro q
      by_cases hq : q = z
      · subst q; simp
      · have hqz : layout.out q ≠ layout.out z := fun h => hq (layout.out_injective h)
        rw [Function.update_of_ne hqz, Function.update_of_ne hq, ha]

def memoryRun (metadata : ℕ → ℕ) : ℕ → ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | _, 0, memory => memory
  | p, n+1, memory => memoryRun metadata (p+4) n (memoryStep metadata p memory)

theorem memoryLoop_first (metadata : ℕ → ℕ) (p n : ℕ) (memory : ℕ → ℝ) :
    memoryLoop metadata p (n+1) memory =
      memoryLoop metadata (p+4) n (memoryStep metadata p memory) := by
  induction n with
  | zero => simp [memoryLoop]
  | succ n ih =>
    simp only [memoryLoop] at ih ⊢
    rw [ih]
    congr 1
    omega

theorem memoryRun_eq_loop (metadata : ℕ → ℕ) (p n : ℕ) (memory : ℕ → ℝ) :
    memoryRun metadata p n memory = memoryLoop metadata p n memory := by
  induction n generalizing p memory with
  | zero => rfl
  | succ n ih => rw [memoryRun, ih, memoryLoop_first]

theorem schedule_represents {b K : ℕ} (layout : Layout b K)
    (f g : Coefficients b K) (metadata : ℕ → ℕ)
    (pairs : List (Basis b K × Basis b K)) (p : ℕ)
    (acc : Coefficients b K) (memory : ℕ → ℝ)
    (hr : Represents layout f g acc memory)
    (hm : ScheduleMatches layout metadata p pairs) :
    Represents layout f g (SKDenseExecution.pushLoop f g pairs acc)
      (memoryLoop metadata p pairs.length memory) := by
  rw [← memoryRun_eq_loop]
  induction pairs generalizing p acc memory with
  | nil => exact hr
  | cons pair pairs ih =>
    obtain ⟨hfirst, hrest⟩ := hm
    exact ih (p+4) (SKDenseExecution.pushStep f g pair acc)
      (memoryStep metadata p memory)
      (memoryStep_represents layout f g acc memory metadata p pair hr hfirst) hrest

/-- End-to-end arithmetic stage: the fixed runtime scatter loop consumes the
generated pair records, and its output RAM is the actual coefficient product. -/
theorem multiplication_realized {b K : ℕ} (params : Parameters) (input : Inputs)
    (layout : Layout b K) (f g : Coefficients b K) (s : State)
    (hone : s.natReg 6 = 1)
    (hcount : s.natReg 4 = Fintype.card (Basis b K × Basis b K))
    (hmem : Represents layout f g 0 s.realMem)
    (hmeta : ScheduleMatches layout s.natMem (s.natReg 5)
      (Finset.univ : Finset (Basis b K × Basis b K)).toList) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 56*(K+1)^2*4^K*36^b+5 ∧
      Represents layout f g (SKCoefficient.mul f g) t.realMem ∧
      t.natMem = s.natMem := by
  obtain ⟨count, t, he, hc, hi⟩ := program_realized params input s hone
  refine ⟨count, t, he, ?_, ?_, hi.2.1⟩
  · rw [hcount, card_multiplication_pairs] at hc
    nlinarith [hc]
  · have hr := schedule_represents layout f g s.natMem
      (Finset.univ : Finset (Basis b K × Basis b K)).toList
      (s.natReg 5) 0 s.realMem hmem hmeta
    rw [← SKDenseExecution.denseMul_correct]
    rw [hi.1, hcount]
    simpa only [SKDenseExecution.denseMul, Finset.length_toList, Finset.card_univ] using hr

/-- A runtime generator can use numerical lexicographic order, independently
of the library's finite enumeration order. -/
theorem multiplication_realized_permutation {b K : ℕ} (params : Parameters) (input : Inputs)
    (layout : Layout b K) (f g : Coefficients b K) (s : State)
    (pairs : List (Basis b K × Basis b K))
    (hperm : pairs.Perm (Finset.univ : Finset (Basis b K × Basis b K)).toList)
    (hone : s.natReg 6 = 1) (hcount : s.natReg 4 = pairs.length)
    (hmem : Represents layout f g 0 s.realMem)
    (hmeta : ScheduleMatches layout s.natMem (s.natReg 5) pairs) :
    ∃ count t, Exec params input program s count t ∧
      count ≤ 56*(K+1)^2*4^K*36^b+5 ∧
      Represents layout f g (SKCoefficient.mul f g) t.realMem ∧
      t.natMem = s.natMem := by
  obtain ⟨count, t, he, hc, hi⟩ := program_realized params input s hone
  have hlength := hperm.length_eq
  simp only [Finset.length_toList, Finset.card_univ, card_multiplication_pairs] at hlength
  refine ⟨count, t, he, ?_, ?_, hi.2.1⟩
  · rw [hcount, hlength] at hc
    nlinarith [hc]
  · have hr := schedule_represents layout f g s.natMem pairs (s.natReg 5) 0 s.realMem hmem hmeta
    have hval : SKDenseExecution.pushLoop f g pairs 0 = SKCoefficient.mul f g := by
      rw [← SKDenseExecution.denseMul_correct, SKDenseExecution.denseMul]
      rw [SKDenseExecution.pushLoop_correct, SKDenseExecution.pushLoop_correct]
      rw [(hperm.map (fun p => fun z => pairContribution p.1 p.2 z (f p.1) (g p.2))).sum_eq]
    rw [hi.1, hcount]
    rwa [hval] at hr

end Manuscript.SKRestrictedAlgebra
