import Manuscript.RestrictedInputScalars
import Manuscript.RestrictedInputCache
import Manuscript.RestrictedInputEncoding

noncomputable section
namespace Manuscript.RestrictedPreparation
open RestrictedMachine

def program (budgetBase : ℕ) : Program := .seq (code (RestrictedInputScalars.scalarCode budgetBase))
  (.seq RestrictedInteractions.tableProgram RestrictedInputCache.program)

def Ready (params : Parameters) (input : Inputs) (budgetBase : ℕ) (s : State) : Prop :=
  RestrictedInputScalars.Ready params input budgetBase s ∧
  (∀ j, j < input.nat 1 → s.natMem j=input.nat (input.nat 1+2+j)) ∧
  (∀ j, j < input.nat 1 → s.realMem (2*j)=(RestrictedInteractions.tableEdge params input j).weight ∧
    s.realMem (2*j+1)=(RestrictedInteractions.tableEdge params input j).logCosh) ∧
  s.realReg 510=(InputPreparation.prepareField (input.nat 0) (input.real (input.nat 1+1))).logBase+
    ∑ j∈Finset.range (input.nat 1),(RestrictedInteractions.tableEdge params input j).logCosh

theorem table_frame (params : Parameters) (input : Inputs) {s t : State} {c : ℕ}
    (he : Exec params input RestrictedInteractions.tableProgram s c t) :
    (∀ r, 67 ≤ r → t.natReg r=s.natReg r) ∧
    (∀ r, 61 ≤ r → t.realReg r=s.realReg r) := by
  refine ⟨?_,?_⟩
  · intro r hr
    apply he.natReg_frame
    simp [RestrictedInteractions.tableProgram,RestrictedInteractions.tableInit,
      RestrictedInteractions.tableBody,RestrictedInteractions.tablePrefix,RestrictedInteractions.tableSuffix,
      RestrictedInteractions.readEdgeCode,RestrictedInteractions.edgeCode,
      code,Program.All,Instruction.natDestination]; omega
  · intro r hr
    apply he.realReg_frame
    simp [RestrictedInteractions.tableProgram,RestrictedInteractions.tableInit,
      RestrictedInteractions.tableBody,RestrictedInteractions.tablePrefix,RestrictedInteractions.tableSuffix,
      RestrictedInteractions.readEdgeCode,RestrictedInteractions.edgeCode,
      code,Program.All,Instruction.realDestination]; omega

theorem scalar_ready_transport (params : Parameters) (input : Inputs) (budgetBase : ℕ)
    {s t : State} (hs : RestrictedInputScalars.Ready params input budgetBase s)
    (hn : ∀ r, 500 ≤ r → r ≤ 501 → t.natReg r=s.natReg r)
    (hr : ∀ r, 500 ≤ r → r ≤ 509 → t.realReg r=s.realReg r) :
    RestrictedInputScalars.Ready params input budgetBase t := by
  simpa only [RestrictedInputScalars.Ready,hn 500 (by omega) (by omega),hn 501 (by omega) (by omega),
    hr 500 (by omega) (by omega),hr 501 (by omega) (by omega),hr 502 (by omega) (by omega),
    hr 503 (by omega) (by omega),hr 504 (by omega) (by omega),hr 505 (by omega) (by omega),
    hr 506 (by omega) (by omega),hr 507 (by omega) (by omega),hr 508 (by omega) (by omega),
    hr 509 (by omega) (by omega)] using hs

theorem program_exec (params : Parameters) (input : Inputs) (s : State) (budgetBase : ℕ) :
    ∃ t, Exec params input (program budgetBase) s (141*input.nat 1+186) t ∧
      Ready params input budgetBase t := by
  obtain ⟨a,ha,ar,_,_⟩ := RestrictedInputScalars.scalar_exec params input s budgetBase
  obtain ⟨d,hd,dtable⟩ := RestrictedInteractions.table_realized params input a
  have df := table_frame params input hd
  have dr : RestrictedInputScalars.Ready params input budgetBase d :=
    scalar_ready_transport params input budgetBase ar (fun r hr _ => df.1 r (by omega))
      (fun r hr _ => df.2 r (by omega))
  have dN : d.natReg 501=input.nat 1 := dr.2.1
  have dlog : d.realReg 507=(InputPreparation.prepareField (input.nat 0)
      (input.real (input.nat 1+1))).logBase := dr.2.2.2.2.2.2.2.2.2.1
  obtain ⟨t,ht,tm,tl,trm⟩ := RestrictedInputCache.program_exec params input d
  have tf := RestrictedInputCache.program_frame params input ht
  refine ⟨t,?_,?_,?_,?_,?_⟩
  · have he := Exec.seq ha (Exec.seq hd ht)
    convert he using 1 <;> first | rfl | (rw [dN]; omega)
  · exact scalar_ready_transport params input budgetBase dr
      (fun r hr _ => tf.1 r (by omega)) (fun r hr hb => tf.2 r (by omega) (by omega))
  · simpa only [dN] using tm
  · intro j hj; rw [trm]; exact dtable j hj
  · rw [tl,dlog,dN]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (dtable j (Finset.mem_range.mp hj)).2

end Manuscript.RestrictedPreparation
