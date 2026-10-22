import Manuscript.RestrictedLayerProgram
import Manuscript.RestrictedLocalBridge

noncomputable section
namespace Manuscript.RestrictedLayerSemantics
open RestrictedMachine RestrictedLocalSum RestrictedHigherLayer

/-- Canonical physical data forgets mutable support/spin scratch. -/
def core (d : Data) : Data :=
  {d with
    U:=0
    spinBase:=0
    natMemory:=fun j => if d.edgeBase≤j ∧ j<d.edgeBase+d.M then d.natMemory j else 0}

theorem core_visible (d : Data) (hspace : d.edgeBase+d.M≤d.spinBase) :
    core (visible d)=core d := by
  simp only [core,visible]
  congr 1
  funext j
  by_cases hj : d.edgeBase≤j ∧ j<d.edgeBase+d.M
  · simp [hj,show j<d.spinBase by omega]
  · simp [hj]

theorem core_layerData (s : State) (hspace : s.natReg 284+s.natReg 283≤s.natReg 312) :
    core (RestrictedLayerProgram.layerData s)=core (data s) := by
  simp only [core,RestrictedLayerProgram.layerData,data]
  congr 1
  funext j
  by_cases hj : s.natReg 284≤j ∧ j<s.natReg 284+s.natReg 283
  · simp [hj,RestrictedSubsets.writeList_below _ _ _ _ (show j<s.natReg 312 by omega)]
  · simp [hj]

theorem localValue_core (d : Data) (u : ℕ) : localValue (core d) u=localValue d u := by
  unfold localValue
  congr 1
  apply List.map_congr_left
  intro T hT
  simp only [term,withSupport,core]
  congr 1
  suffices ∀ i m : ℕ, i+m≤d.M →
      RestrictedSpinTerm.edgeProduct d.N u T
        (fun j => if d.edgeBase≤j ∧ j<d.edgeBase+d.M then d.natMemory j else 0)
        d.realMemory d.edgeBase d.weightBase i m =
      RestrictedSpinTerm.edgeProduct d.N u T d.natMemory d.realMemory d.edgeBase d.weightBase i m by
    exact this 0 d.M (by omega)
  intro i m
  induction m generalizing i with
  | zero => intros; rfl
  | succ m ih =>
      intro hi
      simp only [RestrictedSpinTerm.edgeProduct]
      rw [if_pos (by omega),ih (i+1) (by omega)]

@[simp] theorem localCost_core (d : Data) (u : ℕ) : localCost (core d) u=localCost d u := rfl

theorem sumSupports_eq_list (d : Data) (a : ℝ) (base i : ℕ) (xs : List ℕ)
    (h : ∀ (j : ℕ) (hj : j<xs.length),d.natMemory (base+i+j)=xs[j]) :
    sumSupports d a base i xs.length=(xs.map (fun u => a*localValue d u)).sum := by
  induction xs generalizing i with
  | nil => simp [sumSupports]
  | cons x xs ih =>
      have h0 := h 0 (by simp)
      simp only [Nat.add_zero,List.getElem_cons_zero] at h0
      simp only [List.length_cons,sumSupports,List.map_cons,List.sum_cons]
      rw [h0,ih (i+1)]
      intro j hj
      convert h (j+1) (by simp; omega) using 1 <;> simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem workSupports_eq_list (d : Data) (base i : ℕ) (xs : List ℕ)
    (h : ∀ (j : ℕ) (hj : j<xs.length),d.natMemory (base+i+j)=xs[j]) :
    workSupports d base i xs.length=(xs.map (fun u => localCost d u+24)).sum := by
  induction xs generalizing i with
  | nil => simp [workSupports]
  | cons x xs ih =>
      have h0 := h 0 (by simp)
      simp only [Nat.add_zero,List.getElem_cons_zero] at h0
      simp only [List.length_cons,workSupports,List.map_cons,List.sum_cons]
      rw [h0,ih (i+1)]
      intro j hj
      convert h (j+1) (by simp; omega) using 1 <;> simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def value (d : Data) (k l : ℕ) : ℝ :=
  ((RestrictedSubsets.masks d.N l 0 1).map
    (fun u => SupportEvaluation.coefficient d.N k l*localValue d u)).sum

def cost (d : Data) (k l : ℕ) : ℕ :=
  31*(k-l)+RestrictedSubsets.work d.N l+
    ((RestrictedSubsets.masks d.N l 0 1).map (fun u => localCost d u+24)).sum+64

theorem layer_reads (s : State) (j : ℕ) (hj : j<(RestrictedLayerProgram.masks s).length) :
    (visible (RestrictedLayerProgram.layerData s)).natMemory (s.natReg 312+0+j)=
      (RestrictedLayerProgram.masks s)[j] := by
  simp only [visible,RestrictedLayerProgram.layerData,Nat.add_zero]
  rw [if_pos (by omega)]
  exact RestrictedSubsets.writeList_get _ _ _ _ hj

theorem layer_value (s : State) (hspace : s.natReg 284+s.natReg 283≤s.natReg 312) :
    sumSupports (visible (RestrictedLayerProgram.layerData s)) (RestrictedLayerProgram.coefficient s)
      (s.natReg 312) 0 (RestrictedLayerProgram.masks s).length=
      value (core (data s)) (s.natReg 310) (s.natReg 311) := by
  rw [sumSupports_eq_list _ _ _ _ _ (layer_reads s)]
  have hs : (RestrictedLayerProgram.layerData s).edgeBase+(RestrictedLayerProgram.layerData s).M≤
      (RestrictedLayerProgram.layerData s).spinBase := by dsimp [RestrictedLayerProgram.layerData,data]; omega
  have hc := (core_visible (RestrictedLayerProgram.layerData s) hs).trans (core_layerData s hspace)
  unfold value
  apply congrArg List.sum
  apply List.map_congr_left
  intro u hu
  rw [←localValue_core,hc]
  rfl

theorem layer_cost (s : State) : RestrictedLayerProgram.cost s=
    cost (core (data s)) (s.natReg 310) (s.natReg 311) := by
  unfold RestrictedLayerProgram.cost
  rw [workSupports_eq_list _ _ _ _ (layer_reads s)]
  rfl

theorem program_realized (params : Parameters) (input : Inputs) (s : State)
    (hspace : s.natReg 284+s.natReg 283≤s.natReg 312) :
    ∃ final, RestrictedRecursiveMachine.Exec table params input RestrictedLayerProgram.program s
        (cost (core (data s)) (s.natReg 310) (s.natReg 311)) final ∧
      final.realReg 311=value (core (data s)) (s.natReg 310) (s.natReg 311) ∧
      core (data final)=core (data s) ∧
      (∀ r, 310≤r → r≠313 → r≠314 → r≠315 → r≠316 → final.natReg r=s.natReg r) := by
  obtain ⟨final,he,hv,hd,hn⟩ := RestrictedLayerProgram.program_realized params input s hspace
  have hs : (RestrictedLayerProgram.layerData s).edgeBase+(RestrictedLayerProgram.layerData s).M≤
      (RestrictedLayerProgram.layerData s).spinBase := by dsimp [RestrictedLayerProgram.layerData,data]; omega
  have hs' : (data final).edgeBase+(data final).M≤(data final).spinBase := by
    have hE := congrArg Data.edgeBase hd
    have hM := congrArg Data.M hd
    have hB := congrArg Data.spinBase hd
    dsimp [visible] at hE hM hB
    rw [hE,hM,hB]; exact hs
  refine ⟨final,?_,hv.trans (layer_value s hspace),?_,hn⟩
  · rwa [layer_cost] at he
  · rw [←core_visible (data final) hs',hd,core_visible _ hs,core_layerData s hspace]

end Manuscript.RestrictedLayerSemantics
