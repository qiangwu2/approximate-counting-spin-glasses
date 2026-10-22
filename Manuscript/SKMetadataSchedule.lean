import Manuscript.SKMetadataTable
import Manuscript.SKIndexSpecifications

noncomputable section
namespace Manuscript.SKMetadataSchedule
open RestrictedMachine RestrictedMachine.IndexGeneration SKBasisEncoding SKIndexSpecifications
open SpinGlass SKCoefficient SKRestrictedAlgebra

def pairEquiv (b K : ℕ) : (Basis b K×Basis b K) ≃
    Fin (((K+1)*2^K*6^b)*((K+1)*2^K*6^b)) :=
  (Equiv.prodCongr (basisEquiv b K) (basisEquiv b K)).trans finProdFinEquiv
def numericPairs (b K : ℕ) : List (Basis b K×Basis b K) :=
  (List.finRange (((K+1)*2^K*6^b)*((K+1)*2^K*6^b))).map (pairEquiv b K).symm

theorem numericPairs_permutation (b K : ℕ) :
    (numericPairs b K).Perm (Finset.univ : Finset (Basis b K×Basis b K)).toList := by
  apply (List.perm_ext_iff_of_nodup
    ((List.nodup_finRange _).map (pairEquiv b K).symm.injective) (Finset.nodup_toList _)).mpr
  intro z
  have hz : z∈numericPairs b K := List.mem_map.mpr
    ⟨pairEquiv b K z,List.mem_finRange _,(pairEquiv b K).symm_apply_apply z⟩
  exact ⟨fun _ => Finset.mem_toList.mpr (Finset.mem_univ z), fun _ => hz⟩

theorem numericPairs_length (b K : ℕ) : (numericPairs b K).length=
    ((K+1)*2^K*6^b)*((K+1)*2^K*6^b) := by simp [numericPairs]

theorem numericPairs_indices (b K j : ℕ) (hj : j<(numericPairs b K).length) :
    encode (numericPairs b K)[j].1=j/((K+1)*2^K*6^b) ∧
    encode (numericPairs b K)[j].2=j%((K+1)*2^K*6^b) := by
  simp [numericPairs,List.getElem_map,List.getElem_finRange,pairEquiv,encode,finProdFinEquiv]

theorem schedule_of_indexed {b K : ℕ} (layout : Layout b K) (memory : ℕ→ℕ)
    (pairs : List (Basis b K×Basis b K)) (base : ℕ)
    (h : ∀ j (hj : j<pairs.length), RecordMatches layout memory (base+4*j) pairs[j]) :
    ScheduleMatches layout memory base pairs := by
  induction pairs generalizing base with
  | nil => trivial
  | cons x xs ih =>
    constructor
    · have hh := h 0 (by simp)
      change RecordMatches layout memory base x at hh
      exact hh
    · apply ih (base+4)
      intro j hj
      have hh := h (j+1) (by simpa using hj)
      change RecordMatches layout memory (base+4*(j+1)) xs[j] at hh
      convert hh using 1 <;> omega

theorem record_congr {b K : ℕ} (layout : Layout b K) (m m' : ℕ→ℕ) (p : ℕ)
    (pair : Basis b K×Basis b K)
    (h : ∀ j<4, m (p+j)=m' (p+j)) : RecordMatches layout m p pair ↔ RecordMatches layout m' p pair := by
  cases hb : basisMul pair.1 pair.2 with
  | none => simpa [RecordMatches,hb] using congrArg (·=0) (by simpa using h 0 (by omega))
  | some z => simp [RecordMatches,hb,show m p=m' p by simpa using h 0 (by omega),
      h 1 (by omega),h 2 (by omega),h 3 (by omega)]

def TableRegisters (b K base : ℕ) (s : State) : Prop :=
  s.natReg 142=6^b ∧ s.natReg 143=2^K ∧ s.natReg 144=K ∧
  s.natReg 145=b ∧ s.natReg 146=K ∧
  s.natReg 148=base ∧ s.natReg 149=base+(K+1)*2^K*6^b ∧
  s.natReg 150=base+2*((K+1)*2^K*6^b) ∧ s.natReg 166=(K+1)*2^K*6^b

theorem metadata_schedule (b K base : ℕ) (s : State) (hs : TableRegisters b K base s) :
    ScheduleMatches (denseLayout b K base)
      (metadataPrefix s.natMem (s.natReg 147) (indexedRecord s) (s.natReg 166*s.natReg 166))
      (s.natReg 147) (numericPairs b K) := by
  rcases hs with ⟨hq,hp,hcap,hb,hK,hl,hr,ho,hM⟩
  apply schedule_of_indexed
  intro j hj
  let xy := (numericPairs b K)[j]
  have hxy := numericPairs_indices b K j hj
  let g := writeNatReg (writeNatReg (writeNatReg s 140 (encode xy.1)) 141 (encode xy.2)) 147 (s.natReg 147+4*j)
  have hg : Registers base xy.1 xy.2 g := by
    simp [Registers,g,hq,hp,hcap,hb,hK,hl,hr,ho]
  have hm := emitted_record_matches base xy.1 xy.2 g hg
  have hptr : g.natReg 147=s.natReg 147+4*j := by simp [g]
  have hv : pairRecord g=indexedRecord s j := by
    simp [pairRecord,indexedRecord,g,hxy.1,hxy.2,hM,xy]
  apply (record_congr (denseLayout b K base) _
    (writeRecord g.natMem (g.natReg 147) (pairRecord g)) (s.natReg 147+4*j) xy ?_).mpr
  · simpa only [hptr] using hm
  · intro offset hoff
    rw [show s.natReg 147+4*j+offset=(s.natReg 147)+4*j+offset by rfl,
      metadataPrefix_inside _ _ _ _ _ _ (by rw [hM]; simpa [numericPairs_length] using hj) hoff]
    rw [hptr,writeRecord_inside _ _ _ _ hoff,hv]

theorem complete_metadata_execution (params : Parameters) (input : Inputs) (b K base : ℕ)
    (s : State) (hs : TableRegisters b K base s) :
    ∃ c t, Exec params input metadataProgram s c t ∧
      c≤((K+1)*2^K*6^b)^2*(52*b+29*K+157)+11 ∧
      ScheduleMatches (denseLayout b K base) t.natMem (s.natReg 147) (numericPairs b K) ∧
      t.realMem=s.realMem := by
  obtain ⟨c,t,he,hc,hm,_,hr⟩ := metadata_execution params input s
  refine ⟨c,t,he,?_,?_,hr⟩
  · simpa [hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.2.2.2,pow_two] using hc
  · rw [hm]
    exact metadata_schedule b K base s hs

end Manuscript.SKMetadataSchedule
