import Manuscript.SKMetadataSchedule
import Mathlib.Data.List.OfFn

noncomputable section
namespace Manuscript.SKMetadataSchedule
open SKBasisEncoding

theorem numericPairs_eq_pairList (b K : ℕ) : numericPairs b K=pairList b K := by
  simp only [numericPairs,pairList,basisList,List.finRange,List.map_ofFn]
  rw [List.ofFn_mul]
  simp only [List.product,List.map_ofFn,Function.comp_def]
  congr 1
  simp only [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply (pairEquiv b K).injective
  simp [pairEquiv,finProdFinEquiv]
  simp [Nat.mod_eq_of_lt j.isLt,Nat.add_div,Nat.div_eq_of_lt j.isLt,
    show 0<(K+1)*2^K*6^b by positivity]

end Manuscript.SKMetadataSchedule
