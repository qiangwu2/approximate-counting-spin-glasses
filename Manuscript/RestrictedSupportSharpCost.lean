import Manuscript.RestrictedSupportExecution
import Manuscript.InputIndices

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSupportSharpCost
open RestrictedLocalSum

/-- The explicit trace bound has the polynomial prefactor in Proposition 3.3. -/
theorem factor_bound (d : Data) :
    RestrictedSupportCost.factor d+12≤1000*(d.N+1)*(d.M+1) := by
  simp only [RestrictedSupportCost.factor,termCost]
  nlinarith

theorem enumeration_pos (N k : ℕ) :
    1≤∑j∈Finset.range (k+1),N.choose j*2^j := by
  have hh:=Finset.single_le_sum (fun j (_ : j∈Finset.range (k+1)) => Nat.zero_le (N.choose j*2^j))
    (show 0∈Finset.range (k+1) by simp)
  simpa using hh

theorem trace_bound (d : Data) {k : ℕ} (hk : k≤d.N) :
    RestrictedSupportProgram.totalCost d k 0 (k+1)+12≤
      1000*(d.N+1)*(d.M+1)*(∑j∈Finset.range (k+1),d.N.choose j*2^j) := by
  have h:=RestrictedSupportCost.total_bound d hk
  have hp:=enumeration_pos d.N k
  have hf:=Nat.mul_le_mul_right (∑j∈Finset.range (k+1),d.N.choose j*2^j) (factor_bound d)
  nlinarith

/-- With every interaction order at most Pmax, the genuine instruction
count satisfies the manuscript's C_P (N+1)^(Pmax+2) enumeration bound. -/
theorem physical_trace_bound (d : Data) {Pmax : ℕ} (hN : 0<d.N)
    (P : Finset ℕ) (hP : ∀p∈P,p≤Pmax)
    (order : Fin d.M≃Model.Edge d.N P) {k : ℕ} (hk : k≤d.N) :
    RestrictedSupportProgram.totalCost d k 0 (k+1)+12≤
      1000*(P.card+1)*(d.N+1)^(Pmax+2)*
        (∑j∈Finset.range (k+1),d.N.choose j*2^j) := by
  have hcard : d.M=Fintype.card (Model.Edge d.N P) := by
    simpa using Fintype.card_congr order
  have hc:=InputIndices.card_edges_le hN P hP
  have hc' : d.M≤P.card*(d.N+1)^Pmax := by
    rw [hcard]
    exact hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hp : 1≤(d.N+1)^Pmax := one_le_pow₀ (by omega)
  have hm : d.M+1≤(P.card+1)*(d.N+1)^Pmax := by nlinarith
  have hn : d.N+1≤(d.N+1)^2 := by nlinarith
  have hf : 1000*(d.N+1)*(d.M+1)≤1000*(P.card+1)*(d.N+1)^(Pmax+2) := by
    calc
      _≤1000*(d.N+1)^2*((P.card+1)*(d.N+1)^Pmax) := by gcongr
      _=_ := by rw [pow_add];ring
  exact (trace_bound d hk).trans (Nat.mul_le_mul_right _ hf)
end Manuscript.RestrictedSupportSharpCost
