import Manuscript.SKCandidateSource
import Manuscript.RestrictedPhysicalPreparation
import Manuscript.InputIndices

noncomputable section
namespace Manuscript.SKCandidateSource
open RestrictedMachine RestrictedMaskBridge SKGeneratedLabels Model InputPreparation

/-- The source hypotheses are obtained from the already executed raw-input
preparation. In particular, weights are proved outputs, not extra inputs. -/
theorem physicalData_of_preparation {N M : ℕ} (hN : 0<N)
    (order : Fin M≃Edge N {2}) (beta h epsilon delta : ℝ) (J : Edge N {2}→ℝ)
    (tape : ℕ→ℕ) (a : ℕ→ℝ) (params : Parameters)
    (hparams : params 2=a 2) (budgetBase : ℕ) (s : State)
    (hs : RestrictedPreparation.Ready params
      (RestrictedInputEncoding.encode order beta h epsilon delta J tape) budgetBase s) :
    PhysicalData order a beta h J s := by
  have hp := RestrictedPhysicalPreparation.physical_cache hN order beta h epsilon delta J tape a params
    (by intro p hp;simpa only [Finset.mem_singleton.mp hp] using hparams) budgetBase s hs
  refine ⟨?_,?_,?_,hp.1,hp.2.1⟩
  · simpa only [RestrictedInputEncoding.nat_size] using hs.1.1
  · simpa only [RestrictedInputEncoding.nat_count] using hs.1.2.1
  · have hh := hs.1.2.2.2.2.2.2.1
    simpa only [RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,
      (RestrictedInputEncoding.real_fields order beta h epsilon delta J tape).1,
      prepareField_mean] using hh

theorem PhysicalData.transport {N M : ℕ} (order : Fin M≃Edge N {2})
    (a : ℕ→ℝ) (beta h : ℝ) (J : Edge N {2}→ℝ) {s t : State}
    (hs : PhysicalData order a beta h J s)
    (hn : ∀r,500≤r → r≤501 → t.natReg r=s.natReg r)
    (hr : t.realReg 504=s.realReg 504)
    (he : ∀j,j<M → t.natMem j=s.natMem j)
    (hw : ∀j,j<2*M → t.realMem j=s.realMem j) : PhysicalData order a beta h J t := by
  refine ⟨(hn 500 (by omega) (by omega)).trans hs.size,
    (hn 501 (by omega) (by omega)).trans hs.count,hr.trans hs.mean,?_,?_⟩
  · intro j;rw [he j.val j.isLt];exact hs.edges j
  · intro j;rw [hw (2*j.val) (by have:=j.isLt;omega)];exact hs.weights j

theorem selected_length {N : ℕ} (A : Finset (Fin N)) : (selectedVertices A).length=A.card := by
  rw [←List.toFinset_card_of_nodup (selectedVertices_nodup A),selectedVertices_toFinset]

@[simp] theorem branches_card {N : ℕ} (A : Finset (Fin N)) : branchCount A=A.card+1 := by
  rw [branchCount,selected_length]

@[simp] theorem outside_card {N : ℕ} (A : Finset (Fin N)) : outsideCount A=N-A.card := by
  rw [outsideCount,selected_length,Finset.card_compl];simp

theorem source_operationBound_le {N : ℕ} (s : State) (A : Finset (Fin N))
    (hM : s.natReg 501≤N*N) : operationBound s A≤1000*(N+1)^4 := by
  have hb : branchCount A≤N+1 := by rw [branches_card];have:=Finset.card_le_univ A;simpa using this
  have hu : outsideCount A≤N := by rw [outside_card];omega
  have hbs : branchCount A*branchCount A≤(N+1)^2 := by
    rw [pow_two];exact Nat.mul_self_le_mul_self hb
  have hus : outsideCount A*outsideCount A≤(N+1)^2 := by
    rw [pow_two];exact Nat.mul_self_le_mul_self (by omega)
  have hbu : branchCount A*outsideCount A≤(N+1)^2 := by
    rw [pow_two];exact Nat.mul_le_mul hb (by omega)
  have hinner : 18*N+34*s.natReg 501+96≤148*(N+1)^2 := by nlinarith
  have hm := Nat.mul_le_mul (show outsideCount A*outsideCount A+
      branchCount A*outsideCount A+branchCount A*branchCount A≤3*(N+1)^2 by omega) hinner
  unfold operationBound
  nlinarith [sq_nonneg (N:ℤ)]

theorem physical_count_le {N M : ℕ} (order : Fin M≃Edge N {2}) : M≤N*N := by
  have hc := Fintype.card_congr order
  simp only [Fintype.card_fin,InputIndices.card_edges_eq_sum_choose,Finset.sum_singleton] at hc
  rw [hc,←pow_two]
  exact Nat.choose_le_pow N 2

theorem source_operationBound_physical {N M : ℕ} (order : Fin M≃Edge N {2})
    (s : State) (hM : s.natReg 501=M) (A : Finset (Fin N)) :
    operationBound s A≤1000*(N+1)^4 :=
  source_operationBound_le s A (by rw [hM];exact physical_count_le order)

end Manuscript.SKCandidateSource
