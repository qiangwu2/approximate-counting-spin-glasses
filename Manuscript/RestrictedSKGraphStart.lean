import Manuscript.RestrictedSKStart

noncomputable section
namespace Manuscript.RestrictedSKGraphStart
open RestrictedMachine Model InputPreparation

/-- Direct mean-square budget read from the raw accuracy slot. -/
def budgetCode : List Instruction := [.nconst 579 2,.nadd 579 501 579,.readRealInput 508 579]
def program (a : ℕ→ℝ) (B rho : ℝ) : Program :=
  .seq (RestrictedPreparation.program (RestrictedParameters.budgetBase 2))
    (.seq (code budgetCode) (RestrictedSKController.program a B rho))

structure Ready {N M : ℕ} (order : Fin M≃Edge N {2}) (a : ℕ→ℝ)
    (B rho beta h u : ℝ) (J : Edge N {2}→ℝ) (s : State) : Prop where
  physical : SKCandidateSource.PhysicalData order a beta h J s
  plus : s.realReg 505=FieldExpansion.spinWeight h false
  minus : s.realReg 506=FieldExpansion.spinWeight h true
  budget : s.realReg 508=u
  cutoff : s.natReg 510=(SKControl.control N a B rho u).branchLimit
  exact : s.natReg 511=(SKControl.control N a B rho u).exact.toNat
  edges : s.natReg 512=(SKControl.control N a B rho u).edgeLimit
  trials : s.natReg 513=(SKControl.control N a B rho u).trials

theorem program_exec {N M : ℕ} (hN : 0<N) (a : ℕ→ℝ)
    (B rho beta h u : ℝ) (order : Fin M≃Edge N {2})
    (J : Edge N {2}→ℝ) (tape : ℕ→ℕ) :
    ∃count t,Exec (RestrictedParameters.sk a B rho)
      (RestrictedInputEncoding.encode order beta h u 1 J tape)
      (program a B rho) initial count t ∧ Ready order a B rho beta h u J t ∧
      count≤141*M+78*N+9*(SKControl.control N a B rho u).operations+366 := by
  let params:=RestrictedParameters.sk a B rho
  let raw:=RestrictedInputEncoding.encode order beta h u 1 J tape
  obtain ⟨prep,he,hready⟩:=RestrictedPreparation.program_exec params raw initial (RestrictedParameters.budgetBase 2)
  obtain ⟨hmask,hweight,hlog⟩:=RestrictedPhysicalPreparation.physical_cache hN order beta h u 1 J tape a params
    (by intro p hp;simp only [Finset.mem_singleton] at hp;subst p;exact RestrictedParameters.sk_model a B rho) _ prep hready
  rcases hready.1 with ⟨rN,rM,rh,re,rd,rb,rm,rp,rn,rl,ru,rz⟩
  have fields:=RestrictedInputEncoding.real_fields order beta h u 1 J tape
  have rN' : prep.natReg 500=N := by simpa [raw] using rN
  have rM' : prep.natReg 501=M := by simpa [raw] using rM
  have rm' : prep.realReg 504=Real.tanh h := by
    simpa only [raw,RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,fields.1,prepareField_mean] using rm
  have rp' : prep.realReg 505=FieldExpansion.spinWeight h false := by
    have hp : prep.realReg 505=(prepareField N h).plusWeight := by
      simpa only [raw,RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,fields.1] using rp
    exact hp.trans (prepareField_weight N h false)
  have rn' : prep.realReg 506=FieldExpansion.spinWeight h true := by
    have hp : prep.realReg 506=(prepareField N h).minusWeight := by
      simpa only [raw,RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,fields.1] using rn
    exact hp.trans (prepareField_weight N h true)
  let budgeted:=runCode params raw budgetCode prep
  have bu : budgeted.realReg 508=u := by
    simp [budgeted,budgetCode,runCode,step,rM',raw,fields.2.1]
  have bn : budgeted.natReg 500=N := by simp [budgeted,budgetCode,runCode,step,rN']
  obtain ⟨cc,t,hctl,hcc,hk,hx,hL,hR,hn,hr,hrm,hnm⟩:=RestrictedSKController.program_exec_precise raw budgeted a B rho
  refine ⟨141*M+186+(8+cc),t,?_,?_,?_⟩
  · have hh:=Exec.seq he (Exec.seq (exec_code params raw budgetCode prep) hctl)
    simpa [program,params,raw,budgetCode,codeCost,instrCost,RestrictedInputEncoding.nat_count,budgeted] using hh
  · refine ⟨?_,?_,?_,(hr 508 (by omega)).trans bu,?_,?_,?_,?_⟩
    · refine ⟨?_,?_,?_,?_,?_⟩
      · rw [hn 500 (by omega) (by omega)];exact bn
      · rw [hn 501 (by omega) (by omega)];simp [budgeted,budgetCode,runCode,step,rM']
      · rw [hr 504 (by omega)];simpa [budgeted,budgetCode,runCode,step] using rm'
      · intro j;rw [hnm];exact hmask j
      · intro j;rw [hrm];exact hweight j
    · rw [hr 505 (by omega)];simpa [budgeted,budgetCode,runCode,step] using rp'
    · rw [hr 506 (by omega)];simpa [budgeted,budgetCode,runCode,step] using rn'
    · simpa only [bn,bu] using hk
    · simpa only [bn,bu] using hx
    · simpa only [bn,bu] using hL
    · simpa only [bn,bu] using hR
  · rw [bn,bu] at hcc
    omega

end Manuscript.RestrictedSKGraphStart
