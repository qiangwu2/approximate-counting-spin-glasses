import Manuscript.RestrictedSKControlCost
import Manuscript.RestrictedPhysicalPreparation
import Manuscript.RestrictedSupportExecution
import Manuscript.SKCandidateSource
import Manuscript.SKFinal

noncomputable section
open scoped BigOperators
namespace Manuscript.RestrictedSKStart
open RestrictedMachine Model InputPreparation

def program (a : ℕ→ℝ) (B rho : ℝ) : Program :=
  .seq (RestrictedPreparation.program (RestrictedParameters.budgetBase 2))
    (RestrictedSKController.program a B rho)

structure Ready {N M : ℕ} (order : Fin M≃Edge N {2}) (a : ℕ→ℝ)
    (B rho beta h epsilon delta : ℝ) (J : Edge N {2}→ℝ) (s : State) : Prop where
  physical : SKCandidateSource.PhysicalData order a beta h J s
  plus : s.realReg 505=FieldExpansion.spinWeight h false
  minus : s.realReg 506=FieldExpansion.spinWeight h true
  logBase : s.realReg 510=InputPreparation.logBase N {2} a beta h J
  budget : s.realReg 508=(prepareBudget (LogApprox.constant {2} a B rho) delta epsilon
    (LogApprox.exponent {2} a B)).u
  cutoff : s.natReg 510=(SKControl.control N a B rho (s.realReg 508)).branchLimit
  exact : s.natReg 511=(SKControl.control N a B rho (s.realReg 508)).exact.toNat
  edges : s.natReg 512=(SKControl.control N a B rho (s.realReg 508)).edgeLimit
  trials : s.natReg 513=(SKControl.control N a B rho (s.realReg 508)).trials

theorem program_exec {N M : ℕ} (hN : 0<N) (a : ℕ→ℝ)
    (B rho beta h epsilon delta : ℝ) (order : Fin M≃Edge N {2})
    (J : Edge N {2}→ℝ) (tape : ℕ→ℕ) :
    ∃ count t,Exec (RestrictedParameters.sk a B rho)
      (RestrictedInputEncoding.encode order beta h epsilon delta J tape)
      (program a B rho) initial count t ∧
      Ready order a B rho beta h epsilon delta J t ∧
      count≤141*M+78*N+9*(SKControl.control N a B rho
        (prepareBudget (LogApprox.constant {2} a B rho) delta epsilon (LogApprox.exponent {2} a B)).u).operations+358 := by
  let params := RestrictedParameters.sk a B rho
  let raw := RestrictedInputEncoding.encode order beta h epsilon delta J tape
  obtain ⟨prep,he,hready⟩ := RestrictedPreparation.program_exec params raw initial (RestrictedParameters.budgetBase 2)
  obtain ⟨hmask,hweight,hlog⟩ := RestrictedPhysicalPreparation.physical_cache hN order beta h epsilon delta J tape a params
    (by intro p hp;simp only [Finset.mem_singleton] at hp;subst p;exact RestrictedParameters.sk_model a B rho) _ prep hready
  rcases hready.1 with ⟨rN,rM,rh,re,rd,rb,rm,rp,rn,rl,ru,rz⟩
  have fields := RestrictedInputEncoding.real_fields order beta h epsilon delta J tape
  have rN' : prep.natReg 500=N := by simpa [raw] using rN
  have rM' : prep.natReg 501=M := by simpa [raw] using rM
  have rm' : prep.realReg 504=Real.tanh h := by simpa only [raw,RestrictedInputEncoding.nat_size,
      RestrictedInputEncoding.nat_count,fields.1,prepareField_mean] using rm
  have rp' : prep.realReg 505=FieldExpansion.spinWeight h false := by
    have hp : prep.realReg 505=(prepareField N h).plusWeight := by
      simpa only [raw,RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,fields.1] using rp
    exact hp.trans (prepareField_weight N h false)
  have rn' : prep.realReg 506=FieldExpansion.spinWeight h true := by
    have hm : prep.realReg 506=(prepareField N h).minusWeight := by
      simpa only [raw,RestrictedInputEncoding.nat_size,RestrictedInputEncoding.nat_count,fields.1] using rn
    exact hm.trans (prepareField_weight N h true)
  have ru' : prep.realReg 508=(prepareBudget (LogApprox.constant {2} a B rho) delta epsilon
      (LogApprox.exponent {2} a B)).u := by
    rw [ru]
    simp only [RestrictedInputScalars.budget,raw,RestrictedInputEncoding.nat_count,
      fields.2.1,fields.2.2,params,(RestrictedParameters.sk_budget a B rho).1,
      (RestrictedParameters.sk_budget a B rho).2]
  obtain ⟨cc,t,hctl,hcc,hk,hx,hL,hR,hn,hr,hrm,hnm⟩ := RestrictedSKController.program_exec_precise raw prep a B rho
  have tb : t.realReg 508=prep.realReg 508 := hr 508 (by omega)
  refine ⟨141*M+186+cc,t,?_,?_,?_⟩
  · simpa only [program,params,raw,RestrictedInputEncoding.nat_count] using Exec.seq he hctl
  · refine ⟨?_,(hr 505 (by omega)).trans rp',(hr 506 (by omega)).trans rn',
      (hr 510 (by omega)).trans hlog,tb.trans ru',?_,?_,?_,?_⟩
    · refine ⟨(hn 500 (by omega) (by omega)).trans rN',
        (hn 501 (by omega) (by omega)).trans rM',(hr 504 (by omega)).trans rm',?_,?_⟩
      · intro j;rw [hnm];exact hmask j
      · intro j;rw [hrm];exact hweight j
    · simpa only [tb,rN'] using hk
    · simpa only [tb,rN'] using hx
    · simpa only [tb,rN'] using hL
    · simpa only [tb,rN'] using hR
  · rw [rN',ru'] at hcc
    omega

end Manuscript.RestrictedSKStart
