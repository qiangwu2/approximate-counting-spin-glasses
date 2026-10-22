import Manuscript.SKGeneratedExecution
import Manuscript.SKGhostPhysicalEvaluation
import Manuscript.SKPhysicalModel
import Manuscript.UniformPhysicalMass

noncomputable section
open scoped BigOperators
namespace Manuscript.SKPhysicalEstimator
open MeasureTheory SpinGlass.Disorder Model

def value (N D L R : ℕ) (a : ℕ→ℝ) (beta h : ℝ)
    (χ : SKColorEstimator.Colors (Fin N) L R) (J : Edge N {2}→ℝ) : ℝ :=
  (SKGeneratedExecution.estimator D L R χ (Real.tanh h)
    (SKGhostCoefficient.inputWeight N a beta J)).value

theorem value_eq (N D L R : ℕ) (hL : 0<L) (a : ℕ→ℝ) (beta h : ℝ)
    (χ : SKColorEstimator.Colors (Fin N) L R) (J : Edge N {2}→ℝ) :
    value N D L R a beta h χ J=SKColorEstimator.estimator Subtype.val Finset.univ D L R h
      (DisorderOrthogonality.physicalScale N {2} a beta) χ J := by
  unfold value
  rw [SKGeneratedExecution.estimator_value,SKGhostCoefficient.algorithm_eq_physical N D L R hL]

/-- Proposition 4.5's conditional unbiasedness for every physical input. -/
theorem unbiased (N D L R : ℕ) (hL : 0<L) (hR : 0<R)
    (a : ℕ→ℝ) (beta h : ℝ) (J : Edge N {2}→ℝ) :
    (∫χ,value N D L R a beta h χ J ∂SKColorEstimator.colorLaw (Fin N) L R)=
      SKPhysicalModel.truncation N D L a beta h J := by
  simp_rw [value_eq N D L R hL]
  exact SKColorEstimator.estimator_integral Subtype.val Finset.univ D hL hR
    (by intro e he;simpa using edge_order_mem e) h _ J

/-- Proposition 4.5's displayed original-law color error with the actual C₊,
for arbitrary retained parameters, with no assumed graphical-mass bound. -/
theorem coloring_mse (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : SymmetricLaw μ) (hunit : UnitSecondMoment μ)
    {N D L R : ℕ} (hN : 2≤N) (hL : 0<L) (hR : 0<R)
    (a : ℕ→ℝ) (ha : a 2=1) {beta B h rho : ℝ}
    (hb : 0≤beta) (hbB : beta≤B) (hB : 0<B) (hB1 : B<1)
    (hfield : |h|≤rho*(N:ℝ)^(-(1/4:ℝ))) :
    (∫χJ : SKColorEstimator.Colors (Fin N) L R × (Edge N {2}→ℝ),
      (value N D L R a beta h χJ.1 χJ.2-
        SKPhysicalModel.truncation N D L a beta h χJ.2)^2
        ∂(SKColorEstimator.colorLaw (Fin N) L R).prod (iidLaw μ))≤
      UniformMixedMass.massConstant {2} a (MixedThreshold.betaPlus {2} a B^2) rho*
        Real.exp (2*(L:ℝ))/(R:ℝ) := by
  simp_rw [value_eq N D L R hL]
  have hc:=SKColorEstimator.coloring_mse_le μ hμ Subtype.val Finset.univ D hL hR
    (by intro e he;simpa using edge_order_mem e) h (DisorderOrthogonality.physicalScale N {2} a beta)
  have hm:=UniformPhysicalMass.physical_graphical_mass μ hunit N {2} a
    (by simp) (by simpa [ha]) (by simp) (by simpa using hN) hb hbB hB
    (by simpa only [MixedThreshold.betaF_sk a ha] using hB1) hfield
  have hm' : (∑Γ∈(Finset.univ : Finset (Edge N {2})).powerset,
      SKColorEstimator.graphMass μ Subtype.val h (DisorderOrthogonality.physicalScale N {2} a beta) Γ)≤
      UniformMixedMass.massConstant {2} a (MixedThreshold.betaPlus {2} a B^2) rho := hm
  apply hc.trans
  calc
    _≤(Real.exp (2*(L:ℝ))/(R:ℝ))*
      UniformMixedMass.massConstant {2} a (MixedThreshold.betaPlus {2} a B^2) rho :=
        mul_le_mul_of_nonneg_left hm' (by positivity)
    _=_ := by ring

end Manuscript.SKPhysicalEstimator
