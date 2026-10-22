import Manuscript.HigherOrderFinal
import Manuscript.SKFinal
import Manuscript.HigherOrderCorollaries
import Manuscript.SKCorollaries

/-! The two exhaustive model cases of Theorem 1.1, together with the fixed
positive raw-tail constant. The aliases preserve the explicit accuracy
statements and bounds on the defined operation counters. PrimitiveTheorem
adds the complete fixed-program realization and actual instruction bounds. -/

noncomputable section
namespace Manuscript

/-- Theorem 1.1 for every nonempty finite mixture of orders at least three.
The min/max interaction orders are computed from the actual active set. -/
alias theorem_1_1_higher := HigherOrderFinal.canonical_end_to_end

/-- Theorem 1.1 for SK, with the independent finite coloring law included. -/
alias theorem_1_1_sk := SKFinal.end_to_end

/-- The constant c in Theorem 1.1 depends only on the fixed mixture and B.
It is independent of the input size, actual beta, field, tolerances and law. -/
theorem raw_cutoff_constant_pos (P : Finset ℕ) (a : ℕ → ℝ) {B : ℝ}
    (hB : 0 < B) (hBT : B < MixedThreshold.betaF P a) :
    0 < OriginalLawLowerTail.rawConstant B (MixedThreshold.theta P a B) :=
  OriginalLawLowerTail.rawConstant_pos hB (MixedThreshold.theta_range P a hB hBT).1
    (MixedThreshold.theta_range P a hB hBT).2

alias remark_1_2_higher_relative := HigherOrderCorollaries.relative_counting
alias remark_1_2_sk_relative := SKCorollaries.relative_counting
alias remark_1_2_higher_polynomial_failure := HigherOrderCorollaries.polynomial_confidence
alias remark_1_2_sk_polynomial_failure := SKCorollaries.polynomial_confidence
alias remark_1_2_fourth_moment := UniformTau.tau_tendsto_zero_fourth
alias remark_1_2_bounded_disorder := UniformTau.tau_eventually_zero_of_bounded

end Manuscript
