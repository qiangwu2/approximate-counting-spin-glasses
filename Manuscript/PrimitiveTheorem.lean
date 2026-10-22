import Manuscript.RestrictedHigherFinal
import Manuscript.RestrictedSKFinal
import Manuscript.RestrictedHigherGraphFinal
import Manuscript.RestrictedSKGraphFinal
import Manuscript.RestrictedDeterminism

/-! Public endpoints for the actual finite-program implementation.
The model parameters fix the program before raw inputs and random outcomes.
Accuracy and instruction-count conclusions have no assumed realization contract. -/
noncomputable section
namespace Manuscript

alias theorem_1_1_higher_primitive := RestrictedHigherFinal.end_to_end
alias theorem_1_1_sk_primitive := RestrictedSKFinal.end_to_end
alias proposition_5_2_higher_primitive := RestrictedHigherGraphFinal.end_to_end
alias proposition_5_2_sk_primitive := RestrictedSKGraphFinal.end_to_end

end Manuscript
