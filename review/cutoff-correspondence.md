# Current Lemma 5.1 and Lean correspondence

This supplements `analytic-review.md`. It compares the current frozen source (SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`) with the actual files under `outputs/lean4-formalization`, rather than relying on the older package's manuscript identifier or theorem comments.

## Finding

The inspected cutoff definitions and their algorithmic uses match the current manuscript. I found no stale exponent, incorrect minimum interaction order, lost zero-field case, off-by-one cutoff, or incorrect fallback comparison. The existing package had the result distributed across several statements. The new file `LeanAdditions/CurrentCutoff.lean` gives a single proved theorem in the current manuscript's requested budget `u`.

`Manuscript.CurrentCutoff.lemma_5_1` was compiled successfully using Lean 4.32.1 through the base package's environment. Its axiom audit is saved in `LeanAdditions/CurrentCutoff-axioms.log` and reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or custom mathematical axiom is in this theorem's dependency closure. No base-package or canonical manuscript file was edited.

## Exact constant mapping

| Current manuscript object | Lean object | Assessment |
| --- | --- | --- |
| `kappa_min` | `kapMin` in `Manuscript.Cutoffs`; `SupportExponent.kappaMin pmin` for higher orders; 1 for SK | Same fixed lower exponent |
| `C_star` | The parameter `A` of `Manuscript.Cutoffs` | Same fixed support/branching scale |
| `gamma = min(1/8, exp(-(1+2/kappa_min))/C_star)` | `Cutoffs.gamma kapMin A` | Literal same expression |
| `kappa_min gamma/2 * log(2/(C_star gamma))` | `Cutoffs.cstar kapMin A`, via `CutoffSelection.hZero` | Same auxiliary rate; the Lean function named `cstar` is **not** the manuscript's `C_star` |
| `nu = (1/4) min{1,c1,auxiliary rate}` | `Cutoffs.nu kapMin A c1`, defined as `min c1 (min auxiliaryRate 1)/4` | Equal by commutativity/associativity of minimum |
| `N_0 = ceil(max{P,4,2/gamma})` | `Cutoffs.sizeThreshold P kapMin A` | Literal nested-maximum representation |
| `Phi_N(t)=kappa t log(N/(C_star t))`, `Phi_N(0)=0` | `SpinGlass.CutoffTail.phi kap A N t` | Same positive-argument expression; at zero the leading zero factor gives zero under Lean's totalized real operations |
| `C_t=kappa_min^(-1)(1+log(et C_star)/log(1/(C_star gamma)))` | `Cutoffs.workConstant kapMin A t` | The definition expands to `1/kapMin + log(exp(1)*t*A)/(kapMin*log(1/(A*gamma)))`, algebraically identical |
| `Lambda=log(C_Lambda/u)` | `AlgorithmBudgets.logBudget CΛ u` | Literal same expression |

The core `Cutoffs` existence and scan statements require `0<kapMin`, `kapMin<=kap`, `0<A`, `2/gamma<=N`, `0<Lambda`, and `Lambda<nu*N`. Their use in the new theorem derives the size and logarithmic-window hypotheses from `N>=N_0`, `0<u<1`, `CΛ>=1`, and `CΛ exp(-nu*N)<u`. Positivity of `nu` is established from `c1>0`. The work bound also requires `A>=1` and `t>=1`, which are exactly true in both manuscript regimes.

The definition provides `gamma<=1/8`, which proves the current strict range `0<gamma<1/4`. Some older helper theorems only state the weaker `gamma<=1` because that is all they consume. This is not a mismatch in the selected constant.

## Variable field exponent and zero field

`Manuscript.HigherFieldExponent` defines

- nonzero field: `alpha = log(rho/|tanh h|)/log N`;
- zero field: the finite value `(p-1)/(2p)`;
- `selectedKappa = min((p-2)/p, 2alpha-1/p)`.

The zero-field representative is enough to saturate the better exponent. Theorems `selectedKappa_zero` and `selectedKappa_eq` prove the exact current piecewise formula, rather than merely a smaller uniform exponent. The actual caller supplies `rho=max 1 rho_0`, matching `rho_1`.

The theorem `selectedKappa_ge_min` explicitly proves the lower bound for the supplied field. Its `N>=4` requirement is slightly stronger than the basic higher-order model's `N>=3`, but this is harmless: every nonexact branch first proves `N>=N_0>=4`. A possible model size `N=3` is on the exact branch, where no logarithmic field exponent is needed. The nonzero-field identity separately assumes `N>1` and is used only in the permitted nonexact range.

The constants `gamma`, `nu`, `N_0`, and `workConstant` all use `kapMin`, not `selectedKappa`. `Cutoffs.gamma_gap_variable`, `nu_le_variable`, and `phi_min_le` provide the required transport when the actual exponent increases. Thus both the cutoff and its error can adapt to `h`, while the operation exponent stays uniform over supplied `N,h`.

## Minimum and maximum interaction orders

The intermediate higher-order theorems allow any real `pmin>=3` that is a lower bound on every active integer order, and any natural `pmax` that is an upper bound. This is a valid generalization of the manuscript's actual extrema. The final entry point does not leave these as arbitrary user assumptions: `HigherOrderFinal.canonicalExecute` passes `P.min' hP` and `P.max' hP`, and `canonical_end_to_end` proves their needed inequalities using finite-set minimum and maximum theorems.

The scale `HigherOrderTail.scale` is `C_0^(1/kappaMin pmin)`, with `C_0 = exp(1 + sum_p B^2 a_p^2/p!) * (max 1 rho)^2`. This agrees with the current higher-order constant. The SK scale is `max 1 (SKBranching.branchConstant B (rho^2))`; expanding `eta=(1-B^2)/2` gives exactly the current `A_SK` and `C_star`. The corresponding `c1` definitions are respectively `(gamma/pmax)log(1/theta^2)` and `(3gamma/2)log(1/theta^2)`.

`HigherOrderTail.errorConstant` is `8(2+C_+)`. `SKAlgorithm.errorConstant` is `8(2C_SK+3C_+)`. Their mass constants use the comparison inverse temperature squared; the source notation such as `betaPlus P a B^2` parses as the square of the applied comparison temperature, consistently with the surrounding proof types and `LogApprox.constant`'s explicitly spaced version `betaPlus P a B ^ 2`.

## First omitted index, scan, and operation accounting

The manuscript selects the least retained cutoff `k` for which `Phi_N(k+1)>=Lambda`. The Lean bounded scan starts at 1, stops at `floor(gamma*N)`, and returns the first omitted index `m=k+1`. `cutoffScan_correct` proves `1<=m`, `m<=floor(gamma*N)`, the crossing inequality, and strict failure at every smaller positive index. `selectedCutoff` and the SK `branchCutoff` subtract one. The needed subtraction identity is always justified by `m>=1`; it is not assumed for a possibly zero return.

The default value in `Option.getD 1` is unreachable on an admitted nonexact branch, by the proved existence theorem. It does not silently choose a cutoff after a failed search.

`CutoffExecution.phiComputation` uses the same real formula and counts five arithmetic/logarithm operations. `scan` counts its comparisons and advancement as well. `boundedFloor` finds the upper bound by a descending finite scan, so the implementation does not depend on a free floor oracle. `cutoffSearch_found` identifies this counted execution with the certified abstract scan. `cutoffSearch_correct` proves the combined bound `10N+3` and the same first crossing. This bound applies to the cutoff-search subroutine under its declared operation convention; it is not by itself a statement about all graph-evaluator operations.

## Algorithm selection and error use

For both models, `exactBranch` is precisely

`N < N_0 OR nu*N <= log(C_Lambda/u)`.

This agrees with the manuscript's `Lambda>=nu*N` boundary. The negation used in the proofs gives `N>=N_0` and the strict nonexact inequality `Lambda<nu*N`. The exact branch evaluates the full local spin average and proves equality to the normalized partition function. The cutoff is independent of the disorder realization.

For higher orders, `mse_bound` obtains the actual `selectedKappa`, invokes the scan theorem, converts `m` to `m-1`, applies the physical support-tail theorem, and then uses `selected_error_bounds` and the concrete `support_error_budget`. The error estimate is not a hypothesis of this result.

For SK, `edgeLimit` is the ceiling of `Lambda/log(1/theta^2)`, and `trials` calls `colorTrials` with `2*edgeLimit`, giving the current ceiling of `exp(2L+Lambda)`. The `mse_bound` invokes the actual retained-graph estimator, physical truncation, and concrete error budget. This paragraph checks their selection and downstream use; the independent Section 4 audit remains responsible for correctness of the evaluator internals.

The higher-order counted control computes the same piecewise `kappa` from the cached field mean. `kappaComputation_value` and `control_cutoff` prove equality with the specification, including `h=0`. It charges the nonzero-field logarithms/divisions and the minimum comparison. The separate `control_operations` theorem accounts for the budget and branch control before adding the evaluator cost.

## New direct current-statement theorem

`LeanAdditions/CurrentCutoff.lean:30` proves `Manuscript.CurrentCutoff.lemma_5_1`. The theorem fixes `kapMin,A,c1,CΛ,P` first and establishes the admissibility of the explicit design constants. It then universally quantifies over `N`, the actual exponent `kap`, and `u`. Under the manuscript's `u` window it derives one natural `k` such that:

1. `k < floor(gamma*N)`;
2. `exp(-phi kap A N (k+1)) <= u/CΛ`;
3. for every real `t>=1`, `workConstant kapMin A t>0` and the full weighted binomial sum through `k` is at most `(N+1)*(CΛ/u)^workConstant`;
4. the counted search returns exactly `some(k+1)` and uses at most `10N+3` operations.

The theorem assumes neither a suitable cutoff nor a mass/work/error estimate. It derives the logarithmic window, invokes the existing proved bounded search, translates the first omitted index, and derives the error and cost bounds. The fixed `workConstant` has no dependence on the actual `kap`, `N`, or `u`, as required. The theorem's use of arbitrary `kap>=kapMin` is stronger than specializing to the field formula, and the existing field-transport theorems above provide that specialization without extra analytic assumptions.

Compilation succeeded with no diagnostics. The subsequent full theorem-dependency axiom print also succeeded and contained exactly `[propext, Classical.choice, Quot.sound]`.
