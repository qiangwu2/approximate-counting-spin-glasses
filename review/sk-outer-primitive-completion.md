# SK outer execution refinement

The following new package modules were compiled individually with the package's pinned Lean/mathlib toolchain. Canonical manuscript sources were not changed.

- `RestrictedLabelPass`, `RestrictedCandidateLabels`: uniform digit scan generating ascending selected and complementary physical vertex labels; the ghost sentinel is appended last. The exact generated lists are proved equal to the finite-set encoding used by the graphical mathematics.
- `RestrictedCandidateCharges`, `RestrictedCandidateColors`, `RestrictedCandidateLabelPreparation`: actual RAM initialization of charge 1 on physical branch vertices and charge 0 on the ghost; each outside vertex's color is obtained by a charged raw-input read and remainder operation. Combined cost is at most `112*N+70`. Array separation and preservation of the physical prefix are proved.
- `RestrictedSKTrials`: actual natural arithmetic computes the raw tape offset `2*M+2+(mask*R+trial)*N`; a fixed candidate program is called, its result is added, and the accumulated result is divided by R. Its modular candidate premise is applied only to valid masks, trial indices below R, and the computed raw offset.
- `RestrictedSKMaskFold`: actual loads of stored candidate masks, repeated trial averaging, and estimator accumulation. The stored mask prefix survives every candidate execution.
- `RestrictedSKLayer`: actual fixed-cardinality subset recursion. The returned end pointer determines the label-array base; all subsequent array addresses are computed by instructions. It generates only the requested cardinality and does not scan the full powerset.
- `RestrictedSKOuter`: actual loop over cardinalities 0 through D. Its instruction bound is the sum of the subset-generator work and the individually proved candidate/trial costs.
- `RestrictedSKOuterBridge`: the executed list folds equal the manuscript's finite-set sums; the output equals `SKGeneratedExecution.estimator.value`. The same program is transported into the fixed shared two-procedure table used by the exact branch.
- `RestrictedSKTruncated`: instantiates every modular realization premise with the concrete `SKRawCandidate` implementation and `SKCandidateContract`. The theorem has no assumed output, runtime, arithmetic-evaluator, or metadata correctness premise. From the physical input invariant and one scratch-base inequality it derives a complete restricted-machine execution, exact estimator output in real register 572, the accumulated operation bound, and preservation of the physical input invariant.

The concrete endpoint is `Manuscript.RestrictedSKTruncated.program_exec`. Its program and procedure bodies are fixed independently of N, input disorder values, and random color outcomes. All random data are raw color words on the read-only tape; generated labels, charges, weights, algebra metadata, and coefficients are produced by charged instructions in the composed implementation.

The exact accumulated cost identity is `RestrictedSKOuterBridge.cost_range`; the final outer initialization/dispatch adds 12 steps. The per-mask contribution is `R*(bound(mask)+29)+35`, and each cardinality layer adds the proved subset-generation work and 66 steps. Parent integration supplies the uniform polynomial bound and composes the exact fallback, control, and final logarithm.

The axiom audit is saved in `sk-outer-primitive-axioms.txt`. The five audited headline theorems depend only on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or additional mathematical axiom occurs.

The execution model is the explicitly defined exact-real register machine with finite recursive procedures and charged stack/register operations. This is an operation-count result, not a floating-point roundoff or bit-complexity result.

## Closed final endpoints

After the outer composition, the parent assembled and compiled `RestrictedSKEndpoint.program_overhead`, including physical input preparation, the actual cutoff/controller, exact/truncated branching, and the final positivity/log operation. `RestrictedSKRuntime.polynomial` and `RestrictedSKFinal.end_to_end` then compiled: these close Theorem 1.1 for the fixed primitive program with a common polynomial constant and the original disorder/color product law. The axiom report is `sk-final-primitive-axioms.txt`.

The separate requested-budget interface is also compiled. `RestrictedSKGraphStart.program_exec` reads the raw MSE budget directly before the controller; no controller for a discarded budget is executed. `RestrictedSKGraphEndpoint.program_overhead` proves output real572 equals the existing `SKPhysicalExecution.execute.value` and proves an actual trace bound of `20000*(N+oldGraphOperations+1)^6`. `RestrictedSKGraphRuntime.polynomial` transfers this to `C*N^C*u^(-C)`. `RestrictedSKGraphFinal.end_to_end` proves the full current Proposition 5.2 SK statement for every `0<u<1`: original-law/color-law mean-square error at most u, and a fixed primitive program realizing that estimator with the uniform operation bound on every finite raw input and random outcome. Its axiom report is `sk-graph-primitive-axioms.txt`.

The raw GraphApprox serializer reuses the real accuracy slot for u and supplies a fixed auxiliary scalar 1 to the unused log-budget slot. This is an explicit ordinary input encoding, not a precomputed output, cache, cutoff, or semantic oracle. The program overwrites the budget register by a charged direct input read and uses that exact u for all controller decisions.

## Independent final-statement reread

I reread `RestrictedSKFinal.end_to_end` and `RestrictedSKGraphFinal.end_to_end` against the frozen `main-12-2-2.tex`, including the model definitions and the explicit original-law remainder. No omitted hypothesis or incorrect statement correspondence was found in these SK endpoints.

- The model is exactly the SK specialization: unordered distinct pairs, `a 2 = 1`, and `N >= 2`. The temperature assumptions are `0 < B < 1` and `0 <= beta <= B`; the weak-field assumption is `abs h <= rho*N^(-1/4)`, including h = 0. The Lean endpoints allow any real rho for which the displayed field assumption holds. This is stronger than the manuscript's fixed positive rho convention and covers it by specialization.
- The disorder hypotheses are a probability law, symmetry, and unit second moment; independence is supplied by the finite product `iidLaw`. No fourth moment or bounded-input hypothesis is added. The probability and mean-square conclusions use the product of that original disorder law and the independent uniform color law.
- The main endpoint quantifies epsilon and delta over the full open unit interval. The separate graph endpoint quantifies the requested u over the full open unit interval, rather than only the smaller budgets produced by LogApprox. Its target is `Model.normalizedPartition`, whose definition is precisely Z divided by `(2*cosh h)^N` and the product of the physical `cosh x_e` factors.
- The polynomial constant is chosen before the disorder law, N, raw record count/order, supplied temperature and field, requested accuracies, disorder values, and color outcomes. Its permitted dependence is only on the fixed model and B,rho. The execution assertion holds for every finite disorder input and every color outcome; no probability qualification is attached to the runtime.
- The remainder `OriginalLawLowerTail.tau` is exactly the manuscript sum of binomial counts times original-law tail probabilities. Its explicit c is `Real.artanh(theta/2)/B`, matching the frozen equation for the lower-tail constants. `OriginalLawLowerTail.rawConstant_pos` proves positivity under the already proved `0 < theta < 1` and `0 < B` conditions. Thus the main statement's explicit tau implements the manuscript's positive tail constant.
- The extra `Fin M ≃ Edge N {2}` argument describes arbitrary enumeration of ordinary raw interaction records. It does not supply computed weights, a cutoff, an estimator, a coefficient array, or an operation counter. Actual charged preparation computes all these internal quantities. The color input is a read-only random tape of raw finite color words; the program reads only addresses needed for its selected candidates and trials. The theorem does not claim to materialize an exponential table of random words at zero cost.
- The probability conclusion is stated for the preexisting mathematical output function, and the second conjunct proves that the fixed actual machine program has exactly that output on every raw input and random tape. Hence the output identification is derived, not an assumed realization contract. The machine model is the specified exact-real register machine with charged finite stack procedures; this remains an operation-count theorem, not a floating-point or bit-complexity claim.

The fresh independent axiom queries for both final endpoints and the sharp local bounds are recorded in `sk-final-independent-axioms.txt`. They contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Sharp local candidate cost

`SKRestrictedCandidateSharpCost.lean` now proves the manuscript's explicit local bound for the actual instructions. `expanded_sharp` retains the squared state dimension and proves `expanded <= 10000*Q^4*M^2`. With `Q=N+2*L+1` and `M=(2*L+1)*2^(2*L)*6^(b+1)`, `candidate_bound` gives

`SKRestrictedCandidateExecution.operationBound <= 360000*(N+2*L+1)^6*16^L*36^b`.

`raw_candidate_bound` includes the actual source preparation of labels, charges, colors, and physical matrices, giving the same expression with the absolute coefficient 361000. This sharpens the earlier coarse polynomial-overhead envelope without changing the program or any existing execution theorem. The separate coefficient-array correspondence and outer aggregation can compose these checked numeric inequalities with the existing actual traces.
