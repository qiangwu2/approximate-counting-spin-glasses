# Mathematical audit and end-to-end Lean formalization

The target is the saved manuscript `/Users/qiangwu/Downloads/main-12-2-2.tex`, SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`. The manuscript was not changed by this audit.

## Assessment

The mathematical review found no substantive error in the 15 numbered theorem, lemma, and proposition statements or their proofs. It also checked the counting consequences of Theorem 1.1. The review covered hypotheses, constants, rounding, endpoint cases, and the interfaces between sections. The source-to-formal correspondence is recorded declaration by declaration in `manuscript-map.json`.

The formal development now connects the mathematical estimates to fixed primitive programs for both model classes. The programs start with raw coupling records and raw random colors. Their proved outputs satisfy the original-law accuracy guarantees. Their actual instruction traces satisfy uniform polynomial bounds. The analytical estimates, graph evaluator identities, and runtime realization are conclusions in the dependency chains, not extra premises of the final theorems.

**The final frozen verification passed.** It rebuilt 375 modules, 9,700 theorem declarations, and 12,943 total declarations. All 90 mapped declaration pointers were checked. All four deliberately invalid proof fixtures were rejected. The independent traversal of eight theorem dependency closures found no unsafe or missing dependencies and only the permitted standard axioms. Source and configuration hashes were unchanged throughout the run. See `final-verification.json` and the accompanying build and audit logs.

## End-to-end endpoints

- `Manuscript.theorem_1_1_higher_primitive` and `Manuscript.theorem_1_1_sk_primitive` give the two branches of Theorem 1.1.
- `Manuscript.proposition_5_2_higher_primitive` and `Manuscript.proposition_5_2_sk_primitive` give the separate mean-square algorithms for every requested tolerance 0<u<1.
- The implementation proofs include input preparation, cutoff search, subset and spin generation, path/cycle tables, coefficient updates, degree acceptance, probability correction, trial averaging, and the final output.
- Execution is deterministic given the raw input and random tape. Its charged cost cannot be selected from alternative executions.

The program and fixed model constants precede the varying inputs in the theorem quantifiers. Runtime holds for every finite real coupling input and every permitted color outcome. Accuracy is a probability statement under the manuscript's original independent symmetric unit-second-moment disorder law. It is not asserted for every deterministic coupling array.

The SK implementation uses internal charge capacity 2L and extracts charges at most L. The manuscript uses capacity L with the same 2L colors. Proved coefficient projection and complete-output equality connect the two implementations, and the actual larger allocation satisfies the displayed cost bounds.

## Statements checked

| Result | Checks that determine correctness | Assessment |
| --- | --- | --- |
| Theorem 1.1 | Uniform quantifier order, original disorder assumptions, logarithmic error, tail remainder, arbitrary finite inputs, fixed-parameter dependence of the polynomial exponent | No mathematical defect found. Actual primitive-program output, accuracy, and polynomial runtime proved. |
| Lemma 2.1 | Independence across interaction indices, zero means, off-diagonal cancellation, independent square-integrable random coefficient arrays | Verified mathematically and connected to Lean endpoints. |
| Proposition 2.2 | Positivity before multiplying bounds, repeated-site correction, entropy comparison, Hölder exponents, tilted external field, finite-sign tail integral, edge-tail rounding | Verified mathematically and connected to Lean endpoints. |
| Lemma 3.1 | Support/degree/boundary relation, external-field powers, feasible edge counts, minimum of the piecewise affine exponent, zero external field | Verified mathematically and connected to Lean endpoints. |
| Proposition 3.2 | First discarded support size, geometric sum, transition to the edge tail, floor conventions | Verified mathematically and connected to Lean endpoints. |
| Proposition 3.3 | Exact subset inversion, coefficient cancellation, single full-support branch, number of spin configurations | Exact value identities, generated support/spin enumeration, and the displayed primitive runtime bound proved. |
| Lemma 4.1 | Degree-sequence pairing bound, parity, Gaussian moment calculation, rescaling, constants, empty branching set | Verified mathematically and connected to Lean endpoints. |
| Proposition 4.2 | Branching and edge truncations, overlap handled by a union bound, large-branching edge threshold | Verified mathematically and connected to Lean endpoints. |
| Lemma 4.3 | Unique augmentation, parity at the auxiliary vertex, branching condition, unique path/cycle partition, reverse construction | Verified mathematically and connected to Lean endpoints. |
| Proposition 4.4 | Path and cycle multiplicities, distinct colors, six degree states, exponential factorials, direct edges, original-edge charge, accepted states | Exact graph evaluator identity, actual table/coefficient execution, and sharp local runtime bound proved. Charge-capacity projection is explicit. |
| Proposition 4.5 | Actual independent coloring law, inclusion probabilities, unbiasedness, second moment, zero mixed truncation/evaluation term | Verified mathematically and connected to Lean endpoints. |
| Lemma 5.1 | Fixed design constants, exponent varying with input, cutoff existence/minimality, one cutoff for every fixed enumeration weight, rounding | Verified. A new wrapper states the current requested-error formulation directly. |
| Proposition 5.2 | Both model branches, all error terms, edge/coloring cutoffs, arbitrary accuracy, exact-enumeration branch | Actual raw-u primitive algorithms, original-law mean-square error, and polynomial runtime proved for all 0<u<1. |
| Lemma 5.3 | Noise convention, reverse-hypercontractive exponents, negative powers, tensor product, Hölder conversion | Verified against the cited source. The Lean dependency chain proves the needed inequality rather than introducing it as an axiom. |
| Proposition 5.4 | Independent sign/magnitude representation including atoms at zero, positivity on the truncation event, original-law moments, Markov and union bounds | Verified mathematically and connected to Lean endpoints. |

The review explicitly included supplied temperature zero, external field zero or negative, the smallest permitted system sizes, empty graph/branching set, cutoff zero, exact-branch boundary, noninteger edge thresholds, and equality in the additional moment threshold. The existence of large fixed constants near the temperature threshold is consistent with the theorem's stated uniformity.

## Verification and scope

The formal operation model is the manuscript's ideal exact-real model. The results do not claim native Lean execution-time bounds, floating-point stability, or bit complexity. The only permitted foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. No custom analytic assumptions or unproved program contracts are used to close the main endpoints.

The first frozen rebuild exposed an unfinished natural-number arithmetic step in the ceiling routine's cost proof. An explicit arithmetic tactic closed that equality without changing the statement, program, or bound. A new full verification run uses the repaired source.

The final verifier recompiles all local modules, checks every source-map declaration, audits every local declaration including private declarations, and independently traverses proof bodies and types for the four primitive endpoints and four counting corollaries. Deliberately invalid public/private placeholders and custom axioms test the audit's rejection behavior. Source and configuration hashes are fixed throughout the run.

An additional exact-rational regression passed all 1,344 coefficient comparisons in 672 finite SK scenarios against exhaustive graph enumeration. These checks include both charge capacities, signed and zero weights, and color collisions. They supplement the general proofs.

The analytic and SK review reports document the manual mathematical audit. The later restricted-machine reports document closure of the implementation obligations. Earlier reports retained under `review/history/` describe historical intermediate coverage and are superseded by this report and the final verification record.
