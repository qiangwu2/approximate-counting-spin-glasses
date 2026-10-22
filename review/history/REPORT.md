# Mathematical audit and Lean verification

Audit target: the current saved manuscript `/Users/qiangwu/Downloads/main-12-2-2.tex`, frozen on 22 October 2026. SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`.

## Assessment

The review found **no substantive mathematical error in the 15 numbered theorem, lemma, and proposition statements or their proofs**. It also checked the counting consequences of Theorem 1.1. This conclusion comes from reading the current source and checking the arguments, assumptions, constants, endpoint cases, and interfaces between sections. It is not inferred merely from an existing Lean build or earlier audit claims.

The existing Lean project contains substantial proofs of the actual mathematical conclusions. Its final accuracy results concern the concrete partition functions and original independent symmetric disorder law. They do not assume the graphical-mass bound, mean-square estimate, negative-moment estimate, lower-tail inequality, or correctness of the graph evaluator. Those inputs are proved in the dependency chain, including reverse hypercontractivity.

**An unconditional end-to-end certification of the full algorithm, including its permitted operation count, is not yet complete.** The remaining distinction is precise. Lean proves polynomial bounds for recursively defined `operations` counters. Some parts of the execution use separate allowances for indexing, finite-set generation, cache access, and control work. There is not yet a full instruction semantics and refinement proof showing that every part of the actual algorithm is implemented within these counters. This is a limitation of formal coverage, not a mathematical counterexample to the paper's complexity proof.

The manuscript has not been changed by this audit.

## Final verification

The fresh integrated rebuild passed for **197 modules**. The axiom audit checked **5,034 declarations**, including **3,717 theorem declarations**. Every local mathematical proof passed with only the permitted standard foundational axioms. All four deliberately invalid fixtures were rejected, including a custom axiom outside the project namespaces. The [final verification record](final-verification.json) contains the exact source and log hashes. The canonical manuscript was checked again and remains byte-for-byte equal to the frozen snapshot.

The only integration failure encountered was an import-order error in the library entry file. It was corrected before this final full rebuild. It did not involve a mathematical proof failure.

## Statements checked

| Result | Checks that determine correctness | Assessment |
| --- | --- | --- |
| Theorem 1.1 | Uniform quantifier order, original disorder assumptions, logarithmic error, tail remainder, arbitrary finite inputs, fixed-parameter dependence of the polynomial exponent | No mathematical defect found. Formal accuracy is proved. Full operation realization remains open. |
| Lemma 2.1 | Independence across interaction indices, zero means, off-diagonal cancellation, independent square-integrable random coefficient arrays | Verified mathematically and connected to Lean endpoints. |
| Proposition 2.2 | Positivity before multiplying bounds, repeated-site correction, entropy comparison, Hölder exponents, tilted external field, finite-sign tail integral, edge-tail rounding | Verified mathematically and connected to Lean endpoints. |
| Lemma 3.1 | Support/degree/boundary relation, external-field powers, feasible edge counts, minimum of the piecewise affine exponent, zero external field | Verified mathematically and connected to Lean endpoints. |
| Proposition 3.2 | First discarded support size, geometric sum, transition to the edge tail, floor conventions | Verified mathematically and connected to Lean endpoints. |
| Proposition 3.3 | Exact subset inversion, coefficient cancellation, single full-support branch, number of spin configurations | Exact value identities proved. Primitive execution refinement is incomplete. |
| Lemma 4.1 | Degree-sequence pairing bound, parity, Gaussian moment calculation, rescaling, constants, empty branching set | Verified mathematically and connected to Lean endpoints. |
| Proposition 4.2 | Branching and edge truncations, overlap handled by a union bound, large-branching edge threshold | Verified mathematically and connected to Lean endpoints. |
| Lemma 4.3 | Unique augmentation, parity at the auxiliary vertex, branching condition, unique path/cycle partition, reverse construction | Verified mathematically and connected to Lean endpoints. |
| Proposition 4.4 | Path and cycle multiplicities, distinct colors, six degree states, exponential factorials, direct edges, original-edge charge, accepted states | Exact graph evaluator identity proved. Current capacity projection is checked separately. Primitive execution refinement is incomplete. |
| Proposition 4.5 | Actual independent coloring law, inclusion probabilities, unbiasedness, second moment, zero mixed truncation/evaluation term | Verified mathematically and connected to Lean endpoints. |
| Lemma 5.1 | Fixed design constants, exponent varying with input, cutoff existence/minimality, one cutoff for every fixed enumeration weight, rounding | Verified. A new wrapper states the current requested-error formulation directly. |
| Proposition 5.2 | Both model branches, all error terms, edge/coloring cutoffs, arbitrary accuracy, exact-enumeration branch | Mean-square conclusion proved. Full operation realization remains open. |
| Lemma 5.3 | Noise convention, reverse-hypercontractive exponents, negative powers, tensor product, Hölder conversion | Verified against the cited source. The Lean dependency chain proves the needed inequality rather than introducing it as an axiom. |
| Proposition 5.4 | Independent sign/magnitude representation including atoms at zero, positivity on the truncation event, original-law moments, Markov and union bounds | Verified mathematically and connected to Lean endpoints. |

The review explicitly included supplied temperature zero, external field zero or negative, the smallest permitted system sizes, empty graph/branching set, cutoff zero, exact-branch boundary, noninteger edge thresholds, and equality in the additional moment threshold. The existence of large fixed constants near the temperature threshold is consistent with the theorem's stated uniformity.

## Independent evidence

- [Analytic review](analytic-review.md) checks Sections 2, 3, and 5 and the main theorem's assumptions and consequences.
- [SK review](sk-review.md) checks Section 4, including the graph decomposition and color-coded evaluator.
- [Formal trust review](formal-trust-review.md) examines actual definitions, endpoint types, dependencies, axioms, and the meaning of the operation counters.
- [Current cutoff correspondence](cutoff-correspondence.md) checks the revised Lemma 5.1 against the Lean statement and constants.
- [Independent review of the additions](additions-review.md) checks all five additions for statement fidelity and circular assumptions.
- [Execution boundary](higher-order-runtime-boundary.md) records the exact higher-order indexing/cache/control obligations, and the narrow instruction-realization theorem that is now proved.
- [Baseline verification](baseline-verification/verification-status.json) records a fresh rebuild of 192 modules and an axiom audit of 4,729 declarations, including 3,582 theorem declarations. All three deliberate invalid-proof controls were rejected. The legacy coverage labels in this preserved baseline are superseded by the qualification above.
- [Independent declaration traversal summary](dependency-summary.json) reads proof bodies and types for both main endpoints and four counting corollaries. It finds only `propext`, `Classical.choice`, and `Quot.sound`, with no unsafe or unresolved declarations in those closures.
- [Exact SK regression](sk-regression-progress.log) reports 1,344 exact rational coefficient comparisons in 672 small scenarios against exhaustive graph enumeration. These tests supplement the arbitrary-size proofs.

## Work added during this audit

Five new modules have been integrated. They give the current-error-budget statement of Lemma 5.1, measurable final outputs and failure/success events, the SK charge-capacity comparison through the full estimator, a complete projected SK logarithmic output with the original failure guarantee, and a concrete fifteen-instruction program for preparing one interaction weight and its log-cosh factor. The SK proofs keep the palette at `2L` while retaining only charges through `L` and running exactly `L` exponential iterations. All new proofs passed individual compilation, independent semantic review, and the final whole-project rebuild and axiom audit. The final verification record identifies the exact integrated sources and hashes.

The source map and verification script now bind to the frozen current TeX file. A successful build no longer automatically declares full manuscript/program certification. Kernel checking, mathematical source correspondence, and operation realization are recorded separately.

## What is needed for full program certification

A completion must define the permitted exact-real instructions, finite index and array operations, and finite-uniform sampling. It must then prove that input preparation, support enumeration, the SK tables and coefficient updates, accepted-state extraction, and the final branch execute with the returned mathematical value and within a polynomial instruction bound. The program must not be allowed to insert an arbitrary input-dependent real value as a cost-free literal. An unused instruction language or a theorem assuming the desired value/cost correspondence would not close this gap.

The mathematical proofs, checked output identities, and current counter bounds can be reused in that refinement. No new analytic assumption, bit-complexity claim, floating-point analysis, or change to the paper's theorem is needed.
