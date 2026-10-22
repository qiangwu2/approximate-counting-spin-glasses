> Historical intermediate assessment. Superseded by REPORT.md, restricted-machine-trust-review.md, and final-verification.json.

# Formal trust and manuscript correspondence review

> **Baseline review.** The inspection below describes the original 192-module project. Subsequent checked additions close the final-output/event measurability gap and the SK capacity comparison through the full logarithmic output and its accuracy guarantee. See [the additions review](additions-review.md) and [the current report](REPORT.md). The whole-program primitive-operation refinement remains incomplete.

Review target: `outputs/lean4-formalization`, read directly from the current package rather than treating old status reports as evidence. Frozen manuscript: `main-12-2-2.tex`, SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`.

## Finding

The current endpoints are **not wrappers that assume the main probabilistic or analytic conclusions**. They establish the accuracy guarantee for explicitly defined outputs under the original iid symmetric unit-second-moment law, together with a polynomial bound on those outputs' defined `operations` fields. The mathematical model, error event, tail term, and uniform quantifier order agree with Theorem 1.1.

An unqualified claim that the literal manuscript algorithms have been verified all the way down to their permitted primitive operations is stronger than the current formal result. The package uses a mathematical value-and-counter model, functions representing caches/arrays, finite sets/lists, and explicit extra structural cost allowances. It has no independent primitive-instruction semantics or refinement theorem connecting every value-producing operation to the asserted structural cost. In addition, its SK implementation uses internal charge capacity `2L`, while the frozen manuscript specifies capacity `L`. It proves exact output equality with the physical estimator, but not a formal projection/refinement relation to the literal capacity-`L` program.

These distinctions do **not** uncover an assumed MSE, graphical mass, lower-tail estimate, or running-time inequality hidden in the final theorem hypotheses. They concern the interpretation and source correspondence of the computation object being proved about.

## Endpoints, assumptions, and quantifiers

`Manuscript/MainTheorem.lean:15` aliases `HigherOrderFinal.canonical_end_to_end`; line 18 aliases `SKFinal.end_to_end`.

The higher-order endpoint (`HigherOrderFinal.lean:169–196`) fixes a nonempty finite active order set, positive active coefficients, orders at least three, a positive temperature cap `B < betaF`, and the field cap `rho`. It then asserts:

1. There exists a positive polynomial constant `C`.
2. For every real probability law `μ`, if it is symmetric and has unit second moment, for every `N ≥ max P`, and every specified `beta,h,epsilon,delta` in the stated ranges, the failure measure is at most `delta + tau`.
3. For every finite physical input array `J`, the defined execution counter is at most `C * N^C * epsilon^(-C) * delta^(-C)`.

The SK endpoint (`SKFinal.lean:152–171`) has the same quantifier order with `a 2 = 1`, `0 < B < 1`, `N ≥ 2`, and a product of the finite coloring law and disorder law. Its cost bound quantifies over **every** color tape and input array, not just almost every one. The existential `C` precedes the law, size, actual temperature, field, tolerance, failure allowance, and input. The algorithm definitions do not accept the disorder law as an argument. Probability concerns each fixed supplied parameter choice; there is no hidden simultaneous event over all real parameters.

Neither endpoint assumes any graph-mass estimate, concentration theorem, MSE inequality, lower-tail inequality, evaluator correctness premise, or cost upper bound. The higher-order noncanonical endpoint accepts chosen lower and upper order bounds, but the public canonical endpoint computes the actual min/max of the active finite set. The extra fact that Lean allows any real `rho` is harmless: the manuscript's positive `rho` is included; a negative `rho` only makes the field-range hypothesis impossible for positive sizes.

The positive raw cutoff constant is supplied separately in `MainTheorem.raw_cutoff_constant_pos`. This is a minor packaging separation from the paper's single `∃ C,c > 0` statement, not an unproved assumption. `OriginalLawLowerTail.rawConstant B theta = artanh(theta/2)/B`; `tau` is literally the sum of `N.choose p` times the original law's tail probability at that constant times `N^((p-1)/2)`.

## Physical model correspondence

`Manuscript/Model.lean` defines physical edges as unordered finite subsets of `Fin N` whose cardinality is in the active order set. An input is a function from exactly that subtype to `ℝ`. It uses the coefficient `beta * a_p * J_e / N^((p-1)/2)`, a sum over Bool-coded ±1 spin configurations, and the literal exponential Hamiltonian plus homogeneous field. The prefactor is `(2*cosh h)^N` times the product of edge coshes. The normalized partition function is the quotient by this positive prefactor. The exact graphical expansion and positive partition-function statements are proved in this file.

`SpinGlass/DisorderModel.lean` defines symmetry by invariance under negation and iid law by the finite product measure. `UnitSecondMoment` includes both integrability of the square and its integral equal to one. This avoids the common formalization error of relying on Lean's default integral value for a nonintegrable function. The model imposes neither a density nor a bounded support nor a higher-moment assumption. Arbitrary atoms and beta zero are supported.

`MixedThreshold.lean` defines the entropy ratio's infimum; `MixedThresholdParameters.lean` defines `betaF` as its square root and proves the SK specialization equals one. The fixed constants are functions of the fixed model and cap. They need not be numerically evaluated from a newly supplied model under the manuscript's fixed-model formulation.

## Downstream proof chain

The following are actual source-level chains, not just names appearing in a README:

- Higher order: final `execute_value` → counted input preparation/support evaluator → `HigherOrderTheorem.accuracy` → `HigherOrderAlgorithm.mse_bound` and `integrable_run_error` → support truncation/physical graphical mass. The final cost is obtained from `HigherOrderExecution.execute_polynomial` and the explicit budget substitution in `LogRuntime`.
- SK: final `execute_value` → `SKPhysicalExecution.execute_value` → `SKGeneratedExecution.estimator_value` → `SKGhostCoefficient.algorithm_eq_physical` → the actual signed graph estimator. `SKTheorem.accuracy` invokes `SKAlgorithm.partition_error_integrable` and `mse_bound`, with the independent finite coloring law. The cost endpoint uses `SKExecutionCost.execute_polynomial` and then `LogRuntime`.
- Both accuracy proofs invoke `LogApprox.probability_of_mse` or its joint-law form. These assembly lemmas are deliberately conditional in their individual signatures, but their MSE and integrability inputs are supplied by the branch proofs. Their lower-tail input is itself discharged by `UniformLowerTail.physical_lower_tail_uniform`.
- The latter is connected to the original-law raw cutoff, sign randomization, negative-moment estimate, and a proved reverse-hypercontractivity chain. The conditional helper names do not represent assumptions exported by the final endpoints.

A read-only elaborated-declaration extractor is provided in `DeclarationClosure.lean`. It traverses proof values **and** types recursively, records local direct dependency edges, and independently lists axioms, unsafe declarations, and unresolved constants for both final endpoints and four corollaries. The extraction successfully ran after the root's fresh build. Its results are recorded below; full local dependency edges and elaborated endpoint signatures are in `declaration-closure.log`.

## Operation counter: exact scope

`SpinGlass/ArithmeticEvaluation.lean:21–40` defines `Computation` as only a real `value` plus natural-number `operations`. Its addition/multiplication primitives increment that count, and recursive list sums/products have proved exact arithmetic counts. `InputPreparation.lean` adds exact-real elementary-function operations and explicitly counts preparation, stored coefficients, and final logarithms. Cutoff-selection loops and the numerical error budgets are represented and bounded rather than assumed.

There is substantial counted implementation work here; calling the entire runtime proof an arbitrary postulated polynomial would be inaccurate. However, `Computation` does not enforce that the value arises from a permissible instruction sequence. Its constructor admits any pair. Parts of the implementation form pairs directly, and structural control allowances are added separately. For example, `InputPreparation.prepareEdges` stores a functional cache using `Function.update` while charging a fixed per-entry index/read/write allowance. `SKGeneratedExecution.estimator` adds `candidateGenerationWork` and `visitControl` to the arithmetic result. `SKChargedTrialExecution.totalTrial` adds outer-trial, exponential-loop, direct-factor, and acceptance-control charges.

The source proves polynomial bounds on these defined counters. It does not prove a separate low-level array realization with a running-step relation, cache lookup/update semantics, and per-step simulation. Such a refinement would directly close the user-requested primitive-operation certification. It is **not** a request for numerical stability, machine-code verification, bit complexity, or bounded-precision arithmetic; the paper explicitly excludes the latter questions.

## SK capacity mismatch

The frozen manuscript (`main-12-2-2.tex:1937–1945`) specifies original-edge exponent indices `0,…,L`, the relation `t^(L+1)=0`, `2L` colors, and `(L+1) * 2^(2L) * 6^(b+1)` registers.

Lean's `SpinGlass.SKCoefficient.Basis b K` (`SKCoefficient.lean:25`) uses `Fin (K+1) × Finset (Fin K) × (Fin b → CappedDegree)`: charge capacity and palette size share one parameter. The actual ghost trial uses palette `K=2L`, hence charge indices through `2L` and `(2L+1) * 2^(2L) * 6^(b+1)` registers. `SKChargedExecution.byOutsideSize` (`:93–98`) then accepts only charge `k≤L`. The larger capacity affects only a constant factor in register count and the stated polynomial bound remains proved for this implementation.

The exact value identity `SKGhostCoefficient.algorithm_eq_physical` is proved (`SKGhostPhysicalEvaluation.lean:54–67`) and is used downstream. It identifies the returned graph polynomial with the physical estimator for every signed input; it is stronger than a numerical sample check. But it does not compare two separately defined capacity-`L` and capacity-`2L` programs. For literal source-program coverage, introduce independent palette/charge-capacity parameters and prove that projection to degrees at most `L` commutes with primitive insertion, addition, multiplication, the finite exponential, direct factors, and extraction, then transfer the program and cost statements. Alternatively, the manuscript could explicitly specify the implemented larger-capacity variant, but changing the frozen source is outside this audit.

## Measurability

The base package proves integrability of actual squared errors and continuity/measurability of the underlying finite graph monomials. Its probability assembly deliberately uses `Measure.real` bounds on arbitrary sets (`ErrorReduction.lean:111` and `CountingConsequences.lean:70`), so the formal bounds are valid even without a separately stated measurable-output lemma. In particular, an upper bound on outer failure measure is meaningful; this is not an unsound use of probability or a missing integrability assumption.

Nevertheless, no explicit measurable-output theorem was located for the **actual final executions**, and no explicit final failure/success-event measurability theorem was located. The manuscript describes ordinary random outputs and probability events, so completing those statements improves exact correspondence. Per the root's subsequent instruction, new proofs have been drafted in `LeanAdditions/OutputMeasurability.lean`, outside the package during frozen verification. They reduce execution values to finite graph sums and prove measurability of both outputs, logarithmic success/failure events, and relative-success events, without law/moment/MSE hypotheses. The addition now elaborates successfully against the fresh baseline (exit 0, no diagnostics), including a canonical higher-output theorem. Integration and the package-wide rerun are owned by the root; this review does not silently treat the standalone checked addition as already imported into the baseline.

## Source map and verifier trust

The independently generated `formal-source-inventory.json` records hashes for every local Lean source. It confirms 192 local modules and 192 modules reachable from `Manuscript.lean`, with no unimported local source. A comment/string-aware scan finds none of `sorry`, `admit`, `axiom`, `native_decide`, `ofReduceBool`, `unsafe`, `implemented_by`, `extern`, `opaque`, custom `elab`, or `macro_rules` in mathematical source code. The only matching metaprogram command is the intended audit's `run_cmd`.

The mathlib checkout reports commit `520045ab14e26149ee970e2e617ca04b09bde5d6`, matching the lake pin; its tracked working tree is clean. Lean is pinned to `leanprover/lean4:v4.32.1`. This is provenance evidence, not a claim to have independently verified the Lean kernel or the compiler binary.

`Audit.lean` checks that selected endpoints exist as theorems and audits axiom closures of every visible declaration in the `Manuscript` and `SpinGlass` namespaces, including private names mapped back to their user namespace. Its only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. Thus ordinary `sorryAx`, custom mathematical axioms, and Lean compiler-reflection axioms are not allowed. In this toolchain, `Lean.ofReduceBool` and `Lean.trustCompiler` are distinct axioms and are outside the whitelist. No source use of them was found.

The verification script recompiles the local module graph, runs that audit, tests public and private `sorry` rejection plus custom-axiom rejection, and hashes local source/configuration before and after. These are good safeguards. They establish less than their success fields claim:

1. A required theorem's **name and theorem kind** are checked, not its exact type or its correspondence to the manuscript.
2. `manuscript_theorem_1_1_proved=true` and `coverage_status=END_TO_END_THEOREM_AND_STATED_COROLLARIES` are assigned after syntactic/kernel checks, without an independently enforced mathematical-correspondence or primitive-refinement predicate.
3. `manuscript-map.json` has 21 useful correspondence entries and correctly documents the `2L` implementation variation. It identifies a PDF hash `840280…7087`, not the frozen TeX hash `edbea…42c6`. The verification script hard-codes the same PDF hash. The fresh run therefore does not automatically certify source correspondence to the present frozen manuscript.
4. Imported mathlib proof code is pinned, not rebuilt or hashed by this script. In Lean 4.32.1, `collectAxioms` obtains imported-module axiom dependencies from metadata generated at module export. A separate traversal of actual imported declaration bodies is useful corroboration and is provided by this review's extractor.
5. The namespace restriction would not audit an unused custom axiom placed outside both project namespaces, and the file enumeration assumes the present flat layout. No such axiom or missed file was found in this tree. These are robustness limitations of the future verifier, not present counterexamples.
6. The Python SK regression script is fingerprinted but not executed by `scripts/verify.py`. Such regressions are useful supplementary tests, not formal proofs, so their absence from this verifier does not undermine a successfully checked theorem.

The 21 map entries cover the named theorem/remark and major intermediate statements across the paper, often via more general statements or a bundle of lemmas. This is a coverage map, not an individually checked equivalence for every formula, pseudocode step, and constant in the TeX source. Particularly, the capacity mismatch above must remain explicit.

## Necessary next work

To claim the requested unrestricted end-to-end result against this frozen manuscript:

1. Integrate the successfully checked final-output/event measurability lemmas and add them to required audit endpoints. Their proof construction and standalone check are complete.
2. Complete a primitive-operation realization/refinement for the counted execution, including functional caches, finite index generation, acceptance predicates, and randomness consumption, or clearly limit the formal claim to the current value-and-counter semantics.
3. Prove the capacity-`L` SK program refinement/equivalence and its cost, or explicitly adopt the implemented variant in the source claim. The physical estimator equality already established should be reused.
4. Bind the source map and verification evidence to the frozen TeX hash, record exact endpoint signatures, and separate `kernel_verification_passed` from the human/machine correspondence assessment. A successful compilation must not by itself write `manuscript_theorem_1_1_proved=true`.
5. Run the full fresh verification after any integrated additions and record the independent endpoint dependency closure.

No new proof of graphical mass, reverse hypercontractivity, support truncation, color-estimator MSE, or the logarithmic error conversion is called for by this review; those are already connected to the final results. No bit-complexity or floating-point theorem is required for the paper's declared model.

## Fresh execution/addition evidence

The root reports the fresh baseline completed at 2026-10-22 07:22:23 UTC: all 192 local modules compiled; the package axiom audit checked 3,582 theorem declarations and 4,729 total declarations; all three negative controls were rejected. This is the fresh baseline, before integration of the new measurability module and metadata changes.

The independent `DeclarationClosure.lean` run then completed with exit 0. It bypasses the imported-module axiom cache for its own traversal, recursively reading the actual types and values. All six closures contained exactly `propext`, `Quot.sound`, and `Classical.choice`; none contained unsafe declarations or unresolved constants. The independently obtained axiom lists agree with `collectAxioms`.

| Endpoint | Total declaration closure | Local declaration closure |
| --- | ---: | ---: |
| `Manuscript.theorem_1_1_higher` | 43,868 | 1,074 |
| `Manuscript.theorem_1_1_sk` | 54,262 | 2,552 |
| `HigherOrderCorollaries.relative_counting` | 43,921 | 1,100 |
| `HigherOrderCorollaries.polynomial_confidence` | 43,952 | 1,107 |
| `SKCorollaries.relative_counting` | 54,320 | 2,583 |
| `SKCorollaries.polynomial_confidence` | 54,324 | 2,589 |

See `declaration-closure-summary.json` for machine-readable counts, axiom lists, and the full log hash. The full log includes every project-local direct dependency edge for each root and the elaborated types of the roots.

`LeanAdditions/OutputMeasurability.lean` completed standalone elaboration with exit 0 and no diagnostics; `output-measurability-check.log` is therefore empty. It establishes actual final-output measurability and explicit measurable error/success events by finite-graph-polynomial identities. No proof-source edits were made to the package by this review; the root is integrating the checked addition after preserving the baseline evidence.
