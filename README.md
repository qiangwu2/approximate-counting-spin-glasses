# Approximate counting for mixed p-spin glasses — Lean formalization

This project formalizes the current manuscript's mathematical results and realizes both main algorithms as fixed programs in its exact-real operation model. The program proofs start from raw coupling records and, for SK, raw random colors. They prove the returned value, the original-law error guarantee, and a uniform polynomial bound on the instructions actually executed. No evaluator-correctness, tail estimate, or runtime contract is assumed at the final endpoints.

The final frozen rebuild passed for **375 modules, 9,700 theorem declarations, and 12,943 total declarations**. All four invalid-proof controls were rejected. The independent dependency audit found only Lean's standard axioms, with no unsafe or missing dependencies. Exact results and source hashes are in `verification-status.json`.

The reviewed manuscript is bundled as `paper/main-12-2-2.tex`, SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`. It is an unchanged snapshot of the user's saved manuscript. `manuscript-map.json` maps its statements to the formal declarations. `review/REPORT.md` records the mathematical review and final verification.

## Main endpoints

| Manuscript result | Formal theorem |
| --- | --- |
| Theorem 1.1, higher-order mixtures | `Manuscript.theorem_1_1_higher_primitive` |
| Theorem 1.1, SK | `Manuscript.theorem_1_1_sk_primitive` |
| Proposition 5.2, higher-order mean-square approximation | `Manuscript.proposition_5_2_higher_primitive` |
| Proposition 5.2, SK mean-square approximation | `Manuscript.proposition_5_2_sk_primitive` |

The definitions are in `Manuscript/PrimitiveTheorem.lean`. Its four aliases point to `RestrictedHigherFinal`, `RestrictedSKFinal`, `RestrictedHigherGraphFinal`, and `RestrictedSKGraphFinal`. Their constants are quantified before the disorder law, system size, actual temperature, external field, requested tolerances, raw input, and random outcome. The algorithms do not take the disorder law or its tail remainder as input.

The dependency chains prove the graph expansion, graphical-mass and truncation estimates, exact graph evaluators, independent-color estimator bounds, reverse hypercontractivity, original-law lower tails, and logarithmic error conversion. Counting corollaries give relative approximation and prescribed inverse-polynomial confidence, including equality at the stated moment threshold. The same outputs are realized by the primitive endpoints.

The hypotheses are those of the mathematical statements. In particular, accuracy is averaged over the original independent symmetric unit-second-moment disorder law and internal randomness. Runtime and output realization hold for every finite real coupling input and every permitted random outcome. This does not assert accuracy on every deterministic coupling array.

## Implemented operation model

`RestrictedMachine` specifies exact real and integer arithmetic, comparisons, register and memory operations, and raw-input reads. `RestrictedRecursiveMachine` adds a fixed finite procedure table with charged stack operations. The programs contain no arbitrary input-dependent real literals or uncharged algorithm callbacks. `RestrictedDeterminism` proves uniqueness of the execution result and charged count.

The proved programs include physical weight preparation, cutoff search, subset and spin generation, the SK path/cycle tables, degree-state coefficient operations, independent-color trial loops, inclusion-probability correction, accepted-coefficient extraction, and the final logarithmic output. Values cached or generated inside these stages are proved equal to the corresponding mathematical definitions.

The SK implementation allocates charge capacity `2L` internally and retains output charges at most `L`, using `2L` colors. The manuscript recurrence allocates capacity `L`. `SKChargeProjection` and `SKProjectedOutput` prove equality of the retained coefficients and complete output. The larger internal allocation still satisfies the manuscript's operation bounds. It is a proved equivalent implementation, not a claim that the two memory layouts are identical.

This is certification in the paper's ideal exact-real operation model. Native Lean execution time, floating-point error, and bit complexity are not the claims of the manuscript or this project.

## Reproduce the verification

Lean is pinned to `leanprover/lean4:v4.32.1` and mathlib to `520045ab14e26149ee970e2e617ca04b09bde5d6`. All dependency revisions are in `lake-manifest.json`.

With those dependencies available, run:

```sh
python3 scripts/verify.py
python3 checks/check_sk.py
```

For a fresh checkout, install the pinned Lean toolchain and obtain the pinned Lake dependencies and mathlib cache first. The archive excludes downloaded dependencies and build caches. The current working checkout shares a local dependency cache.

The verifier recompiles every local proof module in dependency order. It requires the four primitive endpoints, checks complete import coverage, audits every local declaration including private declarations, and independently traverses the bodies and types of the four endpoints and four counting corollaries. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. Four deliberately invalid fixtures test rejection of custom axioms and public/private placeholders, including an axiom outside the project namespaces. Source and configuration hashes must remain unchanged throughout verification.

The exact-rational SK regression compares coefficients against exhaustive graph enumeration in 672 finite scenarios, making 1,344 comparisons. It covers both charge capacities, signed and zero weights, and color collisions. It supplements the arbitrary-size Lean proofs.

## Provenance and review

The `SpinGlass/` modules retain relevant general finite algebra and analytic proofs from the user's earlier formalization. `source-provenance.json` records their origin. The current conclusions concern the mixed-model manuscript's literal partition functions and physical normalization. No earlier pure-model conclusion is substituted for the current theorem.

`current-audit-additions.json` records the current additions. The source map and mathematical review are separate from kernel verification. Compilation checks the formal statements; the source review checks that those statements represent the manuscript.
