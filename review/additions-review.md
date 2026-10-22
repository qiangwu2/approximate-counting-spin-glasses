> Historical intermediate assessment. Superseded by REPORT.md, restricted-machine-trust-review.md, and final-verification.json.

# Independent semantic review of the additions

Reviewed directly against the frozen `main-12-2-2.tex` (SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`): external `LeanAdditions/SKChargeProjection.lean`, external `LeanAdditions/CurrentCutoff.lean`, external `LeanAdditions/EdgePreparationInstructions.lean`, external `LeanAdditions/SKProjectedOutput.lean`, and the integrated `Manuscript/OutputMeasurability.lean`. This revision reviews the expanded 454-line SK source, SHA-256 `d6570c5c5323ebe704a7dfed786d0981ef9757813cbceea0db10b325e1d5e3b3`. This review does not modify package proof sources.

## Conclusions

| Addition | Semantic conclusion | Remaining boundary |
| --- | --- | --- |
| `CurrentCutoff.lemma_5_1` | Correct direct formulation of the current manuscript lemma, including a common cutoff for every weight `t` and uniformity in the actual exponent | No substantive statement gap found |
| `SKChargeProjection` | Proves the capacity-`L`, palette-`2L`, `L`-iteration recurrence agrees through extraction, trials, and complete candidate/repetition aggregation with the actual counted estimator and analyzed graph estimator | No smaller-array primitive execution/cost refinement |
| `SKProjectedOutput` | Both GraphApprox branches and the complete logarithmic output equal the original actual execution value; the original joint-law accuracy theorem transfers | The new projected output has no primitive operation counter or whole-program execution refinement |
| `EdgePreparationInstructions` | A fixed 15-instruction program realizes both per-edge outputs from only the five raw scalar inputs, with exact executed-step count | Only arithmetic/elementary-function preprocessing for one edge; no addressing, traversal, cache, or whole-algorithm refinement |
| `OutputMeasurability` | Covers the actual canonical higher output and actual SK output, and supplies measurable failure/success/relative-success events | Canonical higher event statements are obtained by the generic event lemmas or definitional specialization; they are not separately named |

The SK proof is a substantive bridge, not a wrapper that assumes its desired conclusion. It closes the previously missing **algebraic** explanation of the different charge capacities and exponential loop lengths. Its comments and final reporting should retain that scope.

## SK charge projection

### Assumptions and proof structure

`projectedEvaluator_low` assumes `L ≤ K` and `ChargesAtLeast 1 f`. The first holds at `K=2L`. The second says that the primitive polynomial has no charge-zero coefficient; it does not assume a projection identity, a recurrence equality, a runtime claim, or a physical-estimator identity.

The latter premise is fully discharged for the actual ghost primitives by `primitives_positive` and `ghost_endpoints_positive` in the final theorem `ghost_capacity_two_mul_eq_manuscript`. The argument is mathematically appropriate:

- An outside cycle has charge equal to its color-set cardinality, at least three.
- A path with a nonempty outside set has charge `|S|-1+charge(a)+charge(c)`. Distinct endpoints cannot both be the unique ghost, so the endpoint contribution is at least one.
- A rooted cycle has `|S|≥2`, hence even a cycle at the ghost has charge `|S|-1≥1`.
- Direct factors are handled separately and may have charge zero. They are multiplied once each, rather than inserted into an exponential. The proof therefore does not make the false assumption that auxiliary direct edges have positive original-edge charge.

`low_mul` proves the key triangularity from `edgeCount_of_basisMul`: a product coefficient of charge at most `L` only reads factor coefficients of charge at most `L`. It preserves the existing color-disjointness and six-state degree rules. There is no assumption of nonnegative real weights; signed and zero weights are covered.

`charges_pow` proves that the nth power of a positive-charge primitive has charge at least n. `term_zero_low` then makes every exponential term with index greater than `L` vanish on the retained coordinates. `expLoop_low_stable` uses that fact to remove the extra iterations of the capacity-`K` evaluator.

Finally, `projectedExpLoop_low` handles truncation after each multiply/scale/add, `projectedDirectLoop_low` handles every direct factor, and `projectedEvaluator_low` composes these results with `SKDenseExecution.evaluator_correct`. The final actual-ghost theorem supplies all positivity requirements from concrete definitions.

### Correspondence to the displayed manuscript recurrence

The manuscript has `2L` color bits, charge exponents `0,…,L`, six degree states per distinguished vertex, and the updates `Y_0=1`, `Y_j=Y_(j-1) Ψ_A / j`, `E_A=Σ_(j=0)^L Y_j`, followed by one factor per direct edge.

`projectedExpLoop L f` initializes both current term and running total to the projected unit. At step `n+1`, it multiplies the old term by the projected primitive, scales by `1/(n+1)`, and projects; it adds this next term to the old sum and projects again. `projectedEvaluator` executes this loop at exactly `L`, then executes all direct factors. The color parameter remains `K`, so specializing to `K=2L` does not accidentally reduce the palette to `L` colors. This matches the manuscript's mathematical recurrence.

`RetainedBasis (b+1) L (2L)` has exactly `(L+1) * 4^L * 6^(b+1)` entries, as proved in `manuscript_array_size`. `restrict`/`expand` identify those coordinates with the zero-padded large array; `retainedMul_restrict` proves multiplication respects this quotient. Thus the introduction of the smaller coordinate type is meaningful, not merely a relabeling of the larger cardinality.

The generic actual-ghost theorem permits arbitrary finite distinguished sets of `Option V`. Its algebraic assertion remains valid even outside the physical specialization. For the manuscript interpretation, take the existing `distinguished A`, which includes `none`; that ensures the ghost is not an outside vertex. This is an intended specialization, not a missing hypothesis in the algebraic equality itself.

### Extraction and actual estimator output: now closed

The expanded source adds the complete chain missing in the first review:

- `projectedGhostEvaluate` specializes the projected algebra to `distinguished A`, the original field/weights, and the actual outside coloring.
- `projectedByOutsideSize` performs accepted-state, edge-charge, and color-size extraction. `projectedByOutsideSize_eq` proves equality to the existing `SKGhostCoefficient.byOutsideSize` by summing the coefficientwise equality only where `k≤L`.
- `projectedTrial` applies the actual inverse-color-inclusion factors. `projectedTrial_eq` equates it to the **value of the actual counted** `SKGeneratedExecution.trial` for every field, color outcome, and signed edge array.
- `projectedAlgorithm` averages trials and sums over all actual candidate sets and repetitions. `projectedAlgorithm_eq` identifies it with the existing ghost algorithm, and `projectedAlgorithm_eq_generated` identifies it with the **value of the actual counted** `SKGeneratedExecution.estimator`.
- `projectedAlgorithm_eq_disorder` identifies the result with the analyzed finite graph estimator on pair edges, with the only substantive side condition `L>0` already guaranteed by the intended cutoff regime.

All these statements prove their equality conclusions from the prior algebraic bridge and the existing evaluator correctness theorems. None assumes trial equivalence, estimator equivalence, or the desired final answer. The new definitions preserve the original accepted states, color correction, repetition indexing, and candidate enumeration. In particular, the expansion closes the estimator bridge; the first version's residual assessment that extraction/trial/aggregation equalities were absent is now obsolete.

`projectedAlgorithm_eq_disorder` uses total functions on finite subsets with a pair-edge domain restriction in the estimator. The actual top-level physical input is the subtype `Edge N {2}`. This is not a model discrepancy: `projectedAlgorithm_eq_generated` applies to an arbitrary weight lookup and can be specialized to the existing `inputWeight`/prepared physical weights, while the existing `algorithm_eq_physical` supplies the typed physical identity. The generic total-function theorem should not itself be mislabeled as already displaying the subtype-based final execution signature.

### Complete projected output and original-law accuracy: now closed

The new `SKProjectedOutput.lean` closes the final wrapper connection. Its `evaluate` uses the same actual cutoff control and color-tape transport as `SKPhysicalExecution.evaluate`. It leaves the exact fallback unchanged and replaces only the truncated branch by the independently defined projected estimator. `evaluate_prepared` proves equality of both branches when given the actual `prepareInput` result; this specialization correctly ties its explicit field `h` to the cached mean `tanh h`. It does not assume a relationship between an arbitrary prepared input and an unrelated field.

`graphApprox_eq_execute` identifies the resulting value on the actual subtype-based physical input array with `SKPhysicalExecution.execute.value`. Thus the total-function versus physical-subtype interface noted above is also bridged at the actual GraphApprox boundary.

The complete `output` definition computes the same numerical accuracy budget, prepares the same input, uses the same saved color-tape cast, and applies `SpinGlass.logOutput` to the projected correction. That final function includes both the positivity test and the nonpositive-correction fallback. `output_eq_execute` proves pointwise equality to `SKFinal.execute.value` for every physical disorder input and every saved color tape. Its only proof parameters are positivity of the fixed budget constant and of delta, needed by the existing type transport; no output equality, evaluator correctness, MSE, or probability estimate is a premise.

The new `accuracy` theorem then transfers the exact original joint-law failure bound `delta + tau` by this proved equality. Its hypotheses are the standard symmetric unit-second-moment law, SK model, temperature/field ranges, size bound, and accuracy/failure ranges. The final event is explicitly written using the new projected output. It therefore establishes the projected program's accuracy, rather than merely asserting accuracy of a renamed old function.

`Manuscript.theorem_1_1_sk` still aliases the unchanged `SKFinal.end_to_end`, and the canonical source remains unchanged. The new leaf theorem depends on that original execution and accuracy result in the correct direction: independently prove value equivalence, then transport the verified probability statement. It is not necessary to rewrite the original theorem to make this extension valid. The prior review's residual claim that a projected LogApprox equality was missing is now obsolete.

The value, extraction, estimator, physical-input, full-output, and original-law accuracy boundaries are all closed by the reviewed chain. The remaining qualification is the realization and cost of the whole primitive program, including the small-array allocation/schedule. The new output deliberately returns a real value without attaching an operation counter; output equality alone does not transfer a runtime bound to a different implementation.

At the implementation level, `projectedEvaluator` still uses `Coefficients b K`, i.e. the larger function type, with zero padding. `retainedMul` is defined by expanding to that larger type, multiplying there, and restricting. No full exponential/direct evaluator over `RetainedCoefficients` is defined, and no operation counter or primitive instruction semantics is supplied for it. The cardinality theorem alone does not establish that the program physically allocates only the smaller array or performs only smaller-array loops. The newly added extraction/trial/estimator equalities do not change this runtime boundary.

Accordingly, the comment on `restrict` saying “physically allocated” is stronger than this definition establishes. “Read the low-charge coordinates” would describe its proved content precisely. The file's header already correctly excludes a machine schedule/allocation claim.

For a literal small-array runtime result, define multiplication by iterating only pairs in `RetainedBasis`, prove it agrees with `retainedMul`, define the full retained evaluator and its primitive schedule/counter, and transfer the existing value and polynomial bounds. The broader functional-cache/primitive-operation refinement issue remains independent of this algebraic projection addition.

## Current cutoff lemma

No circular premise or weakened quantifier was found. The assumptions are only the intended design constraints: positive lower exponent, `A≥1`, positive exponential remainder constant, and `CΛ≥1`. They are fixed before the variable size, actual exponent, and requested error budget. In particular:

- The constants `gamma`, `nu`, `sizeThreshold`, and `workConstant` depend on the fixed lower exponent `kapMin`, not the actual possibly field- and size-dependent `kap`.
- The theorem quantifies over every `kap≥kapMin`.
- It selects `∃ k` **before** `∀ t≥1`, so the same cutoff works for every fixed enumeration weight.
- The work exponent is the explicit `workConstant kapMin A t`, independent of `N`, `kap`, and `u`.
- The hypothesis `CΛ exp(-nu N)<u` is exactly the truncation window in the manuscript; positive `u` is an explicit redundant consequence, not a restriction on the claimed regime.
- It proves the requested error inequality `exp(-phi(...,k+1))≤u/CΛ`, not just an existence statement in an unrelated logarithmic parameter.
- It identifies the actual counted search's return as `some(k+1)` and bounds that search's counter by `10N+3`.

The proof derives `Λ=log(CΛ/u)` and `0<Λ<nu N` from the window, obtains the finite first crossing, sets `k=m-1`, and transports both the error and weighted-binomial estimates back to `u`. The integer shift is handled by the proved `m≥1` and `m≤floor(gamma N)`, so it gives `0≤k<floor(gamma N)` with no off-by-one mismatch.

The definitions also match the constants displayed in the frozen manuscript: gamma is the same minimum, `N0` is the same ceiling, nu differs only in the order of the nested minimum, and the work constant is the algebraically identical sum `1/kapMin + log(e*t*A)/(kapMin*log(1/(A*gamma)))`.

The theorem is a direct current-source formulation built from existing fully proved search and cost lemmas. It need not be on the dependency path of the old final endpoints to be valid coverage of the present lemma; those endpoints already use the same certified cutoff machinery. Nothing in this addition assumes the error/cost conclusions it claims.

## Integrated output measurability

`higher_canonical_execute_measurable` directly names `HigherOrderFinal.canonicalExecute`, which is the output used by `Manuscript.theorem_1_1_higher`. It derives the min-order positivity and budget-constant positivity from the standard finite-model hypotheses. The additional `N>0` premise follows from the public endpoint's `N≥max P` and its active orders being at least three. No law, integrability, moment, MSE, or runtime hypothesis is added.

The named higher failure/success/relative-success theorems currently use the general `HigherOrderFinal.execute` with explicit min/max order parameters. For the canonical output, there are two equally direct derivations:

1. Specialize those statements to `pmax=P.max' hP` and `pmin=P.min' hP`, then unfold `canonicalExecute`.
2. Apply `logarithmic_failure_measurable`, `logarithmic_success_measurable`, or `relative_success_measurable` directly to `higher_canonical_execute_measurable` and `partition_measurable`.

Therefore canonical event measurability is substantively covered. A separately named `higher_canonical_failure_measurable` (and success variants) would improve API/audit discoverability but requires no new mathematical ingredient. It would be inaccurate to describe the present file as still missing canonical-output measurability.

The SK output theorem uses the same joint finite-color/physical-disorder type as the endpoint and accepts the positive budget proofs carried by the actual `SKFinal.execute`. Its named event lemmas directly name that execution. The original-law assumptions are unnecessary for measurability, correctly absent, and can subsequently be used to interpret the already proved event bounds as ordinary probability statements.

## Per-edge primitive instruction realization

`EdgePreparationInstructions` supplies a real operational model for one specific part of the computation, rather than merely pairing an arbitrary output with a chosen cost.

The program is a parameter-free, fixed list `edgeProgram` of exactly fifteen instructions. Its operand constructors are only an input selector, one of two fixed constants (`-1` and `2`), or one of fifteen register addresses. It has no arbitrary-real literal constructor. `edgeInputs` supplies only `N`, `p`, `a`, `beta`, and `J`; it does not smuggle the target tanh/log-cosh output or an intermediate nonlinear computation into the environment.

The fifteen steps are an explicit realization of the old `prepareEdge` expression:

1. Five steps form the denominator `exp(log N * ((p-1)/2))`.
2. Three steps form the shared coupling `beta*a*J/denominator`.
3. One step computes its tanh.
4. Six steps form `log((exp x + exp(-x))/2)`.

Every register read by this fixed program follows its defining write. `edgeProgram_weight` and `edgeProgram_logCosh` hold for **every** initial register state, demonstrating that no initialized output is required. These equalities are proved by reduction against the existing expressions; reduction is appropriate for a fixed expression compiler and is not a circular output hypothesis.

`Executes` has exactly the empty-program/zero-count rule and the one-instruction/one-increment rule. Its successor rule applies the explicitly defined semantic `step` before executing the rest. There is no rule that accepts an arbitrary result, arbitrary operation counter, or desired cost bound. `run_executes` follows by induction on the instruction list. The final theorem chooses the semantic run as its witness and proves fifteen executed instructions, both output equalities, and equality with the existing per-edge primitive budget. The five raw inputs are separated from writable registers.

`prepareEdge_physical` additionally establishes the literal normalized-coupling tanh and log-cosh formulas when `N>0`. The more general `prepareEdge_realized` permits `N=0` only because it equates two totalized Lean expressions; the physical theorem appropriately restricts to positive sizes. No new mathematical inconsistency or circular assumption was found.

This is a valid narrow refinement under an exact-real unit-cost model for addition, multiplication, division, exp, log, and tanh. Operand reads, destination writes, address selection, and instruction dispatch are components of the semantic instruction step and are **not separately charged**. `Function.update` still represents the register store mathematically. The file explicitly states this limit; it does not claim a low-level implementation of arbitrary functional caches.

It does not refine input-edge enumeration, the outer preparation traversal and its extra overhead, field preparation, shared array/cache realization, SupportSum, SK recurrences, cutoff search, random draws, or the final logarithmic wrapper. In particular, a correct fifteen-step per-edge program cannot justify labeling the entire `Computation.operations` bound as an established primitive-operation runtime theorem. It demonstrates a sound pattern that can be extended to those remaining components.

## Recommended acceptance wording

Accept the cutoff and measurability additions as completing their stated mathematical coverage. Accept the expanded SKChargeProjection as proving the full projected estimator has exactly the value of the existing counted estimator, including extraction, color correction, repetitions, and candidates. Accept SKProjectedOutput as closing both algorithm branches, the actual typed physical-input boundary, the complete logarithmic output identity, and the original-law accuracy transfer. Accept EdgePreparationInstructions as a genuine fixed-program realization of the fifteen arithmetic/elementary-function instructions used for one prepared edge. These additions do not prove whole-algorithm primitive runtime or small-array allocation refinement, and reporting should preserve that distinction. There is no remaining projected-output or projected-accuracy gap in the reviewed chain.

## Reviewed source inventory

- `SKChargeProjection.lean`: `d6570c5c5323ebe704a7dfed786d0981ef9757813cbceea0db10b325e1d5e3b3`
- `CurrentCutoff.lean`: `7672779c0706e26c29a7b73690b0c5aeb2b9f85319834be4cff91751419396dd`
- `EdgePreparationInstructions.lean`: `601da269f39fb3ba420a32a1367afdbafaf42b3660a3f2b4df7e48a4479e39af`
- Integrated `OutputMeasurability.lean`: `327345a8a0f2a7568b25ad1c24dfb083dbc82a3e37d7f2f4155e2f9c80304db8`
- `SKProjectedOutput.lean`: `1c3daf98fb2cf84886238658b227b4eb278684716427fb17280d4aa263ed92a3`
