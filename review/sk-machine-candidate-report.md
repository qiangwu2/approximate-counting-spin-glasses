# SK restricted-machine candidate and relabeling audit

Status: the complete candidate/trial body is compiled and connected to the existing generated trial. Outer aggregation and the final public runtime theorem are separate integration work; this report does not claim those endpoints are finished.

## Exact result now proved

`Manuscript.SKRawCandidate.encoded_program_exec` executes the fixed program `SKRawCandidate.program` on the ordinary serialized physical input and serialized coloring tape. Its hypotheses specify the actual prepared physical cache, a valid candidate mask and repetition index, the positive truncation level, and disjoint label-array addresses. Its output is exactly `SKGeneratedExecution.trial L A (χ A r) (tanh h) inputWeight`, in real register 310.

The program constructs the ascending branch/complement labels, endpoint charges and outside colors; computes all three weight matrices by looking up the physical input; constructs all root tables; constructs the primitive polynomial; computes the basis-pair metadata; constructs every direct-factor array; executes the exponential and direct-factor product; and computes acceptance and color correction during coefficient extraction. No graph sum, primitive table, multiplication schedule, desired output equality, or MSE equality is supplied as an input to this theorem.

`SKRawCandidateCost.operationBound_le` bounds its actual restricted trace by

`7000 * (N + oldGeneratedTrial.operations + 1)^5`.

The bound follows from the executed loops, generated metadata, actual cache operations, and a proved lower bound on the existing trial cost. It is a real-arithmetic RAM operation bound, including addressed reads/writes and control operations, not a bit-complexity statement.

`SKCandidateContract.realized` instantiates the outer-loop candidate contract with this actual program. Its invariant contains the physical cache, fixed control values, the raw tape origin, and the generated safe layout. It does not assume a candidate-realization oracle. Its uniform cost per candidate is bounded using the existing average's operation count. `SKCandidateContractSemantics.average_encoded` connects the actual repeated-trial sum and division directly to `SKGeneratedExecution.average`.

## Independent semantic audit of relabeling

No mathematical defect, vacuous premise, or mismatched input was found in the inspected chain.

1. `SKBranchReindex.coordinate` preserves charged degree and color set and only pulls back the capped branch-degree function. `pull_mul` proves preservation of the actual coefficient convolution by finite-sum equivalence. The resulting ring equivalence therefore preserves all ring operations; it does not redefine multiplication to make the comparison tautological.
2. `SKPairReindex` handles the non-order-preserving branch bijection by explicitly reordering each unordered pair and constructing the inverse bijection. Its sum/product comparison requires symmetry of pair values. Thus the `a<c` selection in both label orders is justified rather than implicitly assumed invariant.
3. `SKPathSymmetry` supplies the needed between-path symmetry by reversing colorful chains and proving their undirected edge sets agree. Its branch/outside injectivity and separation hypotheses are discharged in `SKCanonicalLabels.canonical_trial` by the canonical branch enumeration and the outside subtype. The executable ascending lists independently prove exactly those ranges and injectivity properties.
4. `SKPrimitiveReindex.primitives_map` treats outside cycles, paths between different branch vertices, and returns separately. Endpoint charges are composed with the branch equivalence. Returns retain the charge `|S|-1+2q(a)` and their factor 1/2. The direct factor retains charge zero if either endpoint has charge zero, and otherwise charge one; it is not assigned the sum of endpoint charges.
5. `SKOutsideReindex` starts at the actual path-table recurrence. It reindexes the intermediate-vertex sum by an equivalence and proves the corresponding cycle-root delta-function identity. It consequently covers both path/return closures and outside-cycle closures, without requiring a global injectivity assumption on the coloring.
6. `SKCanonicalLabels` constructs genuine bijections from the proved ranges of the executable branch and outside labels. The appended executable ghost is mapped to the canonical `none` vertex. The physical charge is one and the ghost charge zero in both coordinate systems.
7. Acceptance is invariant under the same branch bijection: the unique ghost permits capped degrees 0, 2 or 4, and each physical branch vertex requires state 4. The extraction's charged-degree cutoff and outside color cardinality are unchanged by relabeling.
8. The augmented color at the ghost is arbitrary but is never read by an outside table, because the outside subtype excludes the ghost. The source program reads each outside color at its original physical vertex index, not its compact outside-list index. The serialized tape theorem matches this exact address.

## Algebra and operational checks

- The basis coordinate encoding has explicit charge/color/degree radices. Metadata computes the charge sum, bit overlap, union and capped degree addition by restricted natural instructions. Metadata generation is executed once for all basis pairs; no precomputed semantic schedule appears in the complete candidate theorem.
- Numeric basis-pair order is connected to the complete pair enumeration. Multiplication accumulates every compatible pair once. Dense output initialization is executed, and source/output disjointness follows from the four coefficient-array blocks.
- Exponential initialization sets both power and sum to the multiplicative identity. Each iteration multiplies the previous power by the primitive polynomial, divides by the next integer, and adds it to the sum. The actual iteration count is the palette/capacity `K`.
- The direct bank scans all `b²` ordered keys. Only `a<c` produces a nonzero edge factor; all other keys produce the zero polynomial, so multiplication by `1+factor` is harmless there. `SKDirectBankSemantics.loop_eq` proves equality with the existing filtered direct list.
- The candidate capacity is `K=2L` and extraction retains charge at most `L`. This is the existing exact charged evaluator. The separate retained-charge projection formalization is what connects it to the manuscript's capacity-L algebra; the operational candidate theorem itself does not claim immediate capacity-L storage.
- All root tables precede the coefficient arrays; direct factors follow the four working coefficient blocks. The actual execution preserves the physical real cache, the natural-memory prefix containing physical edge masks and the outer candidate schedule, and the required persistent registers. Candidate programs preserve every real register at least 500; outer programs may use designated aggregation scratch separately.

## Kernel checks

Standalone compilations of all new candidate modules succeeded. Searches of the inspected source found no `sorry`, declared `axiom`, or `native_decide`. The axiom reports for the complete raw-candidate theorem, its runtime envelope, the complete source-array candidate theorem, and the backend theorem contain only `propext`, `Classical.choice`, and `Quot.sound`. The final callback, average identity, and reindex-chain axiom reports also contain exactly those three standard axioms. The captured reports are `sk-machine-axioms.log` and `sk-reindex-axioms.log` in this audit directory.

Canonical TeX was not edited by this work.

## Complete colorful coefficient output (Proposition 4.4)

The new `SKCandidateCoefficientOutput.backend_exec` and `candidate_exec` strengthen the existing actual-program result with its complete output coefficient array. The direct-bank generation, metadata generation, combination and corrected extraction are unchanged; the proof records the fact that corrected extraction preserves the coefficient memory. No evaluated coefficient is added to the input contract.

`SKColorfulCoefficientOutput.coefficient_original` extends the canonical original-graph coefficient identity to the branch and outside enumerations used by the machine. It uses the independently proved branch-coordinate pullback, outside-table reindexing, acceptance invariance, and original augmented-graph bijection. Neither the ordering of branch labels nor an injective coloring is assumed. Color collisions are handled by the evaluator itself.

`SKColorfulCoefficientOutput.end_to_end` gives one actual candidate execution for arbitrary real external field and edge weights, and proves simultaneously for every charged coordinate `k` and every color set `S` that its accepted-state RAM readout is the exact original graph sum `f_A^χ(k,S)`. In particular it covers every requested `k ≤ L`, with palette/capacity `2L`. Its actual trace obeys the sharp local bound

`360000 (N+2L+1)^6 16^L 36^|A|`.

The theorem's source conditions specify branch/outside labels, the coloring, endpoint charges and edge-weight matrices, together with their memory layout. These are input representation conditions, not output or realization assumptions. Every path cache, primitive polynomial, direct factor, algebra record and coefficient array is derived by the actual fixed machine program.

The representation of an output sum is explicit: `readout_three` proves that each `f_A^χ(k,S)` is the sum of exactly three addressed entries, for ghost degree states 0, 2 and 4 and degree state 4 at every ordinary branch vertex. The theorem returns the complete coefficient array with this constant-size readout; it does not claim that an additional separate array of all scalar `f` values has been materialized. The previously proved capacity projection identifies the retained coordinates with the manuscript's capacity-L algebra.

Recovering a scalar `f(k,S)` from this representation uses three RAM reads and two additions. Recovering every requested scalar therefore adds only a constant times `(L+1) 2^(2L)` readout operations, which is dominated by the stated polynomial/exponential envelope and can be absorbed into its absolute constant. This observation concerns decoding the returned representation; the checked execution theorem itself retains the coefficient array, and the existing corrected extraction already visits every accepted coefficient when computing its scalar trial result.
