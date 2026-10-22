# Independent review of Section 4: the SK model

**Source bound to this review:** `main-12-2-2.tex`, SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6` (independently recomputed). All manuscript line numbers below refer to the frozen copy in this directory. Scope: Section 4, lines 1533–2150, using the definitions, orthogonality, and second-moment bounds in Sections 1–2. No manuscript or existing Lean source was changed for this review. This is a mathematical review, not a claim that every dependency has been independently kernel-checked in this subtask.

## Conclusion

I found **no mathematical counterexample or substantive proof gap in Section 4 as written**. The degree enumeration, weak-field Gaussian bound, augmented-graph correspondence, path/cycle dynamic programming, multiplicity corrections, finite coefficient algebra, estimator, and stated operation order all support their conclusions. The assumptions include the weak field and arbitrary symmetric variance-one disorder exactly where needed. The exact colorful evaluator does not require those probabilistic assumptions.

There is a real but harmless **implementation correspondence distinction**: the current `Manuscript/` Lean evaluator retains intermediate original-edge charge up to `2L`, while the manuscript retains charge only up to `L`. Its final extraction restricts charge to `L`, so it has the same output. This does not refute any Section 4 claim or change the claimed asymptotic operation bound. However, an assertion that the current formal program is literally the manuscript's loop schedule requires a projection/refinement theorem or explicitly describing the formal program as an equivalent implementation. See the dedicated discussion below.

## Dependencies checked for this section

- Original edges are two-element subsets of `[N]`, so graphs are simple and finite. Branching means original degree at least three.
- `N ≥ 2`, fixed `0 < beta_0 < 1`, `0 ≤ beta ≤ beta_0`, and `|h| ≤ rho_0 N^(-1/4)` imply `0 ≤ r_{N,2} ≤ beta_0^2/N` and `hhat^2 ≤ rho_0^2/sqrt(N)`.
- Independence and symmetry give centered independent edge weights. Thus distinct graph monomials are orthogonal, including with an entire dependent coefficient array independent of the disorder (lines 1172–1189).
- Section 2 supplies the total comparison mass `C_+` and the edge-tail bound `C_+ theta^(2(floor(t)+1)) ≤ C_+ theta^(2t)` (lines 1220–1321). I checked that their uses here preserve their direction and strict/non-strict cutoff conventions. A separate Section 2 review remains responsible for its entire proof.
- Throughout, graph sums are finite. Color coefficients are bounded because the inclusion probabilities are positive, so the expectations and products used in the estimator are integrable.

## Lemma 4.1: branching mass (`lem:sk-branching-mass`, lines 1582–1681)

**Status: verified mathematically, including constants.**

1. **Prescribed-degree enumeration (lines 1594–1604).** For a degree vector summing to `2m`, put `d_i` labeled half-edges at vertex `i`. There are `(2m-1)!!` pairings. Each fixed simple graph with those degrees has exactly `product_i d_i!` realizations: assign its incident edges to the labeled half-edges independently at every vertex. Pairings producing loops or multiple edges only enlarge the pairing count. Consequently the displayed bound is valid. No asymptotic degree restriction or existence assumption on the degree sequence is needed. This supplies an independent argument for the cited enumeration fact without trusting the citation.

2. **Gaussian substitution and extending degree ranges (lines 1606–1613).** The original degree sums are even, so the Gaussian even moment gives the exact expression used for each enumerated graph. Extending to arbitrary degrees in the stated coordinate ranges adds only nonnegative terms; odd total degrees in this enlarged sum are not asserted to correspond to graphs. Tonelli is applicable before integrability has been established because all summands are nonnegative. The later estimate proves finiteness. If `r=0`, the equality and bound still hold with the usual zeroth-power convention.

3. **Vertex generating functions (lines 1614–1630).** The nonbranching polynomial is exactly `1+hhat^2 x+x^2/2`. Branching odd degrees start at 3 and even degrees start at 4. The factorial comparisons `(2j+3)! ≥ 6*2^j*j!` and `(2j+4)! ≥ 24*2^j*j!` give the asserted common `exp(x^2/2)` upper bound. The weak-field factor is squared in this argument, as required by the second moment; it has not been accidentally replaced by a first-power factor.

4. **Powers of N (lines 1633–1638).** Both `hhat^2 r^(3/2)` and `r^2` are bounded by constants times `N^(-2)`. This is the essential source of the branching suppression. Writing `B = rho_0^2 beta_0^3/6+beta_0^4/24`, the prefactor is bounded by `N^(-2) B (1+z^4)` exactly as displayed.

5. **Gaussian tilt (lines 1639–1657).** For `eta=(1-beta_0^2)/2`, completing the square uses
   `a|z| ≤ a^2/(1-beta_0^2)+(1-beta_0^2)z^2/4`, with `a=rho_0^2 beta_0`.
   Adding `beta_0^2 z^2/2` gives `(1-eta)z^2/2`. Rescaling the resulting density gives the factor `eta^(-1/2)` and the replacement `z^4 -> eta^(-2)z^4`. Finally, since `b≥1` and `eta≤1`,
   `2^(b-1)(1+eta^(-2b)(4b-1)!!) ≤ (32 b^2/eta^2)^b`.
   Indeed `(4b-1)!! ≤ (4b)^(2b)`, and its scaled upper bound is at least one. The constants are conservative but valid.

6. **Final constants (lines 1658–1678).** The Gaussian normalization and square-completion constant are exactly `C_SK`. The binomial bound gives
   `choose(N,b) N^(-2b) B^b (32 b^2/eta^2)^b ≤ ((32e B/eta^2)b/N)^b`.
   Since `32e/eta^2=128e/(1-beta_0^2)^2`, this is the displayed `A_SK`. The last comparison with `exp(-Phi_N(b))` follows from `A_SK≤C_star` even when the bound exceeds one.

No mathematical repair is needed. Making the two-sentence half-edge argument explicit would reduce citation dependence but is optional exposition.

## Proposition 4.2: SK truncation (`prop:sk-truncation`, lines 1683–1717)

**Status: verified.**

- The discarded family is split into the disjoint alternatives `edges>L` and `edges≤L, branches>D`. Removing the edge restriction from the latter and splitting at `B=floor(gamma N)` only enlarges nonnegative sums.
- The assumption `D<B` guarantees `D+1≥1` and `D+1≤B`. On this interval, `Phi_N'(t)=log(N/(C_star t))-1≥2`. Thus the geometric ratio is `e^(-2)` and the factor 2 is valid.
- The integer implication `branches>floor(gamma N) => branches>gamma N` is correct. The handshake identity gives `2 edges≥3 branches`, so the last family has `edges>3 gamma N/2`. Applying the real-threshold edge bound gives `C_+ theta^(3 gamma N)` with the correct exponent and inequality direction.
- For small N with `floor(gamma N)=0`, the proposition has no admissible D; it does not make a false small-N claim. The main algorithm must use its separate exact branch there, outside the scope of this section.

## Augmentation and Lemma 4.3 (`lem:sk-decomposition`, lines 1721–1839)

**Status: verified, both existence and uniqueness.**

- Every original vertex gains an auxiliary edge exactly when its original degree is odd. Original augmented degrees are even. The degree of 0 is even because the number of odd-degree vertices is even.
- Conversely, deleting 0 from an even simple graph yields a unique original graph, and parity forces each deleted edge to be precisely its odd-vertex auxiliary edge. The evenness condition at 0 is redundant given evenness at all original vertices and the handshake identity, but including it is correct.
- Original degree is at least three iff augmented degree is at least four. Outside degrees become exactly 0 or 2, including degree-one endpoints attached to 0.
- In the induced used-outside graph every connected component is a cycle, a nontrivial path, or an isolated vertex. A cycle has no attachment to the distinguished set. A path component has exactly two attachments, one at each end; for an isolated vertex they must go to different distinguished vertices, since the ambient graph is simple. Equal attachments for a nontrivial path produce a rooted cycle of length at least three.
- The component edge sets and direct edges partition all augmented edges and have disjoint outside vertex sets.
- Uniqueness is forced at every outside vertex because both incident edges must belong to the same piece. Continuing through its outside component gives its entire component piece. The induced outside part of a permitted nondirect piece is connected, so it cannot absorb two components. Direct edges can only be singleton pieces.
- For the converse, piece intersections ensure a simple union with outside degree 0 or 2. Even distinguished degrees and degrees at least four on A yield augmentation of the deleted graph and exact original branching set A. There is no missing exclusion for duplicate auxiliary edges: nondirect pieces with disjoint outside vertices cannot share such an edge, and direct auxiliary edges are separate singleton factors.

## Proposition 4.4: exact colorful summation (`prop:sk-colorful`, lines 1869–2037)

**Status: verified, including arbitrary signed real weights.**

### Path and cycle tables (lines 1882–1910)

The first recurrence has a last-vertex deletion bijection. Its color removal prevents every repeated vertex, not merely repeated endpoints. The second recurrence includes the root color from its zero-edge singleton initialization; its endpoint restriction prevents an early return to the root. Both tables therefore enumerate exactly their stated simple colorful paths.

Closing a path with distinguished endpoints counts an undirected path once when starting at the smaller endpoint. Rooted cycles are counted twice, once per orientation. Entirely outside cycles are counted `2|S|` times, by orientation and root. The size restrictions 1, 2, and 3 respectively exclude degenerate paths and two-edge traversals. Negative weights do not change these multiplicities.

### Charge and degree bookkeeping (lines 1922–1971)

The five original-edge charges are respectively `|S|`, `|S|+1`, `|S|+1`, `|S|`, and `|S|-1`. The last two subtract one or two auxiliary edges exactly. Every nondirect primitive has at least one original edge under its stated minimum size. Direct original edges have charge 1; direct auxiliary edges have charge 0.

The six degree states preserve addition because any sum involving a state at least four stays at least four with the same parity. The quotient relation `y^6=y^4` implements precisely this state map (it does not identify degrees 0 and 2 with degrees at least four). Together with `x_i^2=0` and `t^(L+1)=0`, these monic separate-variable relations admit the displayed finite normal form. In particular, coefficient extraction after reduction is well-defined.

### Exponential and direct factors (lines 1973–2023)

A surviving product of nondirect primitives has disjoint nonempty outside color sets. Its selected pieces are therefore distinct and edge-disjoint. Each collection has exactly `j!` orderings, so factorial division counts it once. Since each primitive has positive original-edge charge, `j>L` cannot contribute. Direct factors choose each distinguished pair at most once and cannot overlap any nondirect edge. Color-disjointness is deliberately stronger than outside-vertex-disjointness, exactly matching the colorful target.

The accepting states select even auxiliary degree and even original distinguished degrees at least four. The decomposition converse then gives the unique original graph with exact branching set A. Used outside vertices survive deletion of 0 because their augmented degree is two and at most one incident edge is auxiliary. Thus their original color set is the recorded S. The reverse direction and decomposition uniqueness give multiplicity one. The empty graph is counted once only in the appropriate `A=empty,k=0,S=empty` coefficient. All arguments concern contributions before cancellations, so zero/negative weights pose no problem.

### Operation bound (lines 2025–2036)

There are exactly `N+1` path tables (the `b+1` distinguished roots and `N-b` outside roots). Each has at most `N4^L` entries, each with at most N predecessors. The closure sums and mask/index operations fit the generous polynomial allowance. A dense coefficient multiplication visits at most
`36(L+1)^2 16^L 36^b`
pairs. Degree vectors have `b+1≤N+1` entries and masks have `2L` bits, so the stated `O((N+2L+1)^2)` per-pair allowance is sufficient. There are at most `L+(b+1)^2` multiplications; scalar passes and additions are smaller. The resulting sixth power and exponential factors are correct. This is an exact-operation model, as the manuscript explicitly says; no bit-complexity claim follows.

## Proposition 4.5: SK evaluation (`prop:sk-estimator`, lines 2044–2137)

**Status: verified.**

- A graph with at most L original edges has at most `2L` used outside vertices, including when it has nonzero field factors. Its colorful probability is `(2L)_m/(2L)^m`, and each target entry has common `m=|S|`.
- Dividing each included coefficient by this probability gives conditional unbiasedness for fixed arbitrary J. The argument does not assume graph weights are nonnegative.
- For an individual retained graph, its coefficient is the average of R independent Bernoulli inclusions divided by their common probability. Its variance is exactly `(1-pi)/(R*pi)`.
- The inclusion probability is decreasing in m. `pi_(2L,2L)=(2L)!/(2L)^(2L)≥exp(-2L)` gives the displayed variance bound. The m=0 case has probability one and variance zero.
- Coefficients of different graphs need not be independent. The full coefficient array is independent of J, so disorder orthogonality eliminates the cross terms in the joint second moment. This distinction is stated correctly and is essential. Total graph mass then gives `C_+ exp(2L)/R`.
- Candidate sets have unique cardinality and are each generated once; summing the colorful evaluator cost over candidates and R trials gives the claimed cost. Preparation and correction work fit the same bound. Uniform color sampling is used in the manuscript's elementary random-operation model; the theorem makes no random-bit/rejection-sampling worst-case claim.

## Complete error identity (lines 2139–2150)

**Status: verified.** The evaluation error has conditional color mean zero for each fixed J. The truncation error is fixed under that conditioning. Their cross term therefore vanishes, yielding the exact squared-error decomposition before the four displayed upper bounds are substituted. No unnecessary factor of two is needed or missing.

## Current Lean capacity distinction

This review inspected actual definitions in `Manuscript/`, not just the older infrastructure in `SpinGlass/`.

- `Manuscript/SKChargedExecution.lean`, lines 17–31, contains the correct charge rules. Endpoint charge is zero at the auxiliary vertex and one at original distinguished vertices; the physical-path charge formula specializes to all five manuscript cases. Its direct factors correctly charge an auxiliary edge zero.
- Its `evaluate` at lines 37–40 uses `SKCoefficient.Coefficients b K`, whose single capacity parameter supplies both K colors and charge degrees `0..K`.
- `Manuscript/SKGeneratedExecution.lean`, `trial`, instantiates K as `2L`.
- `Manuscript/SKChargedExecution.lean`, `byOutsideSize` at lines 93–98, extracts only `k≤L`. `SKGhostCoefficient.coefficient_original` identifies each accepted coefficient with its precise original-graph sum; `SKGhostOutsideSize.byOutsideSize_eq` identifies the final extracted vector for every `L≤K`. These statements directly cover the returned quantity at K=2L; they do not assume evaluator correctness as an input.
- The manuscript, by contrast, imposes `t^(L+1)=0` (line 1941) and uses exactly L exponential iterations (lines 1976–1981).

The mathematical equivalence is as follows. For fixed 2L color variables and distinguished degree states, the quotient from charge capacity 2L to charge capacity L discards only terms of charge above L. Charges add and are nonnegative; degree-state reduction never changes charge. Therefore projection commutes with multiplication followed by the smaller truncation. Every physical nondirect primitive has charge at least one; the finite-exponential terms of index above L project to zero. Direct auxiliary edges have charge zero, so adding them cannot bring a discarded term back into the retained range. Thus low-degree coefficients of both schedules coincide. The larger evaluator changes array length by less than two and exponential iterations by two, and its established cost bound absorbs these factors.

**Classification:** no mathematical error in the paper and no output mismatch. For the user's requirement of complete formal correspondence, formally proving this projection/short-loop identity is a useful remaining bridge if the claim is that the exact displayed schedule is covered. The separate module `LeanAdditions/SKChargeProjection.lean` now proves this bridge and compiles successfully; no existing frozen-package source was changed.

## Scope and remaining cautions

I did not certify bibliographic metadata or historical claims in the Section 4 introductory paragraph. The operative enumeration fact was checked independently above. I did not run numerical tests as a substitute for proof, and I did not treat any prior review's claimed completion as evidence. This report does not by itself establish the whole-paper theorem or a fresh Lean build: those require the other sections, final theorem assumptions, and the parent verification run.


## Completed Lean correspondence bridge

`LeanAdditions/SKChargeProjection.lean` was compiled standalone against the verified existing package with Lean 4.32.1. Final compilation exited 0 with no diagnostics. The separately compiled `SKChargeProjectionAudit.lean` printed the axiom sets of ten bridge results; all contain only `propext`, `Classical.choice`, and `Quot.sound`. In particular, no `sorryAx` or custom axiom occurs in the final output-equivalence chain. Full output and a source checksum are retained in `LeanAdditions/compilation.log`, `LeanAdditions/axiom-audit.log`, and `LeanAdditions/verification.json`.

The bridge preserves the fixed palette `Fin (2*L)`. It introduces a separate `RetainedBasis b L K` with L+1 charge slots and K colors, proves the stated array size `(L+1)4^L6^(b+1)`, and proves that its multiplication is restriction of the larger multiplication. It then proves:

1. `project_mul` / `retainedMul_restrict`: early original-edge truncation preserves every retained product coefficient.
2. `expLoop_low_stable`: terms after iteration L cannot contribute at charges at most L when the primitives have positive original-edge charge.
3. `projectedEvaluator_low`: an explicit recurrence that projects every update and runs exactly L exponential iterations agrees at every retained coordinate with the current evaluator.
4. `ghost_capacity_two_mul_eq_manuscript`: positivity is discharged for the actual auxiliary-vertex primitives, so this comparison has no assumed evaluator-equivalence premise. Auxiliary direct edges may still have charge zero.
5. `projectedByOutsideSize_eq` and `projectedTrial_eq`: actual accepting-state extraction and inverse-color-probability correction preserve equality.
6. `projectedAlgorithm_eq_generated` and `projectedAlgorithm_eq_disorder`: all candidates and repetitions of the projected algorithm equal both the current counted estimator's value and the graph estimator used in the disorder analysis.

The recurrence is the manuscript's mathematical coefficient computation: initialize the empty collection, multiply by the projected primitive array and divide by the next integer, project the result and accumulated sum, and multiply each direct-edge factor exactly once, projecting again. The theorem does not assert literal allocation of the smaller arrays, equality of low-level machine instruction schedules, or a newly verified runtime for primitive-table construction. Those are separate implementation questions. It does resolve the mathematical output correspondence for the L-versus-2L capacity difference through the complete estimator, not just for an abstract coefficient.

## Projected full-output and probability endpoint

The follow-up module `LeanAdditions/SKProjectedOutput.lean` now carries the projected estimator all the way to the theorem's returned logarithmic value. Its `evaluate` definition uses the actual saved `SKControl.control` result and the same exact fallback as `SKPhysicalExecution.evaluate`; only its truncated branch calls the separately defined projected estimator. Its `output` uses the same computed accuracy budget, color-tape transport, prepared prefactor, positivity test, and nonpositive-correction fallback as `SKFinal.execute`.

Theorems `evaluate_prepared` and `graphApprox_eq_execute` prove GraphApprox value equality on actual prepared physical inputs. `output_eq_execute` proves pointwise equality of the returned logarithmic output for every real disorder input and color tape. Finally `accuracy` states and proves the original `delta + tau_N` failure bound for this projected output under the manuscript's model assumptions. It has no mean-square-error, desired-output-equality, or evaluator-correctness premise; the bound follows from the proved program identity and `SKFinal.accuracy`.

This module compiled successfully with no diagnostics. Its four endpoint axioms were separately printed and contain only `propext`, `Classical.choice`, and `Quot.sound`; the logs and source digests are in the `projected-output-*` files in `LeanAdditions/`. This output/probability extension does not attach a new runtime counter to the projected implementation or claim a primitive-allocation refinement.
