# Higher-order execution refinement: established and remaining

This is a source-level review of `SupportExecution`, `SupportLocalExecution`, `SupportIndices`, `SupportCoefficientExecution`, `InputPreparation`, and their immediate definitions. It addresses the stricter question whether the established operation counters are related to actual permitted machine steps. The mathematical analytic audit remains in `analytic-review.md`.

## What the existing theorems establish

The source contains concrete recursive list computations for sums, products, subset generation, spin-string generation, and subset tests. Their correctness and the displayed counter bounds are proved. In particular, `SupportExecution.supportSum_value` identifies the actual return expression with the retained graph sum, and `supportSum_cost` proves a weighted-binomial bound on its `operations` field. Input preparation proves the correct cached weights and logarithmic prefactor. These are substantial results rather than assumed graph-error or cost bounds.

Nevertheless, the underlying type `SpinGlass.ArithmeticEvaluation.Computation` has only two unrestricted fields, `value : ℝ` and `operations : ℕ` (`ArithmeticEvaluation.lean:16`). Its `literal : ℝ → Computation` accepts any real expression at zero cost. This permits legitimate reads of precomputed values, but the type does not distinguish a read of a previously computed register from an uncharged host-language calculation. The theorems about these records do not by themselves supply a machine-execution relation that closes that distinction.

The same boundary occurs in records carrying cached functions and generated lists. Their counters are faithful to a proposed high-level algorithm under intended unit-cost index/array conventions. The current theorem statements do not formalize those conventions and prove the corresponding refinement throughout the entire SupportSum call tree.

## Concrete scalar gap closed in this audit

`LeanAdditions/EdgePreparationInstructions.lean` now provides an execution realization of `InputPreparation.prepareEdge`, not merely a generic unconnected syntax.

Its read-only input type has exactly five keys: system size, interaction order, interaction coefficient, supplied inverse temperature, and supplied coupling. Constants have a fixed two-symbol alphabet, `-1` and `2`. Operand constructors accept only one of these input keys, one of those constants, or a register index. They cannot accept arbitrary real expressions. The instruction type permits only addition, multiplication, division, exponential, logarithm, and hyperbolic tangent, each writing one typed real register. The execution relation has a zero-step base rule and a rule that executes exactly one such instruction; its step count is derived, not supplied as an unchecked result field.

The concrete program has 15 instructions:

| Instructions | Computation |
| --- | --- |
| 1–5 | Compute `exp(log N * ((p-1)/2))` |
| 6–8 | Compute the shared coupling `x=beta*a*J/denominator` |
| 9 | Compute `tanh x` |
| 10–15 | Compute `log((exp x + exp(-x))/2)` while reusing `x` |

`prepareEdge_realized` proves that, from **any** initial register contents, this actual instruction sequence executes in 15 steps, returns precisely both scalar outputs of `InputPreparation.prepareEdge`, and equals its existing primitive-operation count. The arbitrary initial-state quantifier rules out supplying a precomputed answer through an uninitialized register. `prepareEdge_physical` further identifies the outputs with the physical tanh and log-cosh formulas using the model's half-integer normalization. No output or cost-correctness hypothesis is assumed.

This is an exact realization of the scalar arithmetic/elementary-function budget. The model does not separately charge operand selection or destination-register assignment within each arithmetic instruction. The enclosing input-array traversal, metadata operations, and cache writes are separate obligations, as explicitly stated in the theorem documentation. The module is not presented as a SupportSum or full higher-order execution theorem.

The module compiled successfully under Lean 4.32.1. Its axiom audit is recorded separately in `LeanAdditions/EdgePreparationInstructions-axioms.log`.

## Remaining concrete boundaries

### Input layout, metadata, and cache accesses

`InputPreparation.prepareEdges` (`InputPreparation.lean:76`) stores its cache as a function `E → EdgeData` using nested `Function.update` calls. The comment treats finite-index updates and reads as unit-cost array primitives. That is a reasonable target model, but a theorem identifying this mathematical function with an addressed array and preserving update/read values and costs is still needed. Executing nested functional updates literally need not give constant-time access.

Its five charged overhead operations per edge encompass several intended metadata/control/read/write actions. The expression `e.val.card`, the coefficient lookup `a e.val.card`, and coupling lookup `J e` need a fixed input layout or a proved addressed-array representation. Without that layout, their physical costs cannot be inferred from the function types. The scalar 15-step theorem does not establish the enclosing `20 * es.length` execution cost.

`InputIndices.generationWork` (`InputIndices.lean:85`) is a proved polynomial expression built from the recursive generator's work. The actual list `edges` is formed through certified-choice packing, subtype tags, and concatenation. A machine-level simulation must account for the packing, order-list traversal, edge identifiers, and concatenation and connect them to the declared overhead. Proof erasure makes subtype proofs free, but that fact alone is not an addressing/layout theorem.

### Local spin representation and access

`SupportLocalExecution.localAssignments` (`SupportLocalExecution.lean:13`) uses `U.equivFin` to transport generated spin strings to functions on the local support. `SupportIndices.cubeAssignments` (`SupportIndices.lean:354`) represents a coordinate read through a list lookup `(l[i.val]?).getD false`. The current indexed cost treats spin reads as array accesses. There is no shown refinement from these function/list representations to a concrete local or ambient array, including construction of the local-to-ambient index map.

This is not an obstacle to a polynomial implementation: one may fill an ambient array once for each assignment and then access it by vertex index, exactly as the manuscript describes. It is an additional formal obligation. If the displayed list lookup were executed literally for every access, its traversal costs would have to be counted, rather than identified with one array read.

### Local incidence, containment, and saved edge lists

The source does prove a concrete short-circuit containment test and a saved list of induced interactions. However, arithmetic characters call `localIncidence`, defined using a finite-set subtype construction (`SupportEvaluation.lean:131`), and then a finite-set-to-list traversal. Their representations and construction costs are not part of the arithmetic character's counter. A concrete implementation can instead store the already validated original vertex indices for each induced edge and use those indices directly. The equivalence of that implementation to the `localIncidence` character must be proved.

`indexedSpinTerm` (`SupportLocalExecution.lean:93`) adds `3*|U|`, a sum of local incidence sizes, and the number of edges to the arithmetic term counter. These terms describe the intended writes and reads but are not a trace of explicitly defined memory instructions. To close the refinement, the writes, spin/field reads, and interaction-weight reads should be explicit in the machine program and its execution bound should derive these terms or a justified encompassing bound.

### Loop control and sharing through the support sum

`SupportExecution.layer` computes one coefficient, reuses its value for each generated support, and appends generator/packing counts (`SupportExecution.lean:13`). Its reuse of `literal c.value` is intended cached reuse; a register/environment invariant should certify that it is a previously computed value. The same applies to field and interaction caches.

`sumFinset` obtains a list through `Finset.toList`, and the truncation traverses `Finset.range(k+1)`. Their machine iteration and control costs should be attached to concrete lists/indices. The final `supportSum` branch test itself is not a separate increment of its returned counter. This does not contradict the generous eventual polynomial upper bound, but it prevents taking every counter equality as an exact instruction count without specifying what the primitive model charges.

The coefficient evaluator does have a specific arithmetic recurrence for descending factorial, factorial, and sign. It still needs the same operation-realization relation for its integer counters and real arithmetic if the final claim is a machine-step theorem.

## Minimal full higher-order refinement

The shortest credible completion is a compositional refinement of the existing implementation, preserving its graph identities and cost proofs, with these pieces:

1. Fix a unit-cost exact-real machine with separate types for real registers, natural indices, Boolean values, and array/list addresses. Keep the physical input read-only and restrict program constants to fixed model constants plus literal scalars. Specify precisely which control and memory actions cost one.
2. Give a finite addressed representation of the interaction array and the support/spin arrays. Prove representation invariants for lookup and update; this replaces reliance on function-valued caches and abstract finite-set enumerations as free operations.
3. Refine the existing include/exclude and cube generators, their packing, and index-map construction to actual machine loops. Reuse their mathematical list correctness and output-sensitive counting lemmas, but prove that the machine steps are bounded by the charged overhead.
4. Refine one local-spin evaluation from the saved induced-edge list and cached field/edge arrays, with explicit multiplication, field-factor access, spin reads/writes, and accumulation. Prove equality to `localEvaluator.value` and a bound sufficient for the current `localConstant`/`layerConstant` estimate, or adjust those fixed constants transparently if control/read accounting needs more slack.
5. Compose coefficient generation, support generation, local evaluations, and the exact/full-support branch into a single machine program. Prove its output equals `supportSum.value` and its actual steps have the weighted-binomial bound; then connect this with cutoff selection and the already-proved MSE theorem.
6. Compose input preparation, budget/control computation, SupportSum, and final logarithm, proving that each cached value is available when read. Only this final composed execution theorem supplies the complete deterministic algorithm operation guarantee under the explicit machine model.

A general expression syntax and a generic theorem about its node count are insufficient unless the actual programs above are compiled into it and their values, sharing, index work, and primitive budgets are proved. The new edge-preparation theorem does make that connection for one scalar subroutine. I have not completed the full SupportSum refinement in this audit and do not claim it is already established by the existing counter theorems.
