# Approximate counting for mixed p-spin glasses

Lean formalization of the [October 27, 2026 manuscript](paper/manuscript-2026-10-27.pdf), including its higher-order and SK approximation algorithms as fixed programs.

## Main theorems

The public endpoints are in [`Manuscript/PrimitiveTheorem.lean`](Manuscript/PrimitiveTheorem.lean):

- `Manuscript.theorem_1_1_higher_primitive` and `Manuscript.theorem_1_1_sk_primitive`: logarithmic approximation.
- `Manuscript.proposition_5_2_higher_primitive` and `Manuscript.proposition_5_2_sk_primitive`: mean-square approximation.

The proofs establish program execution, the returned estimator, its accuracy guarantee, and polynomial bounds on charged instructions.

## Formal scope

The general reverse-hypercontractivity theorem quoted in Lemma 5.3, for arbitrary finite product probability spaces and all exponents `q < p < 1`, is not formalized in full. Its uniform-sign specialization with `q < 0 < p < 1`, exactly the case used by the manuscript, is independently proved in Lean. [`Manuscript/PDF16Noise.lean`](Manuscript/PDF16Noise.lean) relates this specialization to the manuscript's resampling operator and time parameter. The other numbered results have complete formal counterparts, and all dependencies needed by the main algorithm theorems are proved.

The operation bounds use the manuscript's exact-real arithmetic model. Accuracy is a probability guarantee under the stated independent symmetric unit-second-moment disorder law and, for SK, independent internal colors. Execution and operation bounds hold for every permitted finite input and random outcome. Floating-point error, bit complexity, and native execution speed are outside this model.

## Build

Install [Lean via elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
```

The project pins Lean to `leanprover/lean4:v4.32.1` and mathlib to commit `520045ab14e26149ee970e2e617ca04b09bde5d6`. Dependency revisions are recorded in `lake-manifest.json`. The first build requires network access to obtain these dependencies.
