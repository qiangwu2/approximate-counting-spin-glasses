# Higher-order GraphApprox primitive endpoint

The standalone raw-accuracy endpoint is implemented in these new package modules:

- `Manuscript/RestrictedHigherGraphEndpoint.lean`
- `Manuscript/RestrictedHigherGraphRuntime.lean`
- `Manuscript/RestrictedHigherGraphFinal.lean`

All three compile successfully with Lean 4.32.1 against the existing package.

## Actual execution

`RestrictedHigherGraphEndpoint.program` starts from the zero machine state and the raw input `RestrictedInputEncoding.encode order beta h u 1 J tape`. The edge-record enumeration only specifies raw input order; it is absent from program syntax. The fixed model parameters contain the model data, not any evaluated interaction or output.

The program executes physical preparation, then executes three primitive instructions that read the requested raw accuracy at real-input address `M+2` and store it in real register 508. It then executes the existing cutoff controller, support setup, and recursive support program. Thus the cutoff uses the original supplied `u`; the temporary budget computed during preparation is overwritten by an actual input read. The endpoint stops with the graph value in real register 330 and has no final logarithm.

`program_exec` derives the complete primitive execution and proves that its output equals `HigherOrderExecution.execute(...,u,J).value`. Its hypotheses are only the positive vertex count, fixed order bound, and a bijection identifying the ordinary raw coupling records. It does not assume output equality, support realization, cache correctness, a runtime estimate, or an MSE estimate.

Its explicit primitive-operation bound is

`141 M + 78 N + 461 + (59 N + 26 + (66 N + 56) M + 300 (N+1) + 400) W`,

where `W = sum_{l=0}^k choose(N,l) 2^l` and `k` is the cutoff computed from the raw `u`.

## Runtime

`RestrictedHigherGraphRuntime.old_lower` proves that the existing exact arithmetic computation count dominates `M` and that its square dominates `W`. Consequently `program_overhead` bounds the actual primitive execution by

`3000 (N + HigherOrderExecution.execute.operations + 1)^4`.

`polynomial` combines this proved operational bound with `HigherOrderExecution.execute_polynomial`. One positive fixed constant `C` bounds every actual execution by `C N^C u^(-C)` throughout the full range `0 < u < 1`. The instruction count includes the actual raw input reads, physical cache generation, cutoff/control, support enumeration, and recursion. This is the declared real-arithmetic RAM model, not a bit-complexity claim.

## Original-law MSE

`RestrictedHigherGraphFinal.end_to_end` proves, for the higher-order assumptions of Proposition 5.2, the original-law MSE bound at the requested raw `u`, and simultaneously provides the actual fixed-program execution with the polynomial instruction bound and exact output identity. The analytic bound is transferred through the proved `HigherOrderExecution.execute_value` identity to `HigherOrderAlgorithm.mse_bound`. The endpoint has no desired-equality or desired-MSE premise.

The positive vertex count needed by physical preparation is derived from nonempty interaction orders, the lower order bound of three, and the assumption that every interaction order is at most `N`.

Canonical TeX and existing package root imports were not edited by this addition.
