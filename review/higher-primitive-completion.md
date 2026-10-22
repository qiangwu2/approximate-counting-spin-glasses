# Higher-order primitive execution completed

The new module `Manuscript.RestrictedHigherFinal` proves `end_to_end`: for the manuscript's original higher-order hypotheses, one constant accompanies both the original-law probability estimate and an actual finite-procedure register-machine execution from ordinary raw serialized input. The execution's real output register 3 equals the previously proved manuscript algorithm output, for every disorder array and every ordering of the input interaction records.

The machine program is fixed by the model parameters before N, field, tolerance, probability parameter, disorder, and raw record ordering are supplied. Its two fixed procedures generate retained subsets and local Boolean spin masks. They save and restore only explicit finite register lists; each saved register, call, and return is charged. All arithmetic, comparisons, parameter reads, raw input reads, cache reads/writes, loop tests, and output accumulation are realized by restricted instructions.

Key checked statements:

- `RestrictedHigherEndpoint.program_exec`: actual complete execution from zero state, with exact manuscript output and explicit instruction count bounded by `141*M + 78*N + 461 + B(N,M)*W(N,k)`, where `B=59*N+26+(66*N+56)*M+300*(N+1)+400` and `W=sum_{l=0}^k choose(N,l)*2^l`.
- `RestrictedSupportExecution.program_correct`: the actual support program, including coefficient computation, subset generation, cube generation, and local spin arithmetic, equals the retained support evaluator. This includes k=N and arbitrary raw edge-record ordering.
- `RestrictedSupportLowerBound.weighted_le_operations_square`: W is bounded by the square of the earlier arithmetic count plus one, including the exact branch. No runtime statement is assumed.
- `RestrictedHigherRuntime.program_overhead`: actual steps are at most `3000*(N + oldFinal.operations + 1)^4`.
- `RestrictedHigherRuntime.polynomial`: the actual trace has the common polynomial bound in N, epsilon inverse, and delta inverse.
- `RestrictedHigherFinal.end_to_end`: combines this concrete execution with the original-law accuracy theorem.

The exact branch intentionally uses the same uniform support-layer program: lower coefficients vanish and the full-support layer is exact. Its 3^N work is bounded by the square of the earlier exact 2^N evaluator's work, preserving the polynomial theorem. This is a coarser implementation bound than the original arithmetic counter, not an assumed counter equality.

The axiom audit for all four final statements reports only `propext`, `Classical.choice`, and `Quot.sound`; see `higher-primitive-axioms.txt`. No canonical manuscript or historical module was edited for this refinement. The machine is the explicitly specified exact-real stack RAM, not a floating-point implementation.
