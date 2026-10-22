# Independent analytic audit of Sections 2, 3, and 5

Audit date: 2026-10-22. Source: `main-12-2-2.tex` in this directory, SHA-256 `edbea067f5db10e67d31935a68778b0e1fcc786ed0e050ef06b1152b132642c6`. The digest was recomputed from the actual file. Line references below refer to that frozen source. I read the assumptions and main statements in Section 1, all of Sections 2, 3, and 5, and the SK estimates and constants consumed by Section 5. I did not use earlier audit summaries as evidence. No manuscript or Lean source was edited.

## Outcome and scope

**No confirmed mathematical defect, and no unresolved substantive proof gap, was found in the assigned analytic sections.** In particular, the constants and exponents in the second-moment bound, higher-order support estimate, cutoff selection, negative-moment argument, and logarithmic-error conversion are consistent. The cited reverse-hypercontractive theorem has the hypotheses, time normalization, and negative-exponent range required by the proof.

The SK conclusion in Section 5 is verified as a consequence of the displayed SK truncation and evaluation results. A separate audit must establish the complete color-coded evaluator in Section 4; this report does not certify that construction merely by checking its downstream algebra. The present audit is a conventional mathematical audit, not an end-to-end Lean verification. In particular, the external reverse-hypercontractive theorem remains an external mathematical input until it is actually proved or imported as a proved theorem in Lean.

The only observations classified as exposition or conventions are listed near the end. None invalidates the stated mathematical conclusions.

## Assumptions, quantifiers, and constants

The standing assumptions are explicit at lines 938–975 and 1139:

- The interaction orders form a finite nonempty set, either SK with order 2 and coefficient 1, or a mixture with all orders at least 3. Coefficients are positive. There are no repeated sites in an interaction.
- `N >= P`, where `P` is the maximum interaction order. Thus `N >= 2`, and in Section 3, `N >= 3`.
- The couplings are independent with a common symmetric real law and unit second moment. Higher moments are not silently used in the core analytic estimates.
- `0 < beta_0 < beta_f` is fixed, while the supplied `beta` may equal zero. This distinction is essential: divisions by `beta_0` and `theta` remain legitimate at zero supplied temperature.
- `rho_0 > 0` is fixed and the supplied field is homogeneous, with `|h| <= rho_0 N^(-1/4)`. Supplied parameters are specified rather than selected after seeing the disorder.

The threshold bounds in lines 965–969 are correct. For `x in (0,1]`, every power has order at least 2, so `xi(x) <= xi(1)x^2`; integrating `I''(x) >= 1` from zero gives `I(x) >= x^2/2`. These prove the strictly positive lower bound for `beta_f^2`, while evaluation at 1 proves its finite upper bound. For SK, the limit at zero and the same lower bound give `beta_f = 1`.

Consequently `beta_0 < beta_+ < beta_f`, `0 < theta < 1`, and `0 < lambda_+ < 1`. All subsequent logarithms, inverse powers, and denominators using these fixed constants are defined. Their dependence is solely on the fixed model and `beta_0,rho_0`, not on the disorder law. Dependence on the law occurs only in the tail quantity `tau_N` and in its asymptotic rate under extra moments.

## Section 2: expansion, orthogonality, and total mass

### Expansion and positivity (lines 1143–1169)

The elementary identity `exp(x sigma_e) = cosh(x)(1 + tanh(x) sigma_e)` applies because each interaction spin product is either sign. The independent spin average assigns one factor `tanh h` precisely to each odd-degree vertex. This establishes the claimed finite graph expansion, including the empty graph.

Every finite real coupling gives `|tanh x_e| < 1`; hence each product factor is strictly positive and the spin average is strictly positive. This is a pointwise statement for every finite input, and does not require a probability exceptional set. For negative fields the graph weights can have either sign, but positivity of the original product average still holds. All empty products and zeroth powers, including `0^0` at zero field, are explicitly assigned the value one at line 1148.

Symmetry makes `omega_e` centered. Its boundedness is enough to make that expectation meaningful. The bound `r_{N,p} <= beta_0^2 a_p^2 / N^(p-1)` uses only `tanh^2 x <= x^2` and the unit second moment; it is valid also at `beta = 0`.

### Lemma `lem:orthogonality` (lines 1172–1186)

Verified. For distinct edge sets there is an interaction in their symmetric difference, whose weight appears to the first power and is independent of every remaining factor. The diagonal factors into the product of second moments. There is no requirement that the graphs have disjoint vertex sets: independence belongs to interaction indices, which is the correct notion here.

For the random-coefficient identity, the full coefficient array must be independent of the full disorder array, as stated. Coefficients can be mutually dependent. There are finitely many graphs, all edge weights and field factors are bounded, and each coefficient is square integrable, so expansion and integration of the finite square are legitimate. Conditioning on the coefficient array establishes the result. The deterministic truncation identity follows by taking coefficients zero or one. No unproved orthogonality between coloring coefficients is assumed.

### Proposition `prop:mass` (lines 1220–1322)

Verified, with the stated explicit `C_+`. The checks that matter for this estimate are as follows.

1. The tilted field identity is exact:
   `arctanh(tanh^2 h) = (1/2) log cosh(2h)`.
   It is nonnegative, even in `h`, and at most `h^2`. The tilted spins therefore have the required mean `tanh^2 h`.
2. The graph sum with the comparison weights is the tilted spin average of the product, by the same finite expansion. No probabilistic interpretation of the comparison weights as actual edge moments is needed.
3. The number of ordered `p`-tuples with a repeated site is at most `binom(p,2) N^(p-1)`: use a union bound over a pair of positions constrained to agree. The bound permits overcounting and has exactly the normalization needed. After division by `p!` and multiplication by `beta_+^2 a_p^2/N^(p-1)`, its error is `beta_+^2 a_p^2/[2(p-2)!]`. Summing gives the manuscript's `beta_+^2 Delta`.
4. For negative magnetization, `xi(x) <= xi(|x|)` follows from nonnegative coefficients. The definition of `beta_f`, evenness of `I`, and the zero value at zero prove `beta_+^2 xi(x) <= lambda_+ I(x)` on the full interval `[-1,1]`. Odd interaction orders introduce no sign problem here.
5. It is necessary to check that the product factors are positive before multiplying their individual upper bounds. The manuscript does so correctly: `beta_+^2 xi(1) < log 2` implies `beta_+^2 a_p^2 < p! log 2`, and `p! <= p^(p-1) <= N^(p-1)`. Thus `bar r_{N,p} < log 2 < 1`, including the smallest allowed `N = P`.
6. The change of measure contributes exactly `exp(tilde h S_N)/cosh(tilde h)^N`. The exponents `q_1 = (1+lambda_+)/(2 lambda_+)` and `q_2 = (1+lambda_+)/(1-lambda_+)` are conjugate and strictly greater than one. Their product parameter is `v = q_1 lambda_+ = (1+lambda_+)/2 < 1`.
7. For uniform independent signs, Chernoff's inequality gives `Pr(S_N >= Nx) <= exp(-N I(x))` for `x in [0,1]`. The endpoint `x=1` follows by a limit of the exponential-Markov parameter, or directly from `Pr(S_N=N)=2^(-N)`. Symmetry and monotonicity of `I` yield `Pr(X_N>t) <= 2 exp(-t)` on the entire nonnegative half-line, with the tail zero beyond `N log 2`.
8. The tail integral equals `1 + v integral exp(vt) Pr(X_N>t) dt`. Its bound is `1 + 2v/(1-v) = (3+lambda_+)/(1-lambda_+)`. Taking the power `1/q_1 < 1` can only decrease this number, since it exceeds one.
9. Discarding `cosh(tilde h)^N >= 1` and using `log cosh y <= y^2/2` gives the field contribution `exp(q_2 rho_0^4/2)`. This is precisely the field term in `C_+`.

The edge tail is also correct for every real `t >= 0`. An integer edge count greater than `t` is at least `floor(t)+1`; since `theta in (0,1)`, it contributes at most `theta^(2(floor(t)+1))` relative to the comparison mass. Replacing this exponent by `2t` only enlarges the upper bound. This handles integer and noninteger thresholds and `t=0` without a rounding error.

The corollary `E hat Z_N^2 <= C_+` follows because the original moments are bounded by the comparison weights. `C_+ > 1`, so it also supplies the advertised `C_+ >= 1` for the main algorithm.

## Section 3: higher-order support and exact summation

### Lemma `lem:higher-support-mass` (lines 1353–1406)

Verified for every stated `alpha >= 1/4`, not only for the subsequently chosen exponent. For a graph with `v` used vertices and total degree `d`, one has `d >= v` and `d >= 2v - |boundary Gamma|`. Thus `ell = max(2v-d,0)` is an integer in `[0,v]`, and the field factor is bounded by `rho_1^(2v) (v/N)^(2 alpha ell)`. This inequality uses both `|tanh h| <= 1` and the assumed decay bound, exactly as written. At zero field and `ell=0`, the established zeroth-power convention is necessary and sufficient.

The graph count `binom(N,v) product_p binom(binom(v,p),n_p)` is an upper bound because it may choose unused vertices. Combining it with the second-moment bound gives an exponent

`-v + sum_p (p-1)n_p + 2 alpha max(2v-d,0)`.

The inequality `(p-1)/p >= (p_m-1)/p_m` lowers this to the displayed piecewise affine function `g(d)`. On `[v,2v]` its minimum is one of the endpoints; beyond `2v` it has positive slope. The endpoint values are exactly `(2alpha-1/p_m)v` and `(p_m-2)v/p_m`. This proves the stated minimum exponent. Replacing the original exponent by the smaller one gives an upper bound because `0 < v/N <= 1`.

Only feasible edge-count vectors are subject to this estimate initially. After the estimate has been applied to each feasible vector, extending the remaining nonnegative coefficient sum to all independent nonnegative integers is valid. The exponential-series sums give exactly `C_0^v`. There is no incorrect assertion that infeasible vectors satisfy the original degree constraint.

The comparison `C_star^(kappa_alpha) >= C_0` follows from `kappa_alpha >= kappa_min > 0` and `C_0 >= 1`. At zero field only empty-boundary graphs contribute; all their used vertices have degree at least two. This yields the improved exponent `(p_m-2)/p_m` with the same constants. If `v < p_m`, there are no such nonempty support graphs, and the estimate remains valid. At `v=N`, the power of `v/N` is one, so the bound does not incorrectly claim smallness.

### Field-dependent exponent (lines 1408–1426)

Verified. For `h != 0`, `tanh h != 0`, and `N >= P >= 3` makes `log N > 0`; the formula for `alpha_h` is therefore defined. The weak-field bound gives `alpha_h >= 1/4`, including negative `h` through the absolute value. The explicit `h=0` branch avoids evaluating the logarithm at zero. The claimed crossover occurs when `2alpha-1/p_m >= (p_m-2)/p_m`, equivalently `alpha >= (p_m-1)/(2p_m)`.

For each fixed supplied `N,h`, `kappa` is constant as a function of the real variable in `Phi_N`. Consequently the derivative calculation is legitimate even though `kappa` varies across algorithmic inputs.

### Proposition `prop:higher-truncation` (lines 1428–1443)

Verified. The hypothesis `0 <= k < floor(gamma N)` ensures that the first discarded integer is within the interval on which the derivative estimate applies. Successive support sizes have an exponent increment at least two, and `1/(1-exp(-2)) < 2` proves the first term.

A remaining integer support size `v > floor(gamma N)` also satisfies `v > gamma N`. Since `v <= P |Gamma|`, the remaining family has more than `gamma N/P` edges. The real-threshold edge-tail estimate proves the second term with exponent `2 gamma N/P`. There is no floor discrepancy. If `floor(gamma N)=0`, the proposition has no permitted `k`; Section 5 handles these inputs by exact evaluation.

### Proposition `prop:pure-evaluation` (lines 1480–1529)

Verified as a finite algebraic identity for arbitrary finite real edge weights, including weights outside `[-1,1]`. Positivity is not needed for this result. Expanding the local spin average restricts graph support to `S`. Möbius inversion on the subset lattice removes all graphs except those of exact support `U`, since the inner alternating sum is `(1-1)^(|U\V(Gamma)|)`. Summing over `|U| <= k` gives the desired truncation.

For a fixed `S`, the multiplier is `sum_{j=0}^{k-s} (-1)^j binom(N-s,j)`. Because `k<N`, the partial-binomial-sum identity is valid and gives `(-1)^(k-s) binom(N-s-1,k-s)`. Its endpoint `s=k` has an empty second sum and multiplier one. At `k=0`, the formula returns `G(empty)=1`, as required. At `k=N`, the separate branch returns the full spin average and avoids an invalid negative upper binomial index.

The operation count is a conservative valid bound in the stated exact-operation model. The entire interaction list has at most `C_P (N+1)^P` entries, and scanning it per spin assignment controls membership tests, spin products, and weight lookup. Coefficient preparation by Pascal recurrence costs `O(N^2)`. Enumerating subsets of a fixed size with their vertex lists fits the claimed overhead. Summing the per-assignment bounds proves the displayed count. The separate `k=N` branch costs only `O((N+1)^(P+1) 2^N)`, which is also bounded by the proposition's larger expression.

As a supplementary check, I independently compared direct graph enumeration against direct local spin averages and these coefficients using exact rational arithmetic. Cases were `N=3` with order 3, `N=4` with orders 3 and 4, and `N=5` with order 3; field means were `0,1/3,-1/3`; all cutoffs from zero through `N` were tested. Edge weights included negative, zero, and absolute values greater than one. All 45 cutoff equalities passed. Details are in `analytic-finite-checks.json`. These finite checks supplement the algebraic audit and do not establish the general theorem by themselves.

## Section 5.1: cutoffs, exact fallback, and mean-square approximation

### Lemma `lem:cutoff-selection` (lines 2178–2224)

Verified. Both regimes have `C_star >= 1` and `kappa >= kappa_min > 0`. The displayed choice

`gamma = min(1/8, exp(-(1+2/kappa_min))/C_star)`

is strictly positive, strictly less than `1/4`, and ensures `Phi_N' >= 2` for `0 < x <= gamma N`. With `N >= N_0`, `gamma N >= 2`, so `floor(gamma N) >= gamma N/2`. The lower bound for `Phi_N(floor(gamma N))` uses monotonicity only within this valid interval.

The fixed rate `c_1` exactly matches the relevant macroscopic edge tail: `theta^(2gamma N/P)` in the higher-order case and `theta^(3gamma N)` in SK. All three quantities in the minimum defining `nu` are strictly positive. The factor `1/4` gives both `Phi_N(floor(gamma N)) >= 4 nu N` and `c_1 >= 4nu`.

On the truncation branch, `Lambda = log(C_Lambda/u)` satisfies `0 < Lambda < nu N`. Therefore the final allowed discarded index already has `Phi_N > Lambda`, so the least qualifying `k` exists and obeys `0 <= k < floor(gamma N)`. Minimality gives `Phi_N(k) < Lambda` also at `k=0`, since `Phi_N(0)=0`. The macroscopic remainder is at most `exp(-4Lambda)`, more than sufficient for the requested budget.

For any fixed `t >= 1`, the function `x log(etN/x)` has derivative `log(tN/x) >= 0` on `(0,N]`. This correctly bounds every summand by the term at `k`, and the zero summand is harmless. The decomposition

`k log(etN/k) = Phi_N(k)/kappa + k log(et C_star)`

and the positive lower bound `Phi_N(k) >= kappa_min k log(1/(C_star gamma))` yield exactly the stated `C_t`. Its numerator logarithm is positive because `t >= 1` and `C_star >= 1`. All its denominators are positive. The case `k=0` is handled separately. The search involves at most `O(N)` candidates and needs only constant work per candidate in the exact-operation model.

### Proposition `prop:mean-square` (lines 2249–2294)

Verified, with the dependency on the SK evaluator noted in the scope statement.

The cutoffs depend only on the fixed model and supplied `N,h,u`, rather than on the disorder. Thus the orthogonality estimates are not compromised by adaptive disorder-dependent selection. For higher-order mixtures the error is at most `(2+C_+) exp(-Lambda) = u/8`. For SK, `L = ceil(Lambda/log(1/theta^2))` is at least one and obeys `theta^(2(L+1)) <= exp(-Lambda)`. Also `R = ceil(exp(2L+Lambda)) >= 1` gives `exp(2L)/R <= exp(-Lambda)`. The total SK error is bounded by `(2C_SK+3C_+) exp(-Lambda) = u/8`. These stronger estimates imply the advertised upper bound `u`.

The enumeration lemma applies with fixed `t=2` and `t=36`, respectively. In the SK cost, `L <= 1 + Lambda/log(1/theta^2)` and `Lambda < nu N` imply `N+2L+1 <= C(N+1)`. Since `exp(2L+Lambda) >= 1`, its ceiling is at most twice itself. Hence `R 16^L exp(C_36 Lambda) <= C exp(C' Lambda)`, producing a polynomial in `u^(-1)` with fixed exponents. The constants may be very large near the threshold, but that is allowed by the theorem.

The exact branch is essential and correct. When `N<N_0`, the exponential `2^N` is bounded by a model-dependent constant. Otherwise the exact branch occurs only when `Lambda >= nu N`, which gives `2^N <= exp((log 2/nu)Lambda) = (C_Lambda/u)^(log 2/nu)`. Thus arbitrary requested accuracy cannot force a cost exceeding the claimed joint polynomial: the requested inverse accuracy is already exponentially large in the regime where complete enumeration is used. The equality boundary `Lambda=nu N` goes to this exact branch and is covered. Exact enumeration is also valid for SK, since the local spin-average identity is independent of the restriction to higher orders.

The final bound is pointwise in every finite input and every realization of the algorithmic colors; it does not rely on bounding the magnitudes of the supplied disorder. Elementary functions and real arithmetic are explicitly charged as exact operations, so no bit-complexity or floating-point guarantee is silently inferred.

## Section 5.2: negative moments and the disorder tail

### Lemma `lem:reverse-hypercontractivity` (lines 2312–2335)

Verified against the external source, rather than inferred from a familiar but potentially different noise convention. I accessed [Mossel–Oleszkiewicz–Sen, *On reverse hypercontractivity*, arXiv:1108.1210v5, Corollary 1.11, page 5](https://arxiv.org/pdf/1108.1210). That result applies to products of the simple resampling semigroups, to strictly positive functions, with any output exponent less than the input exponent, both less than one. Its time condition in the source's notation is `t >= log((1-q_out)/(1-p_in))`.

For one uniform sign, time `t` for the generator `Id-E` gives `exp(-t) Id + (1-exp(-t)) E`. Taking the product over coordinates is exactly the manuscript's `N_vartheta` with `exp(-t)=vartheta`. Set the manuscript's `q=1-sqrt(vartheta)` and `s=vartheta^(-1/2)-1`. Then `0<q<1`, `s>0`, and `s=q/(1-q)`. With input exponent `q` and output exponent `-s`, the source's required time is

`log((1+s)/(1-q)) = log(1/vartheta)`.

Thus the hypothesis holds with equality. Raising the resulting negative-exponent norm inequality to power `-s` reverses its direction and gives `E[(N_vartheta f)^(-s)] <= (E f^q)^(-s/q)`, exactly as claimed. There is no missing factor of two in the time convention. The sharper uniform-cube inequality is unnecessary.

The subsequent ordinary Hölder step uses conjugate exponents `2-q` and `(2-q)/(1-q)`, both greater than one. Its two factors multiply pointwise to `f`, and it yields `E f^q >= (E f^2)^(-(1-q))`. Finally `s(1-q)/q=1`, so the desired second-moment upper bound follows. Strict positivity on a finite cube ensures every negative power is finite. The dimension assumption `m>=1` is satisfied in the application since the interaction set is nonempty for `N>=P`.

### Proposition `prop:lower-tail` (lines 2348–2396)

Verified. The fixed constant `c=arctanh(theta/2)/beta_0` is strictly positive and finite. On the event `B_N`, every supplied `beta <= beta_0` satisfies `|x_e| <= beta_0 c` and therefore `|omega_e| <= theta/2`. The union bound for the complement uses exactly the thresholds and strict inequalities defining `tau_N`; no independence is needed for that union bound.

Symmetry of each real coupling allows an equality-in-law construction `J_e=epsilon_e |J_e|` with independent uniform signs independent of all magnitudes. If the original law has an atom at zero, assign an unused independent sign to it. Independence of the original coupling array means the magnitude coordinates in this construction are also independent. The event `B_N` only depends on magnitudes, so restricting to it preserves the uniform conditional sign law.

On `B_N`, each factor in the inflated sign function is at least one half; hence `f` is strictly positive. Its sign average is one because only the empty graph survives. Applying the noise to each sign monomial cancels precisely one factor `theta^(-1)` per interaction, so `N_theta f = hat Z_N` for every sign configuration. There is no inflation of the field factors or vertex count.

The conditional second moment is the sum of squared sign-Fourier coefficients. It remains a nonnegative finite quantity even outside `B_N`, although the inflated function need not be positive there. Thus it is legitimate to apply the negative-moment lemma only on `B_N`, and then remove the indicator from the nonnegative second-moment upper bound. This does not apply the negative-moment lemma outside its positivity domain.

After the indicator has been removed, independence of the magnitudes factors the edge moments. Each is `r_{N,p}/theta^2 <= bar r_{N,p}`. Proposition `prop:mass` therefore supplies exactly `C_+`. Markov's inequality for `hat Z_N^(-s) 1_{B_N}` and the union bound give `Pr(hat Z_N<z) <= C_+ z^s + tau_N` for every `z>0`. The proof is valid for unbounded disorder with only the stated second moment; it does not require a global untruncated negative moment.

## Main logarithmic guarantee and moment consequences

### Proof of `thm:finite-size` (lines 2402–2419)

Verified. Since `delta,epsilon in (0,1)`, `C_+ >= 1`, and `s>0`, the budget `z=(delta/(2C_+))^(1/s)` belongs to `(0,1)` and `u=delta epsilon^2 z^2/8` belongs to `(0,1/8)`. The mean-square algorithm is therefore called within its domain.

On `hat Z_N >= z` and `|T-hat Z_N| <= epsilon z/2`, one has `T >= z(1-epsilon/2)>0` and `|T/hat Z_N-1| <= epsilon/2 < 1/2`. The logarithmic inequality gives the claimed error. The boundary events are consistently handled: the successful event uses non-strict inequalities, and the failure terms use the matching strict inequalities.

The failure probability is bounded without any independence between `T` and `hat Z_N`: use the union bound, the lower-tail estimate, and Markov on the squared approximation error. The two numerical budgets are exactly `C_+ z^s=delta/2` and `4u/(epsilon^2 z^2)=delta/2`. The branch returning the base logarithm when `T<=0` is outside the successful event, and its contribution is already covered.

Finally,

`u^(-1)=8(2C_+)^(2/s) epsilon^(-2) delta^(-(1+2/s))`.

All powers are fixed by the model, so substitution gives a joint polynomial in `N,epsilon^(-1),delta^(-1)`. The base normalization is the exact logarithm of the factors removed from the partition function. Finite real inputs produce finite real mathematical outputs under the declared exact-arithmetic model.

### Section 1 consequence checks (lines 1018–1035)

The fourth-moment statement is correct: `t^4 Pr(|J_0|>t) <= E[|J_0|^4 1_{|J_0|>t}] -> 0`. Each order contributes `o(N^(2-p))`; in SK this is still `o(1)`, not merely `O(1)`. For higher confidence, the exponent `p-m(p-1)/2` is decreasing in `p` because the assumed `m` is strictly greater than two. Its maximum is at `p_m`, where the specified lower bound for `m` makes it at most `-b`. Thus `tau_N=o(N^(-b))` and choosing `delta=N^(-b)/2` gives the claimed eventual confidence.

For relative error, `eta=log(1+epsilon)` lies in `(0,1)` and is at least `epsilon/2`. The interval `[1/(1+epsilon),1+epsilon]` lies in `[1-epsilon,1+epsilon]`. The stated polynomial cost and the probability `1-tau_N-1/(2N)` follow. The convergence is uniform in specified parameters because the same `tau_N` bounds them all; this is not a claim of simultaneous success on one disorder event, and the manuscript explicitly distinguishes those statements.

## Defects, gaps, and exposition classified separately

### Confirmed mathematical defects

None found in the assigned sections and their inspected analytic interfaces.

### Unresolved substantive proof gaps

None found in these analytic arguments. The full Section 4 evaluator is an explicit dependency of the SK branch and is outside this report's certification. The published reverse-hypercontractive result is an explicit, verified theorem input; citing it is not a conventional-paper proof gap, but merely restating it as a Lean axiom or hypothesis would not constitute unconditional end-to-end formalization.

### Harmless conventions or exposition

- The definition of `I` at `x=±1` uses the usual continuous convention `0 log 0=0` without spelling it out. The subsequent use of `I(1)=log 2` makes the intended definition unambiguous. An explicit convention would help formalization.
- The Chernoff bound and tail-integration identity are named or written rather than separately proved. They are valid standard facts in precisely the finite-sign setting used here, including the endpoints; there is no missing probabilistic hypothesis.
- The exact fallback refers to the local average defined in the higher-order section, but its displayed formula and finite expansion apply verbatim to SK. This is an organizational observation, not a model mismatch.
- The theorem's operation model explicitly excludes bit complexity. Extremely large fixed constants, huge exact arithmetic operands, and cancellation in inclusion–exclusion do not contradict its stated guarantee. A practical finite-precision implementation would require a separate analysis.

## Formalization obligations highlighted by this audit

An unconditional formalization of these sections must connect the concrete finite-spin partition function and independent symmetric disorder variables to the graph expansion and orthogonality, prove the finite-sign entropy/Chernoff estimate and its integrated bound, establish the support-count and subset-inversion arguments, and implement the cutoff/exact-enumeration dichotomy with its actual cost model. It must also prove or import a proved product-space reverse-hypercontractive theorem and verify the sign–magnitude transport, rather than assume the negative-moment inequality or the resulting lower tail. For SK it must additionally consume a theorem establishing the actual color-coded evaluator. These are substantial proof obligations; proving only the final scalar budget inequalities would not certify the paper end to end.
