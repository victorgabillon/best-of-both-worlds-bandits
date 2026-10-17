# Manuscript-to-Lean theorem map

This map covers **six principal named results**: Theorems 1, 2, 4, 6, Corollary 7, and Lemma 10. Theorem 6 has two bounds. All declaration names below are exact; shorter mathematical formulas explain, rather than replace, their full Lean types. The frozen mathematical baseline is identified by `verification/manuscript-baseline.json`. The included E3 editorial version is in [paper/source/](../paper/source/); [MANUSCRIPT_FIDELITY.md](MANUSCRIPT_FIDELITY.md) verifies that its principal statements preserve that baseline. Source filenames below refer to that directory.

For a full source-build, endpoint-axiom audit, and 57-module kernel replay, run:

```sh
./scripts/verify.sh
```

For the transitive axiom audit after the build, run `./scripts/verify.sh --phase axioms --skip-prepare`. Its generated `AuditEndpoints.lean` and logs contain fully elaborated types and explicit `#print axioms` output for 19 principal endpoint/variant declarations. Each result below also gives an individual source-build command; that command alone is not the full release verification.

## Notation and models

Let $K\ge2$ be the number of arms and $n$ the horizon. `Fin K` represents labels/ranks with zero-based values; paper rank $r$ is represented by value $r-1$. Used round $t$ in the paper corresponds to Lean value $t-1$ in `Fin n`. A fixed table is supplied as `g : ℕ → Fin K → ℝ`; only its first $n$ rows matter.

A uniquely best arm has a strictly greater total reward (adversarial case) or mean (stochastic case) than every competitor. The best arm is assigned the smallest competitor gap, so the ordered profile satisfies $0<\Delta_1=\Delta_2\le\cdots\le\Delta_K$. Equal suboptimal gaps are allowed. The definitions in [GapComplexity.lean](../BestOfBothWorlds/GapComplexity.lean) are

$$H_{\rm UNIF}=K/\Delta_1^2,\qquad H_{\rm SR}=\max_{1\le r\le K}r/\Delta_r^2,\qquad H_{\rm BOB}=\Delta_1^{-1}\max_{1\le r\le K}r/\Delta_r.$$

Write $L_K=\bar{\log}K=\sum_{r=1}^K1/r$; it is the exact harmonic sum, not the natural logarithm. Adversarial upper-bound complexities use the actual table's average reward gaps. Lower-bound reference complexities use the supplied reference profile, except that Theorem 4 explicitly uses the constructed stochastic instance's actual complexity.

For lower bounds, $\mathcal D_c$ is the manuscript's **labelled** gap class. Given a reference profile, one exceptional arm label has actual gap in $[\Delta_1/c,c\Delta_1]$; every other label $j$ retains actual gap in $[\Delta_j/c,c\Delta_j]$. Deterministic membership also includes bounded table entries and a uniquely best realized arm. See [LowerBoundGapClasses.lean](../BestOfBothWorlds/LowerBoundGapClasses.lean). This class is not simply a coordinatewise comparison after independently re-sorting both profiles.

**Upper learner model.** [AdaptiveBanditProcess.lean](../BestOfBothWorlds/AdaptiveBanditProcess.lean) constructs the actual trajectory law from measurable conditional action probabilities on observed history, with strict positivity and normalization. UNIF and P1 are concrete policies. Stochastic reward vectors are fresh independent draws from a fixed real-vector probability measure $\nu$, with every coordinate in $[0,1]$ almost surely. Coordinates within one vector may be dependent; finite support or Bernoulli rewards are not assumed. Fixed adversarial tables instead use Dirac row laws. Error is the probability that the actual recommendation differs from the actual best arm; stochastic error includes reward and action randomness.

**Lower learner model.** [SeededLearner.lean](../BestOfBothWorlds/SeededLearner.lean) gives an arbitrary measurable private-seed type, probability law $\rho$, actions depending on that same seed and strictly previous observed action/reward pairs, and a recommendation using the seed and complete observed history. Measurability in the seed is required for every fixed history. The seed is independent of the pre-drawn table. This permits persistent state, random recommendations, deterministic learners, and zero action probabilities. The final lower bounds quantify over real-history learners, then restrict them to the finite real reward supports with proved interaction/law agreement. No representation theorem for every abstract stochastic kernel on unrestricted measurable spaces is claimed. The lower-bound tables are **oblivious**, fixed before interaction; the learner is adaptive.

## Theorem 1 — UNIF adversarial upper bound

**Manuscript:** `upLowGenAd.tex`, label `th:UPARU`; proof `appUpperUniform.tex`.

For every $K\ge2$, horizon $n$, and fixed table $g$ bounded in $[0,1]$ on the used rounds, with a unique cumulative-reward best arm,

$$e_{\rm UNIF}(g,n)\le K\exp\!\left(-\frac{3n}{28H_{\rm UNIF}(g)}\right).$$

The errors use fresh uniform sampling, cumulative importance-weighted estimates, and the smallest-index estimated maximizer. Gaps and complexity come from this actual table, not a reward mean. The statement has no extra explicit $n>0$ premise; its unique-best assumption implies it.

**Lean:** `BestOfBothWorlds.UniformAdversarialBound.unif_adversarial_error_bound` in [UniformAdversarialBound.lean](../BestOfBothWorlds/UniformAdversarialBound.lean).

**Build:** `lake build BestOfBothWorlds.UniformAdversarialBound`. Exact constants: prefactor $K$, exponent $3/28$.

## Theorem 2 — adversarial lower bound

**Manuscript:** `upLowGenAd.tex`, label `th:LOWadPRO`; proof `appLOWAd.tex`.

Fix $K\ge4096$, reference gaps $0<\Delta_1=\Delta_2\le\cdots\le\Delta_K\le1/8$, and a horizon satisfying

$$K\exp(-n\Delta_1^2/128)\le1/128.$$

For every real-history private-seed learner and every probability seed law, there exist two fixed tables $g_1,g_2\in\mathcal D_3$, with different actual best arms, such that

$$\max\{e(g_1,n),e(g_2,n)\}\ge\min\!\left\{\frac1{128}\exp\!\left(-\frac{32n}{H_{\rm UNIF}(\Delta)}\right),\frac1{32}\right\}.$$

Witnesses may depend on the learner and horizon, but not on the seed subsequently sampled. Their errors average only the learner's seed for each fixed table. $H_{\rm UNIF}(\Delta)$ is the **reference** complexity. Odd horizons are allowed. Lean also carries the redundant $K\ge2$ hypothesis explicitly.

**Lean:** `BestOfBothWorlds.LowerBounds.adversarial_lower_bound` in [AdversarialLowerBound.lean](../BestOfBothWorlds/AdversarialLowerBound.lean).

**Build:** `lake build BestOfBothWorlds.AdversarialLowerBound`. Exact constants: $4096$, $1/8$, horizon $128$ and $1/128$, exponent $32$, prefactor $1/128$, cap $1/32$, class factor $3$.

## Theorem 4 — conditional best-of-both-worlds lower bound

**Manuscript:** `lowerBoundBOB.tex`, label `th:lowBOB`; proof `appLOWBOB.tex`.

Fix $K\ge2$, reference gaps $0<\Delta_1=\Delta_2\le\cdots\le\Delta_K\le1/8$, and $n>0$ with

$$K\exp(-n\Delta_1^2/128)\le1/32.$$

For every real-history private-seed learner and probability seed law, **there exists an i.i.d. stochastic instance** $S\in\mathcal D_4$ with a strict mean-best arm such that

$$e(S,n)\le\frac1{64}\exp\!\left(-\frac{2048n}{H_{\rm BOB}^{S}}\right)
\quad\Longrightarrow\quad
\exists g\in\mathcal D_4:\ e(g,n)\ge\frac1{16}.$$

Here $g$ is a deterministic bounded table, and $H_{\rm BOB}^{S}$ uses the **actual sorted mean gaps of the constructed stochastic instance**, not BASE/reference gaps. Both witnesses may depend on the learner and $n$. The stochastic witness exists outside the implication; the adversarial witness is required only if its small stochastic-error premise holds. This is not an unconditional claim that every learner must have constant adversarial error, nor one fixed stochastic witness uniform over all horizons.

**Lean:** `BestOfBothWorlds.LowerBounds.BOBLowerBound.theorem4` in [BOBLowerBound.lean](../BestOfBothWorlds/BOBLowerBound.lean). The conclusion additionally exposes stationarity, strict best means, and actual class membership. `stoComplexity_eq_actual_real` proves the complexity bridge to the actual real reward laws.

**Build:** `lake build BestOfBothWorlds.BOBLowerBound`. Exact constants: class factor $4$, gap cap $1/8$, horizon denominator $128$ and threshold $1/32$, stochastic exponent $2048$ and prefactor $1/64$, adversarial error $1/16$.

## Theorem 6 — P1 stochastic upper bound

**Manuscript:** `upperBoundBOB.tex`, label `th:UpBOB`; proof `appUPPBOB.tex`.

For $K\ge2$, every bounded real-vector probability law $\nu$ with a unique mean-best arm, and every positive integer $n$, the actual P1 recommendation satisfies

$$e_{\rm P1}(\nu,n)\le2K^3n\exp\!\left(-\frac{n}{128H_{\rm P1}}\right).$$

For clarity, $H_{\rm P1}$ is the exact attained minimum over integer analysis schedules $n_1=n_2=n\ge n_3\ge\cdots\ge n_K>0$. Writing $a_r=n_r/n$ and $a_{K+1}=0$,

$$H_{\rm P1}=\min_a L_K\max_{1\le r\le K}
\frac{\sum_{i=r}^K i(a_i-a_{i+1})+(K/24)a_r\Delta_r}{a_r^2\Delta_r^2}.$$

Coincident comparison times are allowed. [P1Complexity.lean](../BestOfBothWorlds/P1Complexity.lean) defines the finite minimum and proves its attainment and equality with the manuscript's expression. No schedule, mean, or gap is an algorithm input or an unproved final premise. Reward vectors are i.i.d. across rounds; within-round coordinate correlation is permitted.

**Lean:** `BestOfBothWorlds.P1StochasticBound.p1_stochastic_error_bound` in [P1StochasticBound.lean](../BestOfBothWorlds/P1StochasticBound.lean).

**Build:** `lake build BestOfBothWorlds.P1StochasticBound`. Exact constants: $2K^3n$, denominator $128H_{\rm P1}$, and $1/24$ in the complexity.

## Theorem 6 — P1 adversarial upper bound

For every $K\ge2$, horizon $n$, and bounded fixed table $g$ with a unique realized best arm, the **same concrete P1 policy and recommendation** satisfy

$$e_{\rm P1}(g,n)\le K\exp\!\left(-\frac{3n}{40L_KH_{\rm UNIF}(g)}\right).$$

This error uses action randomness for the fixed table, and its complexity uses actual cumulative-average gaps. Unique best again implies $n>0$. The proved stronger $3/28$ variant is additional; the endpoint below retains the corrected manuscript's exact $3/40$.

**Lean:** `BestOfBothWorlds.P1AdversarialBound.p1_adversarial_error_bound` in [P1AdversarialBound.lean](../BestOfBothWorlds/P1AdversarialBound.lean).

**Build:** `lake build BestOfBothWorlds.P1AdversarialBound`. Exact constants: prefactor $K$, exponent $3/40$, harmonic factor $L_K$.

The combined endpoint `BestOfBothWorlds.P1UpperBounds.p1_upper_bounds` in [P1UpperBounds.lean](../BestOfBothWorlds/P1UpperBounds.lean) proves both guarantees as a conjunction. Build it with `lake build BestOfBothWorlds.P1UpperBounds`. Each separate endpoint requires only its own environment's assumptions.

## Corollary 7 — stochastic BOB-complexity guarantee

**Manuscript:** `upperBoundBOB.tex`, label `coco`; proof and rounded-schedule discussion in `appUPPBOB.tex`.

Under the stochastic assumptions of Theorem 6:

$$n\ge\Delta_K/\Delta_1\quad\Longrightarrow\quad H_{\rm P1}\le2H_{\rm BOB}L_K^2.$$

For **every positive integer** $n$, including smaller horizons,

$$e_{\rm P1}(\nu,n)\le2K^3n\exp\!\left(-\frac{n}{256H_{\rm BOB}L_K^2}\right).$$

The first assertion requires the gap-ratio horizon condition; the probability assertion does not. At unsupported short horizons, the proof shows the displayed probability bound is at least one. All gaps/complexities use the actual stochastic means.

**Lean:** `BestOfBothWorlds.P1Corollary.p1_complexity_le_bob` and `BestOfBothWorlds.P1Corollary.p1_stochastic_bob_error_bound` in [P1Corollary.lean](../BestOfBothWorlds/P1Corollary.lean).

**Build:** `lake build BestOfBothWorlds.P1Corollary`. Exact constants: complexity factor $2$, probability prefactor $2K^3n$, denominator $256H_{\rm BOB}L_K^2$.

## Lemma 10 — observed-transcript change of measure

**Manuscript:** `appTechLem.tex`, label `l:transcriptChangeMeas`.

Fix one arm $k$ and a deterministic set of informative rounds $T$ before interaction. Two independent-entry table laws differ only at $(k,t)$ for $t\in T$, where their rewards are Bernoulli$(u)$ and Bernoulli$(v)$ with $u,v\in(0,1)$. Elsewhere entry laws are common arbitrary finite-support probability laws, possibly deterministic or dependent on arm/round. The table is independent of the learner's private seed. The observed transcript contains all selected arm/reward pairs **and the final recommendation**, not unobserved entries.

For the same private-seed learner, let $P_A,P_B$ be its actual transcript laws, $N_k(T)$ the number of informative pulls, and $I=\mathbb E_A[N_k(T)]\operatorname{kl}(u,v)$. Then:

1. $P_A$ and $P_B$ have common support, including zero-mass atoms.
2. On positive transcript support, the log likelihood is the sum over actual informative pulls of $\log(u/v)$ for reward one and $\log((1-u)/(1-v))$ for reward zero. Thus $D(P_A\Vert P_B)=I$; the actual Mathlib KL is finite and equals `ENNReal.ofReal I`.
3. For every observed-transcript event $W$, put $p=P_A(W)$ and $q=P_B(W)$. If $0<q<1$, then $\operatorname{kl}(p,q)\le I$ and $p\log(1/q)\le I+\log2$. If $q=0$, then $p=0$; if $q=1$, then $p=1$.
4. $P_A(W^c)+P_B(W)\ge\tfrac12\exp(-I)$, also for empty/full events.

The manuscript uses $K\ge2$ and $n>0$; the Lean lemma family needs only the finite horizon/arm parameters and designated arm to be defined, so it also handles zero horizons when those parameters make sense. It has no gap or unique-best assumption. The finite measurable reward alphabet has measurable singletons (hence every subset is measurable) and may contain nonbinary values. Lean allows any two distinct designated reward values; choosing actual real values $1,0$ includes the manuscript's Bernoulli instances. Neither a finite seed nor positive action probabilities are assumed. The informative set can be empty/full and $u=v$ is allowed. The event inequalities do not apply directly to unobserved full-table good events.

**Lean namespace:** `BestOfBothWorlds.SeededChangeOfMeasure`.

| Part | Exact declaration suffixes | Source |
| --- | --- | --- |
| Common support | `lemma10_common_support`, `lemma10_positive_support` | [SeededChangeOfMeasure.lean](../BestOfBothWorlds/SeededChangeOfMeasure.lean) |
| Pointwise log likelihood | `lemma10_log_likelihood` | [SeededInformativeLikelihood.lean](../BestOfBothWorlds/SeededInformativeLikelihood.lean) |
| KL identity and finite-value bridges | `lemma10_kl_identity`, `lemma10_kl_ne_top`, `lemma10_kl_eq_ofReal`, `lemma10_toReal_kl_identity` | [SeededChangeOfMeasure.lean](../BestOfBothWorlds/SeededChangeOfMeasure.lean) |
| Event bounds and endpoints | `lemma10_event_binaryKL`, `lemma10_event_log`, `lemma10_event_zero`, `lemma10_event_one` | [SeededChangeOfMeasure.lean](../BestOfBothWorlds/SeededChangeOfMeasure.lean) |
| Testing | `lemma10_testing` | [SeededChangeOfMeasure.lean](../BestOfBothWorlds/SeededChangeOfMeasure.lean) |

**Build:** `lake build BestOfBothWorlds.SeededInformativeLikelihood` (includes `SeededChangeOfMeasure`). Exact constants: additive $\log2$ and testing factor $1/2$; the KL identity itself is exact.

## Limits of the composed claim

Every listed principal statement has its own certificate. The audit did not locate a general Lean equality between the upper stochastic gap interface and the lower real-mean sorted-profile interface, or a private-seed implementation of P1 proved law-equivalent to its upper kernel process. Do not claim that these interfaces have already been mechanically composed. General kernel-representation and universal arbitrary tie-breaking claims are also outside the certificate. The actual fixed tie convention is smallest-index; suboptimal reward/mean ties remain allowed.
