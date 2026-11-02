# S023 — Exact geometric-bin chambers and a finite-clock bridge

**Status:** complete informal proof for all positive real rates; exact
rational Python regression for integer rates; Lean only proves the
measurability of the strict-chamber events **if imported CI is green**.
The arbitrary-real chamber probabilities and true continuous sorting
pushforward are **not** asserted as Lean results.

## 1. The genuine clocks and their bins

Let (I) be a finite set, with independent genuinely exponential clocks
(T_i\sim\mathrm{Exp}(\lambda_i)), (\lambda_i>0), on S020's
product sample space. Choose any real bin width (\delta>0), set

\[
B_i=\lfloor T_i/\delta\rfloor,\qquad
q_i=e^{-\lambda_i\delta}\in(0,1).
\]

The actual exponential survival function and independence imply

\[
\mathbb P(B_i=k)=(1-q_i)q_i^k\quad(k\ge0).
\]

This calculation uses no weighted-priority law. It needs only the
exponential survival formula, finite product independence, and the
fact that exponential clocks are nonnegative almost surely. For an
ordered list of **all** vertices (\pi=(\pi_1,\ldots,\pi_m)), let
(F_{\pi,\delta}={B_{\pi_1}<\cdots<B_{\pi_m}}).
Set (Q_j=\prod_{k=j}^m q_{\pi_k}). Then the **exact** probability is

\[
\boxed{\quad
\mathbb P(F_{\pi,\delta})
=\frac{\prod_{j=1}^m(1-q_{\pi_j})}
       {\prod_{j=1}^m(1-Q_j)}
  \prod_{j=2}^m Q_j.\quad}
\]

For (m=0) the event is certain, with probability 1, as every
empty product equals 1. For (m=1) the formula also gives 1.

**Proof by geometric gaps.** Write
(k_j=B_{\pi_j}\) and, when the bins are in strict order,
(k_1=d_1\ge0), (k_j=k_{j-1}+1+d_j) for (j\ge2), (d_j\ge0).
Independence gives, for one configuration,

\[
\prod_{j=1}^m(1-q_{\pi_j})q_{\pi_j}^{k_j}
= \left(\prod_{j=1}^m(1-q_{\pi_j})\right)
 Q_1^{d_1}\prod_{j=2}^m Q_j^{1+d_j}.
\]

Sum separately over all (d_j\ge0) using
(\sum_{d\ge0}Q^d=(1-Q)^{-1}), justified because
each (Q_j\in(0,1)). The boxed expression follows.

**Independent first-bin calculation.** The event that clock (\pi_1)
is the unique smallest **bin** (strictly before all other bins)
has probability

\[
\frac{(1-q_{\pi_1})\prod_{j=2}^m q_{\pi_j}}
     {1-\prod_{j=1}^m q_{\pi_j}}.
\]

Conditional on that event, the shifted remaining bin indices are
independent geometric variables with the original (q_i), by the
memorylessness of geometric survival. Multiplying this first-bin
factor recursively gives the same strict-chamber expression.
The Python test implements the gaps and the first-bin calculation
independently, using exact `Fraction` arithmetic.

## 2. Quantitative collision bound and true-chamber sandwich

For two distinct clocks, the probability of landing in the same
**bin** is exactly

\[
c_{ij}(\delta)
=\frac{(1-q_i)(1-q_j)}{1-q_iq_j}
\le\min(1-q_i,1-q_j)
\le\delta\min(\lambda_i,\lambda_j).
\]

The first bound follows from (1-q_iq_j\ge1-q_i) and
(1-q_iq_j\ge1-q_j). The second uses (1-e^{-x}\le x)
for (x\ge0). Therefore the finite union bound gives

\[
\mathbb P(\text{at least one bin collision})
\le\delta\sum_{\{i,j\}\subset I}\min(\lambda_i,\lambda_j).
\]

Let (E_\pi={T_{\pi_1}<\cdots<T_{\pi_m}\}) be the actual
strict real-clock chamber. Since the floor map preserves strict
bin order, (F_{\pi,\delta}\subseteq E_\pi).
If **no** bin collision occurs, the strict clock ordering and the
strict bin ordering coincide. Consequently

\[
\boxed{0\le\mathbb P(E_\pi)-\mathbb P(F_{\pi,\delta})
\le\delta\sum_{i<j}\min(\lambda_i,\lambda_j).}
\]

This bound is simultaneous for **all** permutations and is valid
for **all positive real rates**. It does not assume that the
continuous sorted-order distribution is already Plackett–Luce.

## 3. Taking the genuine real-clock limit

As (\delta\downarrow0),

\[
\frac{1-q_{\pi_j}}{1-Q_j}
=\frac{1-e^{-\lambda_{\pi_j}\delta}}
       {1-e^{-(\sum_{k=j}^m\lambda_{\pi_k})\delta}}
\longrightarrow
\frac{\lambda_{\pi_j}}{\sum_{k=j}^m\lambda_{\pi_k}},
\qquad Q_j\longrightarrow1.
\]

All tail sums are positive. Hence the boxed finite-bin product
converges to (\prod_j\lambda_{\pi_j}/\sum_{k=j}^m\lambda_{\pi_k}),
and the explicit collision sandwich forces

\[
\boxed{\mathbb P(E_\pi)=
\prod_{j=1}^m
\frac{\lambda_{\pi_j}}{\sum_{k=j}^m\lambda_{\pi_k}}.}
\]

This proves the genuine continuous exponential ordering law
**mathematically** without a multivariable density integral.
In particular the two-clock case is
`P(T_r<T_s)=r/(r+s)`.
This is an alternative informal proof of IG-P11 (already proved
on paper by the spacings/density argument in S019), not a novel
classification claim.

A direct Lean path is now: formalise real exponential tails;
derive geometric-bin probabilities by `Measure.pi` cylinder
independence; prove geometric sums and the pair collision
bound; take (\delta\to0) using the explicit finite product
formula; identify S023's measurable `strictClockChamber` with
the strict bin event up to the bounded collision set. The final
step into S018's discrete greedy-output pushforward remains a
separate Lean task.

## 4. Exact rational regression

For positive **integer** rates (a_i) and (n\ge2), choose
(\delta=-\log(1-1/n)). Then
(q_i=(1-1/n)^{a_i}\in\mathbb Q) and every finite-bin
chamber probability above is rational. The pair collision satisfies
the sharper entirely rational bound

\[
c_{ij}\le 1-q_i\ \text{and}\ \le 1-q_j
\le\frac{\min(a_i,a_j)}{n},
\]

using Bernoulli's inequality ((1-1/n)^a\ge1-a/n).
Therefore all true chamber probabilities lie in exact rational
intervals
`[strict_bin_chamber, strict_bin_chamber + collision_bound]`.
These enclosures are mathematically justified for genuine
continuous clocks; they do not rely on finite-rate enumeration.

`tests/test_s023.py` independently implements the geometric-gap
formula and the memoryless first-bin recursion, checks their
equality across all permutations up to five vertices, checks
the exact rational enclosures against the known analytical
product, and cross-checks S022's two-clock exact bin oracle.
No float comparisons are used.

## 5. Formal and research status

- S022 **Lean-verified:** genuine independent exponential finite
  product, pair marginals and a.s. no ties.
- S023 proposed **Lean contribution:** measurability of arbitrary
  finite strict clock chambers via finite intersections of
  coordinate inequalities. Inspect the actual imported CI SHA.
- S023 **complete informal proof:** exact geometric-bin chamber law
  and its real-clock limit for every finite set of positive real
  rates, with an explicit nonasymptotic collision error.
- **Open in Lean:** true exponential survival/cylinder
  probabilities; numerical (r/(r+s)); complete chamber masses;
  measurable canonical sorting and end-to-end real-clock greedy
  pushforward.

The connected n≤6 EGU atlas remains **90 / 8 / 45** and there is
no independent novelty certificate.
