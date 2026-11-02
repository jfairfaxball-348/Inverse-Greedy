# S022 — Finite continuous exponential clocks do not tie

**Scope.** This session addresses an actual measure-level finite-product
obligation from S022, rather than assuming the finite clock order already
has the discrete Plackett–Luce law. The numerical unequal-rate race ratio
and full finite sorting-chamber law remain **open in Lean**.

## 1. Pair marginals of the actual finite product

Let \(I\) be any finite index type, \(r_i>0\), and
\(\mu_I=\bigotimes_{i\in I}\operatorname{Exp}(r_i)\) be the **genuine**
Mathlib `Measure.pi` from S020. For any distinct \(i,j\in I\),
S020's `iIndepFun` theorem yields independence of
\(X_i(\omega)=\omega_i\) and \(X_j(\omega)=\omega_j\).
The established S020 coordinate-marginal theorem identifies both
laws with their actual `expMeasure`s. Hence

\[
(X_i,X_j)_*\mu_I
 =\operatorname{Exp}(r_i)\otimes\operatorname{Exp}(r_j).
\]

The new Lean theorem is `finiteIndependentExp_pair_law`. It uses
`iIndepFun.indepFun`,
`IndepFun.map_prod_eq_prod_map_map`, and the coordinate-law theorem.
No unproved independence hypothesis is inserted.

## 2. Nullity of the pairwise and global tie events

The diagonal \(D=\{(x,y):x=y\}\) has zero measure under any two
positive-rate independent exponential coordinates by S019
`independentExpPair_no_ties`, using the density and null singletons.
Pulling back through the **proved pair law** gives, for \(i\ne j\),

\[
\mu_I\{\omega:X_i(\omega)=X_j(\omega)\}=0.
\]

Since \(I\) is finite, a union over all distinct ordered pairs is a
finite union of null sets:

\[
\mu_I\{\omega:\exists i\ne j,\ X_i(\omega)=X_j(\omega)\}=0.
\]

The complement is a measurable event by the S021 result. Using
probability normalization yields

\[
\mu_I\{\omega:\forall i\ne j,\ X_i(\omega)\ne X_j(\omega)\}=1.
\]

The Lean declarations are
`finiteIndependentExp_pair_tie_null`,
`finiteIndependentExp_any_tie_null` and
`finiteIndependentExp_pairwise_distinct_probability_one`.
All statements include the **empty** and **singleton** index types:
the set of distinct-index ties is empty and the all-distinct condition
is vacuously true. Strict positivity is retained throughout.

## 3. Independent exact rational bin oracle

For a separate regression of genuine continuous clocks, take *integer*
rates \(r,s>0\), \(n\ge2\), and a bin width
\(\delta=-\log(1-1/n)\). Define \(B_i=\lfloor T_i/\delta\rfloor\).
The exponential survival law gives the geometric bin distribution

\[
\Pr(B_i=k)=(1-q_i)q_i^k,\qquad
q_i=e^{-r_i\delta}=(1-1/n)^{r_i}\in\mathbb Q.
\]

By independence and geometric-series summation, the **exact** rational
three-way binned comparison probabilities are

\[
\Pr(B_r<B_s)=\frac{(1-q_r)q_s}{1-q_r q_s},
\quad
\Pr(B_s<B_r)=\frac{(1-q_s)q_r}{1-q_r q_s},
\quad
\Pr(B_r=B_s)=\frac{(1-q_r)(1-q_s)}{1-q_r q_s}.
\]

These sum to one identically. Moreover

\[
\Pr(B_r=B_s)\le \min(1-q_r,1-q_s)
 \le\frac{\min(r,s)}{n},
\]

because \(1-(1-1/n)^k\le k/n\) for integer \(k\ge1\).
This is an explicit elementary proof of vanishing bin collisions
(as \(n\to\infty\)) for positive **integer** rates.

More generally, for arbitrary positive **real** rates and \(\delta\to0\),
the strict-bin formula above tends to \(r/(r+s)\), by
\((1-e^{-r\delta})/\delta\to r\).
For distinct continuous clock times, a sufficiently fine binning
preserves their strict order. This gives an alternative **informal**
proof of the actual unequal-rate comparison probability without
importing the discrete `firstChoice` theorem. It is **not** a
Lean formalisation of that numerical result.

`tests/test_s022.py` calculates these binned probabilities as
`fractions.Fraction` for integer rates and checks exact partition,
rate-swap, collision bounds and convergence regression. Unlike a
finite numerical quadrature, its finite-n results are exact.

## 4. Formal proof boundary and next steps

This session's proposed imported Lean theorem establishes that all
actual finite products have almost surely distinct clocks. It **does
not** prove either the two-clock formula \(r/(r+s)\) as a Lean
measure identity, a measurable tie-broken sorting map, or
probabilities of arbitrary strict chambers. The S018 discrete greedy
pushforward cannot be applied to continuous clocks until a true
finite-chamber equality is proved.

The S022 source was initially built on the PR branch; refer to
`HANDOVER.md` for the **exact final CI SHA and status** rather than
interpreting this document as a successful build certificate.

No new EGU graph classification or novelty claim: 90 EGU, 8 non-EGU,
45 unresolved connected graphs through six vertices.
