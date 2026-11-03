# S024 — The genuine exponential survival bridge (2026-11-03)

**Scope:** actual Mathlib `expMeasure` and `finiteIndependentExp` measures
at arbitrary **strictly positive real rates**, NOT an assumed finite
weighted-priority law. Formal statements are imported via
`InverseGreedy/ExpSurvival.lean`. Check `HANDOVER.md` for the exact
final CI head and merge result.

## 1. Genuine one-clock survival

Mathlib's `cdf_expMeasure_eq hr t` gives the genuine real-valued
cumulative distribution function. `ofReal_cdf` identifies its
`ENNReal.ofReal` with the **actual** measure of `Set.Iic t`.
For `t >= 0` this yields

\[
\Pr(T_r\le t)=1-e^{-rt}.
\]

For `t<0` the same genuine CDF gives
\(\Pr(T_r\le t)=0\). In particular
\(\Pr(T_r<0)=0\) (the bound at zero includes it).

The complement `Ioi t = (Iic t)ᶜ`, probability
normalisation, and `ENNReal.ofReal_sub` imply, for every
`r>0`, `t>=0`,

\[
\boxed{\Pr(T_r>t)=e^{-rt}.}
\]

There is **no** appeal to the discrete Plackett–Luce race law.
The corresponding Lean declarations are
`expMeasure_Iic_nonnegative`,
`expMeasure_Iic_negative`,
`expMeasure_Ioi_nonnegative`,
and `expMeasure_negative_time_null`.

## 2. Transport to the genuine finite independent product

S020 already proves `finiteIndependentExp_coordinate_law` for
every index `i` of a finite type, including singleton families.
Pulling back `Set.Ioi t` through the measurable projection
`Function.eval i` proves

\[
\Pr_{\otimes_j\mathrm{Exp}(r_j)}(T_i>t)=e^{-r_i t}
\quad (t\ge0).
\]

The same projection and negative support give
`finiteIndependentExp_coordinate_negative_null`.
Taking the **finite** union of these null events, then complementing
under the actual product probability measure, gives

\[
\Pr(\forall i,\ T_i\ge0)=1,
\]

including empty and singleton index types. This is
`finiteIndependentExp_all_nonnegative_probability_one`.
It supplies the support prerequisite for natural-number geometric
binning, but the bin map itself is not yet formalised.

## 3. Exact independent rational consistency tests

`tests/test_s024.py` checks four groups of `Fraction` identities
at rational exponential bin boundaries
\(\delta=-\log(1-1/n)\), positive integer rates \(r\), and
\(q=(1-1/n)^r\). It checks
\(\Pr(T>k\delta)=q^k\),
\(\Pr(T\le k\delta)=1-q^k\), the exact bin difference
\(q^k-q^{k+1}=(1-q)q^k\), finite partial sums with remainder,
and finite-coordinate product survival including the empty family.

These are **exact algebraic regressions**, not an independent formal
proof that actual continuous random variables have these probabilities.

## 4. Precisely remaining Lean gaps

- Prove a measurable floor/bin function from real clock times to
  naturals and derive exact geometric atom probabilities **from**
  the actual exponential survival formula above.
- Prove bin independence under the actual finite product, exact
  strict bin order/chamber formulas and explicit pair collision bound.
- Complete the \(\delta\downarrow0\) argument in Lean and identify
  the true two-clock event probability
  \(r/(r+s)\), then all strict finite chamber masses.
- Construct a measurable canonical sorting/greedy-output map
  and identify its pushforward with S018's weighted discrete law.

Those statements were already established **informally** in S019/S023;
this session only claims the specific imported Lean CDF/survival/support
results. Connected graph atlas unchanged at
**90 EGU / 8 non-EGU / 45 unresolved**. Independent novelty not certified.
