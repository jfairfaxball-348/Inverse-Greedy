# S028 — Actual exponential ceiling-bin geometric evaluation

**Research date:** 2026-11-03

## Mathematical objects and source

Fix arbitrary strictly positive real rates \(r,s\) and bin width
\(\delta\). Let \((T_r,T_s)\) have the actual independent product
\(\operatorname{Exp}(r)\otimes\operatorname{Exp}(s)\) formalised as
`independentExpPair r s`; the ceiling-bin map is the **measurable**
`clockCeilBin δ t = Nat.ceil (t/δ)`. S027 has already proved in Lean
the countable measure identities for the genuine sets of strict-bin
winners and same-bin collisions, including null exceptional zero bins.

Put \(q_r=e^{-r\delta}\), \(q_s=e^{-s\delta}\). Because the three
parameters are positive, \(0<q_r,q_s<1\). The genuine positive-bin
collision cylinder \(D_k=\{K_\delta(T_r)=K_\delta(T_s)=k+1\}\)
has probability

\[
 \Pr(D_k)=(1-q_r)(1-q_s)(q_rq_s)^k.
\]

The cells are measurable and pairwise disjoint, and the zero-bin
exception has measure zero. Applying S027's countable additivity **to
the real-clock product**, and then ENNReal geometric summation, gives

\[
 \Pr(K_\delta(T_r)=K_\delta(T_s))=
 \frac{(1-q_r)(1-q_s)}{1-q_rq_s}.
\]

The independent ENNReal identity used for this step is

\[
 \sum_{k\ge0}(a x^k)(b y^k)
   =ab(1-xy)^{-1}
 \qquad(a,b,x,y\in[0,\infty]).
\]

It is valid even outside the convergent geometric regime under
ENNReal's extended conventions, and makes no probability assumptions.

**Formal status:** `InverseGreedy/BinnedRaceGeometric.lean`
was added to the imported Lean build and is subject to exact-head
CI. Until that CI is green, the new Lean claims are **unverified**.
Do not interpret a source-level declaration as a checked theorem.

## Further geometric evaluation and limit (mathematical derivation)

The S027 true strict-bin winner series similarly evaluates to

\[
 W_\delta=
 \Pr(K_\delta(T_r)<K_\delta(T_s))
 =\frac{(1-q_r)q_s}{1-q_rq_s}.
\]

The reverse winner has probability
\((1-q_s)q_r/(1-q_rq_s)\). These three disjoint
measurable outcomes sum to one. If a real strict winner does not
occupy a strictly earlier bin, the two clocks must be in the same
bin (the exceptional zero-bin event is null). Consequently

\[
 W_\delta\le\Pr(T_r<T_s)\le W_\delta+C_\delta,
 \quad
 C_\delta=\frac{(1-q_r)(1-q_s)}{1-q_rq_s}.
\]

Because \(1-q_rq_s\ge 1-q_r\) and
\(1-q_rq_s\ge1-q_s\), one has the explicit bound

\[
 C_\delta\le \min(1-q_r,1-q_s)
 \le \delta\min(r,s).
\]

Taking \(\delta\downarrow0\) gives \(W_\delta\to r/(r+s)\)
and \(C_\delta\to0\), therefore the continuous rate ratio
\(\Pr(T_r<T_s)=r/(r+s)\).

More sharply, direct one-sided analytic expansion gives

\[
 \lim_{\delta\downarrow0}
  \frac{r/(r+s)-W_\delta}{\delta}
 =\frac{rs}{2(r+s)},\qquad
 \lim_{\delta\downarrow0}
  \frac{C_\delta}{\delta}
 =\frac{rs}{r+s}.
\]

`tests/test_s028.py` checks both symbolic derivatives, plus exact
rational three-way bin sums, tails and error enclosures. These
checks **do not formalise the limit or continuous race law**.

## Outstanding proof obligations

1. Verify, at the exact imported Lean head, the actual collision
   geometric evaluation above.
2. Evaluate the actual strict-bin winner series, and transport both
   ENNReal expressions to the real fractions.
3. Formalise the strict-bin/continuous comparison sandwich,
   collision bound and zero-width limit, to obtain the unequal-rate
   true exponential winner probability as an imported Lean theorem.
4. General finite sorting-chamber probabilities and the canonical
   measurable sorted-clock-to-greedy pushforward remain distinct.

Do not confuse these obligations with the already completed S018
discrete weighted greedy-output law. Preserve the connected n<=6
census: 90 EGU / 8 non-EGU / 45 unresolved. No independent
mathematical novelty is claimed.
