# S020 — Finite independent exponential-clock model

Let I be any finite index type (including the empty type) and
r : I → ℝ satisfy r(i)>0 for every i. Define on Ω=(I→ℝ)

    μ = Measure.pi (fun i => expMeasure (r i)).

This uses Mathlib's actual finite product of real exponential measures;
it is not a construction from a discrete order distribution.
`Measure.pi.instIsProbabilityMeasure` shows μ(Ω)=1, including I=∅.
`measurePreserving_eval` identifies the distribution of coordinate
T_i(ω)=ω(i) as exactly `expMeasure (r i)`.
`iIndepFun_pi` proves the entire family of coordinate clocks is
jointly independent, rather than just pairwise independent.
Using `Measure.pi_eval_preimage_null` and the S019 exponential
singleton-null lemma, for every i∈I and t∈ℝ:

    μ({ω : ω(i)=t}) = 0.

Proof module: `InverseGreedy/FiniteIndependentExp.lean`. These facts
are Lean-verified **only if** the exact imported Lean GitHub Actions
build at the listed SHA passes; verify `CLAIMS.md` and `HANDOVER.md`.

The single-coordinate cylinder-null property does not by itself prove
that *two different* coordinates cannot tie. For finite sorting,
the next tasks are pairwise no-tie events, their finite union,
measurable sorting with a deterministic tie-break, and the probability
of every strict ordering chamber. Independently, the two-clock
unequal-rate comparison formula r/(r+s) still requires a continuous
integral proof in Lean.

The S018 equality for the *discrete* weighted priority output law is
separate, and is not evidence that the continuous sorting pushforward
has been formalised.

No atlas change: 90 EGU / 8 non-EGU / 45 unresolved.
