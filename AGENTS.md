# Agent rules — Inverse Greedy

At session start read README.md, CLAIMS.md, ROADMAP.md, HANDOVER.md,
and latest sessions/SNNN.md; inspect actual GitHub CI and branch.
Execute proofs and code, verify, commit/merge and install the next
session. Do not substitute a plan for requested execution.

Rigour:
- All rates are strictly positive; zeros or limiting rates are not EGU.
- Separate complete informal mathematical proofs, exact finite tests,
  floating-point heuristics, Lean compilation and independent novelty.
- Failing numerical optimisation is NOT a nonexistence proof;
  a tiny numerical residual is NOT an exact positive certificate.
- Bounded rational-rate enumeration does not classify all positive reals.
- C6 and P5 are obstructions as full graphs or connected components,
  NOT automatically as arbitrary induced subgraphs.
- Cograph constructive join+union closure is sufficient, not necessary;
  P4 is an EGU noncograph.
- Never confuse equal-rate predecessor results with variable-rate claim.
- Do not conflate exponential priority *times* with exponentially
  distributed maximum-weight independent-set *objective weights*.
- Formalising an algebraic rational identity is not the same as
  formalising the stochastic greedy output law.
- No production Lean sorry/admit/native_decide; verify actual CI
  build SHA before claiming the theorem is Lean checked.
- Prior art search is not a theorem novelty certificate.
- Predecessor repo is read-only. Respect concurrent GitHub updates.

Close every session with verified tests/CI, SHA, revised claim ledger,
roadmap, handover and installed next-session prompt.

- Atlas regression snapshots are part of test semantics. New census
  classifiers must have an include_sNNN flag or update earlier
  snapshots explicitly; S006/S007 require include_s009=False.
