# S046 — Palomar modern-module port and submission-surface attempt (19 November 2026)

**Explicit evidence boundary:** This document records active S046 work, **not**
a public Palomar registration, official comparator pass, mathematical priority
certificate or a completed independent referee review. The owner has imposed
the strict NO PAPER until REGISTERED gate.

## Previously proved candidate

IG-P5 is the exhaustive EGU classification for graphs on at most five
vertices, with strictly positive independent Exp(rate) arrival clocks and
uniformity across *all inclusion-maximal independent sets*. The only exception
is the path P5, **up to full graph isomorphism**. The imported source theorem
`InverseGreedy.graphs_le_five_classification` is a **disjunction**. The strict
P5 non-EGU obstruction `p5Nb_not_realClockEGU`, graph-isomorphism transport,
and true n=5 iff `fin5_realClockEGU_iff_not_P5` are separate Lean proofs.
The source model uses Mathlib's genuine product exponential measure, and
`realClockEGU_iff_firstChoiceEGU` bridges it to the discrete recursion.

## Owner-controlled licence

The root `LICENSE` is Apache License, Version 2.0, explicitly chosen by the
owner on 2026-11-19. Existing owner decision commit:
`ec4edc24f9230332af7ae80d45af3377c87f9f0c`.
Metadata must truthfully declare `Apache-2.0` (now staged).

## Migration and hard results to date

Baseline main: `c073675d83b29ae3c330efd504427f58ac2be066`,
original green CI run
https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44478758381

The original proof tree comprises 95 Lean files without a modern `module`
header. Branch
https://github.com/jfairfaxball-348/Inverse-Greedy/tree/s046-modern-lean-port
holds a reproducible `experiments/s046_port_modules.py`, to mechanically
add `module`, promote `import` to `public import` and start an
`@[expose] public section`. **This is a conservative first pass, not a
semantics-preserving compiler certificate.**

- First CI migration trial (exact branch head
  `fcc403982ddffc83f9acb2a32d08c73204e19e09`):
  https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44479613803
  — module header scan succeeded; full `lake build` failed in
  `InverseGreedy/FiniteClockGapInverse.lean:131` because the public
  equivalence's proof field had unresolved metavariables.
- A narrow compatibility option `set_option backward.proofsInPublic true`
  was added before `finiteGapBinEquiv` at
  `e33cc6a92447f0a9395ec15ea44bff0c1eb4868d`.
- Second migration trial
  https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44480066802
  — Lean build progressed further, then failed in
  `InverseGreedy/SixVertexBurnsideChecks.lean` on now-inaccessible private
  permutation helper definitions; two dependent kernel Boolean checks
  consequently did not reduce.
- Replaced `private def` with ordinary exposed `def` for
  `oneEdgeSwapFirst6` and `oneEdgeSwapSecond6` on the test branch at
  `3787060034eef122fbc2ab2ce353815d54aa60b1`, with mathematical
  definitions unchanged. **The final patched migration build must still be
  checked; do not extrapolate success from prior CI.**

The test-branch workflow
`.github/workflows/s046-port.yml` performs mechanical migration in an
isolated CI checkout, checks headers, builds all imported Lean files, commits
converted sources on the branch **only after successful full Lean build**,
then compiles Challenge/Solution and invokes the official Comparator runner.
An unsuccessful build cannot auto-commit the migrated sources. Existing
research CI continues to run full Python unit tests, exact.py and n=6 census;
the static preflight is informational, not Palomar certification.

## Independently presented statement and validation gate

The branch also contains a **staged, not yet independently accepted**
`Challenge.lean` (Mathlib-only), matched `Solution.lean` importing the
pre-existing proof, `comparator.json`, `formalization.yaml` v0.4,
and `scripts/verify-comparator.sh` adapted from PalomarTemplate.

Challenge explicitly defines:
- clock comparison and stable-order real arrival times;
- sequential greedy independent-set output;
- Mathlib independent product of true exponential measures;
- all inclusion-maximal independent sets; and
- `RealClockEGU` with strictly positive real rates, and labelled P5.

The compared `PalomarEGU.graphs_le_five_iff` is the full n<=5
iff-excluding-P5 theorem, not merely the source disjunction. Solution is
meant to close that theorem using original imported Lean certification,
strict P5 non-EGU, and isomorphism transport. Its actual elaboration,
`#print axioms` and official Comparator result **must be read from exact
CI evidence before being called verified**. The Challenge contains an
intentional Palomar-style `sorry`, but the Solution must have none.

## Literature / priority boundary

The scoped S045 audit reviewed Pippenger (1989), Krivelevich et al. on
random greedy MIS, existing unequal-rate RSA examples, and the equal-rate
TreeStack predecessor. Unequal-rate RSA **predates** this project. No
matching exact five-vertex positive-rate iff was found in that targeted
search, but this does not establish novelty. A forward-citation and
editorial scope audit remains open. Palomar may regard this classification
alone as too narrow; independent editorial judgement is required.

## Required closing evidence

Any final release must record actual source `#print axioms`, official
`lake comparator` including independent kernels, complete imported
`lake build`, Python unit tests, exact computation, connected n<=6
census, static preflight, final exact 40-character SHA, dual-green push/PR
CI, full metadata/policy compliance, and public immutable source.

At this staging checkpoint: **NOT SUBMITTED / BLOCKED**, with no verified
Palomar review, entry, ID or version. Owner action is to authenticate and
approve *after* a validated public commit exists; there is currently
nothing to confirm. Preserve 90 EGU / 8 non-EGU / 45 unresolved n<=6
connected classes; all-m star-corona AEGU and 156/112 Lean orbit
exhaustiveness remain unproved.

Follow-on: `sessions/S047.md`.
