# S014 handover — 2026-10-31

## S014 work (PR #13)

Branch: `s014-weighted-projection`.
PR: https://github.com/jfairfaxball-348/Inverse-Greedy/pull/13

**New S014 structural result:** InverseGreedy/ProjectedOrderLaw.lean
defines weighted full permutation mass for the event that filtering
an entire order to a retained set yields a target list. It proves
an exact first-head equation distinguishing whether the first vertex
is retained (and therefore must match target head) or discarded.
This is a genuine law-level event recurrence, but is NOT the
full weighted projection law to the retained Plackett-Luce process.

Independent Lean helpers: retained-first scalar rate-cancellation
identity and empty retained-set boundary; see final-head CI.
`tests/test_s014.py` checks all retained subsets on six unequal
rational rates for first retained winner, and representative full
projected laws via independent head recursion. Mathematical
derivation, formal boundary and next step:
proof/WEIGHTED_PROJECTION_HEAD.md.

**Verified full-code/docs SHA** `2cd7ab3982af13b0779feb63698a0cf782830568`,
Actions PR run **41223800603**: full exact Python/census and imported Lean
were both successful, including the cancellation and boundary lemmas.
Further claim/roadmap metadata-only changes after this SHA require
another final-head dual-green check before merging.

**Still open in Lean:** first-retained event probability itself;
weighted deletion-consistency of *all* projected permutations;
`priorityOutputMass = finiteRaceLaw`; independent Exp clocks.
All are mathematical paper theorems/obligations as distinguished
in CLAIMS. No independent novelty claim. Atlas stays 90/8/45.
The next session is sessions/S015.md.

---

# S013 handover — 2026-10-31

## Final S013 release

**PR #12 merged successfully** as squash commit
`12adedef9d0d49fcc5cb43e6f6ac24dadfdbf0aa` on main,
at 2026-10-31T16:41:17Z. Its exact final branch/PR head
`50a0010596669380c4deb3e927a3fc35995fa9c4` passed **both**
the full exact Python/certified census job and all imported Lean
modules in GitHub Actions push run **41220677570**.
The corresponding PR run **41220697882** was launched at the same
head; its completion is separately visible in GitHub Actions.

This certifies IG-L20 and IG-L21 on the released code and the
S013 Fraction regressions. It does **not** certify weighted projection
to arbitrary retained subsets, full `finiteRaceLaw` pushforward,
continuous independent exponential clocks or independent novelty.
S014 is installed.

## Incoming verified S012 release

S012 PR #11 merged into main as squash commit
`9d9287177e4c9fd96099d9d429c698c4537142f8`.
The exact final PR head
`2c334bf06a84f4ad0cadb458382885ad3942aa88`
passed full exact Python and imported Lean in PR Actions run
**41215599528**. Subsequent main at `fe3c11c1a0fa920a30d01af22fe64026f1065d9a`
was the starting point for S013.

## S013 new imported Lean structure

**IG-L20 — general weighted first-head factorisation.**
`InverseGreedy/PriorityHeadConditioning.lean` proves:
- Every first-headed full priority leaf has orderMass =
  firstChoice of the head times orderMass of the complete tail;
- For any real-valued head-and-tail function, the exact weighted sum
  over **all actual** `List.permutations(active.toList)` equals the
  sum of firstChoice(head) times the weighted tail expectation, with
  no duplicate orders and no factorial decide proof.

Both complete Python and imported Lean passed at exact SHA
`5cce19f348d477634b780b69afef5b93f36fbee6`,
Actions run **41219976009**.

**IG-L21 — weighted first-head event/greedy reduction.**
`InverseGreedy/PriorityHeadEvents.lean` states and proves the
corresponding equality for an arbitrary complete-order event.
It applies the S012 deterministic first-choice residual theorem to
the true weighted greedy-output event mass. Critically, the
weighted inner sum still uses *all remaining tail vertices*,
and only the **event** filters away the blocked vertices.
It does **not** assume the missing law-level restriction result.
Initial CI failed because event decidability was not explicit in
the theorem signature; this was corrected by an explicit
`DecidablePred` parameter. Both imported Lean and full Python passed at exact SHA
`a5b9cb158ced98eba33c48637a61e1b2d758a8de`, Actions run
**41220399183**. Thus IG-L21 is Lean-verified, but the weighted
subset-deletion law is not.

**Independent exact regression:** `tests/test_s013.py` checks the
weighted test-function identity on every nonempty subset of six
unequal-rate vertices; first-vertex conditional mass on all
subsets; and conditional filtered-tail laws and deterministic
residual greedy outputs for edgeless, path, cycle, star and a
six-vertex undirected graph. Python suite verified at earlier
S013 green runs; verify the exact final head and census.

Complete mathematical proof and exact boundary:
`proof/WEIGHTED_HEAD_EVENTS.md`.

## Remaining obligations and S014

The S011 mathematical deletion-consistency proof remains to be
formalised **as a weighted law of full projected permutations**.
S013 first-head conditioning alone does not prove
`(filter retained)_* PL_active = PL_retained`.
Only after that can S013's honest event equation be identified
in Lean with `finiteRaceLaw` by induction and S010 fuel invariance.

Neither the whole discrete greedy law nor continuous independent
Exp-clock ordering is Lean-verified yet. No mathematical novelty
claim or arXiv/Palomar release is made.

S014 installed at `sessions/S014.md` to prioritise the
first-retained-winner law, complete weighted deletion projection,
and final discrete greedy pushforward. Atlas unchanged:
**90 positive / 8 negative / 45 unresolved** connected n<=6.

## Release state

S013 changes are on `s013-weighted-head-conditioning`.
All imported Lean modules and the full exact Python suite/census
must pass at the exact final PR head; record the final PR/run and
merged SHA before claiming complete release.
