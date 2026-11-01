# S016 handover — 2026-11-01

**S016 release merged:** PR #15 squash-merged into `main` as `b1bd2634fe12286924a35cc390810e9353feda87`. Exact final PR head `ac8e271e5fc5e4fcd3ddcf7b156d025d12ff4a86` passed both imported Lean and full Python/certified census in **both** push run [41346130914](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41346130914) and PR run [41346137455](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41346137455). The new theorem is all-positive-real first-retained-winner marginal only, **not** full deletion consistency.

**PR #15:** https://github.com/jfairfaxball-348/Inverse-Greedy/pull/15
The first-retained-winner probability theorem is now a compiled Lean theorem, not just a paper claim or a scalar identity. Branch `s016-first-retained-winner`, exact validated code SHA `fd83d359cdb5ef5db527bfe59ae72799d8c9913e`; full Python exact tests, certified connected-graph census and imported Lean were successful in Actions run `41345774024`: https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41345774024. The exact-final-head verified release is recorded above.

New `InverseGreedy/FirstRetainedWinner.lean` defines the genuine weighted complete-permutation first-retained event and proves a conditional head recurrence (retained head decides the event immediately, discarded head recurses). `InverseGreedy/FirstRetainedExact.lean` proves for all retained⊆active, retained nonempty, i∈retained and strictly positive rates that `firstRetainedMass rates active retained i = firstChoice rates retained i`. The induction is on the active-cardinality fuel and uses S011 full tail normalization plus an exact proportional-rate fixed-point calculation.

`tests/test_s016.py` independently tests the event with rational head-split DP for all 512 subsets of nine strongly unequal-rate vertices; a separate complete-permutation oracle covers all 64 subsets of six vertices. These finite regressions are not the Lean proof.

**Remaining Lean obligations:** full conditional ordered-sequence deletion consistency, `priorityOutputMass = finiteRaceLaw` with blocked-neighbour filtering, and independent Exp-clock semantics. Do not infer the complete retained law just from its first-element marginal. Six-vertex certified atlas unchanged: 90 EGU / 8 non-EGU / 45 unresolved. Session S017 is installed.

---

# S015 handover — 2026-11-01

**PR #14 merged:** https://github.com/jfairfaxball-348/Inverse-Greedy/pull/14
Branch `s015-projection-support` was squash-merged to main as `fd08c64a29fcab5e12ffd0c4ebdbb49a746add9f`. Exact final PR head `3583f27d3a69f5124f88e6b0a859cf065ca8c126` passed both imported Lean and full Python/certified census in GitHub Actions run `41290187561`. This certifies only the S015 support and singleton Lean theorems, not general deletion consistency.

S015 added `InverseGreedy/ProjectionSupport.lean`, proving for every retained ⊆ active that filtering an actual full `List.permutations` order yields an actual complete retained permutation. This implies zero mass for all unsupported filtered targets for arbitrary real rates; a singleton retained set has mass one at the singleton order when all rates are strictly positive, using S011 normalization.

`tests/test_s015.py` extends exact rational tests to all 7! complete priority orders and all 128 subsets, independently comparing projected and intrinsic retained laws. The general law equality is a test oracle, not established by these Lean lemmas.

**Remaining**: First-retained-winner probabilities for arbitrary nonempty retained sets of size ≥2, complete weighted deletion-consistency, `priorityOutputMass = finiteRaceLaw`, and independent Exp-clock equivalence remain open in Lean. Baseline 90 EGU / 8 non-EGU / 45 unresolved. S016 installed.

---

# S014 handover — 2026-10-31

## S014 release — merged PR #13

**PR #13 merged** as squash commit
`713e5641bda05d570c92866ca85f326f5d9ae044` on `main`.
The exact final S014 PR head
`66524262097647f7edc5dca34dd1f9e9139a1265`
passed **both** full Python/certified census and imported Lean in
GitHub Actions run **41224006146**. This checks the S014 Lean
claims and exact regressions on the final reviewed code. It does
not prove full weighted deletion consistency in Lean.

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
