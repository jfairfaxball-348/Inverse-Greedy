# S010 handover — 2026-10-31

## Incoming state and release

S009 was fully merged as PR #8 (squash 9569618) with green Python
and imported Lean at head ed0d02d4, runs 41188364427 / 41188368166.
The S010 work was prepared on branch `s010-finite-law-fuel-and-skip`
as PR #9: https://github.com/jfairfaxball-348/Inverse-Greedy/pull/9

**S010 PR #9 was merged successfully.** The exact final PR head
`8064bde884981bc8170826db046fea9d582315f2` passed **both**
the exact Python and imported Lean jobs in GitHub Actions PR run
**41193924574**. The original new Lean lemmas also passed at
`fbf578c2a1b877a0c7c1a6217dc00ce785af135c` in PR run
**41193711626** after correcting a reserved-word naming error.
Squash merge commit on main:
`8c6115433a00498bd5ca45c7c7392fc5adac59dc`.
This post-merge handover records the verified exact release head.

## New mathematical results — IG-P9 and IG-P10

Write AEGU for graphs whose positive-rate attainable greedy MIS laws
have uniform MIS law in their total-variation closure. AEGU is **not**
equivalent to actual EGU.

- Disjoint union G ⊔ H is AEGU iff G and H are AEGU.
- For nonempty G and H, the graph join G ∨ H is AEGU iff G and H
  are AEGU, using group-total rate scaling to match MIS counts.
- Consequently, for star-corona C_m (m>=2) from S009, both C_m ⊔ K2
  and C_m ∨ K1 are AEGU but remain provably non-EGU.
- With k=2^m and TV_C(t) from S009, choosing positive rates on the
  universal joined vertex z equal to total_C/(k+1) gives
  TV_join(t)=(k+1)/(k+2)*TV_C(t). With an equal-rate K2 component,
  TV_union(t)=TV_C(t). Both approach zero, neither is ever zero.

Complete informal proofs: proof/APPROXIMATE_EGU_CLOSURE.md.
Independent exact checks: tests/test_s010.py (first-choice
recursion and all 7! orders for seven-vertex join).
The partial connected n<=6 atlas remains 90 EGU / 8 non-EGU /
45 unresolved.

## New Lean results — IG-L13

InverseGreedy/FiniteLawFuel.lean, imported in InverseGreedy.lean:
- afterChoice_subset_erase and afterChoice_card_lt;
- finiteRaceLaw_fuel_step_stable and finiteRaceLaw_fuel_eq_card;
- greedyAccept_blocked and greedyOutput_skip_blocked.

These are structural finite combinatorial statements. They do **not**
establish the whole-weighted-permutation law, the pushforward to
finiteRaceLaw, or independent exponential-clock semantics. Keep all
these latter requirements explicitly open.

## Next

sessions/S011.md is installed: structurally decompose actual
List.permutations exactly once, normalize summed orderMass, then
combine the skip and fuel lemmas with weighted pushforward and
eventually continuous clocks. Investigate genuinely new AEGU
boundary mechanisms with strict proof or exact witnesses.

No Inverse Greedy arXiv/Palomar release or independent novelty claim.
