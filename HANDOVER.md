# S012 handover — 2026-10-31

## Incoming verified release

S011 PR #10 was merged as squash commit
`0e5949b4a79aa215ae5aeb5ff13b524deb9ae69f`.
The final exact PR head
`1850e94398964fba7e021b29b6a6fa460f8c73c1`
passed both imported Lean and full Python in PR CI
41196801662. Main was verified green at
`8c7c1e5dbd6f0f153caa034d6ea2f3b37fb861d7`,
run 41196998263. S012 started from that main SHA.

## S012 additions

**IG-L16 — deterministic greedy residual identity.**
`InverseGreedy/GreedyBlockedErasure.lean` proves:
- greedy acceptance never loses previously accepted vertices;
- deleting all later neighbours of a previously accepted vertex
  preserves a complete greedy scan, for symmetric neighbour maps;
- adding a vertex nonadjacent to a retained suffix commutes with scanning;
- hence Greedy(v :: suffix) equals {v} united with Greedy of the suffix
  after deleting the neighbours of v.

This is a **pointwise deterministic theorem**, not the weighted-law
pushforward. It compiled with full Python CI at exact SHA
`39090ae14521c6f8851f3d60f9429daa3a66ee8c`, Actions
run **41214427832**.

**IG-L17 — bounded weighted event masses.**
`InverseGreedy/PriorityOutputLaw.lean` defines the full priority
permutation event mass grouped by `greedyOutput`, and proves each
target has event mass in [0,1], reusing S011 normalization.
This compiled with full Python CI at SHA `b53605cbd5e3ecbd48fdb235b6a1049b9f6a85b2`,
run **41214659606**. The event law has NOT been identified with
`finiteRaceLaw` in Lean.

**IG-N1b / IG-L18 — a positive C6 total-variation gap.**
From the S001/S003 C6 pair-product bound p0 p1 p2 ≤ 1/729,
at least one of the three pair outputs has probability ≤ 1/9.
The uniform distribution over five MIS assigns each 1/5.
Therefore **TV(P_r,U) ≥ 4/45** for every strictly positive
rate vector. In particular **C6 is not AEGU**, unlike the S009
star coronas, which have positive but unattained arbitrarily
small TV distances.

The pure algebraic deficit implication (not the stochastic
event-to-TV identification) is compiled in
`InverseGreedy/C6TVGap.lean` at SHA
`ab91f0819f4c6f71640e062ce009abc0849e4dbe`,
run **41214809471**. Complete informal proof:
`proof/C6_TV_GAP.md`. The bound is not claimed sharp.

## Verification

- `tests/test_s012.py` exhaustively compares deterministic
  residual identities for stars, paths, cycles, edgeless graphs and
  a six-vertex graph. It tests arbitrary accepted seeds, the
  necessity of symmetry and independent exact weighted-order vs
  recursive laws.
- `tests/test_s012_c6_gap.py` checks all 729 positive tuples in
  {1,2,4}^6 exactly, their opposite-pair probabilities against the
  first-choice recursion, the TV gap, and full 720-order oracles.
- All imported Lean modules and complete Python suite (including
  the certified connected n≤6 census) must be validated at the
  exact **final PR head**, as documented in the S012 PR.

## Unresolved and next session

**Formal weighted restriction/deletion consistency for arbitrary
retained subsets, and equality `priorityOutputMass = finiteRaceLaw`,
remain OPEN in Lean.** They are mathematical paper proofs from
S011 with exact arithmetic regression support. Independent
continuous Exp-clock equivalence also remains open.

S012 supplies no new connected six-vertex classification:
**90 EGU / 8 non-EGU / 45 unresolved**. C6 remains one of the
previously classified eight negatives; its new result strengthens
its obstruction from non-EGU to non-AEGU.

S013 is installed in `sessions/S013.md`. No independent novelty
certificate, Palomar registration or arXiv publication is claimed.
