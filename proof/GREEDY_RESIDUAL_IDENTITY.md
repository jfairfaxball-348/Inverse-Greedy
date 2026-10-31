# S012 — Deterministic greedy residual identity

Let `neighbours : V → Finset V` be a symmetric adjacency relation:
if `w ∈ neighbours(v)`, then `v ∈ neighbours(w)`.
The vertex sets are finite, and the priority list may be any finite list.
No rate, positivity, independence or probabilistic hypothesis is needed.

Write `Greedy(L; A)` for a scan of list `L` started from an accepted
vertex set `A`. Each scanned vertex `w` is accepted precisely when
`neighbours(w) ∩ A` is empty. Write `Greedy(L)=Greedy(L;∅)`.

## Deterministic theorem

**First-choice residual identity.** For any vertex `v` and suffix `L`,

    Greedy(v :: L)
      = {v} ∪ Greedy(filter (λ w, w ∉ neighbours(v)) L).

This is the exact pointwise identity required for conditioning a
weighted priority law on its first vertex. In a simple graph the filter
keeps the vertices outside the open neighbourhood; a full permutation
has no second copy of `v`, so the retained list is the induced
closed-neighbourhood complement `V\\N[v]`.

**Proof.** A greedy scan only inserts vertices, never deletes them.
The initial scan of `v` from the empty accepted set inserts `v`.
Every later `w∈neighbours(v)` has `v∈neighbours(w)` by symmetry,
so it is rejected. Deleting every such blocked occurrence therefore
does not change any subsequent accepted set. For every remaining
`w∉neighbours(v)`, symmetry gives `v∉neighbours(w)`. Thus inserting
`v` into the seed of its greedy scan does not change whether `w` is
accepted, and the two scans commute vertex by vertex. Their final
accepted sets differ exactly by the already accepted `v`.
The identity follows by induction on `L`. QED.

## Scope and limitations

- The Lean module `InverseGreedy/GreedyBlockedErasure.lean` contains
  scan monotonicity, erasure of every blocked neighbour, commuting
  insertion of an unrelated accepted vertex, and the stated pointwise
  residual theorem. The release ledger records whether GitHub Actions
  compiled its latest exact SHA.
- The exact Python regression `tests/test_s012.py` checks the identity
  against every suffix order for empty, star, path, cycle and additional
  six-vertex graphs. It also tests arbitrary accepted prefixes and
  exhibits a directed counterexample when symmetry is omitted.
- This theorem is **not** the weighted-distribution identity.
  To reach `finiteRaceLaw`, one must still establish law-level
  deletion consistency in Lean and sum `orderMass` over complete
  permutations grouped by their `greedyOutput`.
- Identifying the discrete `orderMass` model with independent
  continuous exponential clocks remains a separate task.

The underlying mathematics is elementary and no independent novelty is
claimed. This file documents a formalisation dependency, not a
publication-level classification theorem.
