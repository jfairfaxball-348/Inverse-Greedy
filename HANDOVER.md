# S011 handover — 2026-10-31

## Incoming verified release

S010 PR #9 was merged as `8c6115433a00498bd5ca45c7c7392fc5adac59dc`.
Its exact final PR head `8064bde884981bc8170826db046fea9d582315f2`
passed both Python and imported Lean jobs (Actions run 41193924574).
The subsequent exact main head `7d87a1e6e863c7be93a440599c7b6fa7889b1c06`
also passed GitHub Actions run 41194086791.

## S011 research results

The actual `List.permutations(active.toList)` (not just support
membership) has been proved in Lean to be a distinct-head disjoint
enumeration of complete tail permutations. The proof checks duplicate
freeness on both sides and obtains a List.Perm equality; no factorial
`decide` is used. InverseGreedy/FullPermutationDecomposition.lean
compiled in an imported GitHub Actions Lean+Python run 41195940431,
SHA `00fb0afe5b1253c23d4fd825cc9fc338ea9fddf7`.

In addition, the S011 paper proof establishes **IG-R2**, deletion
consistency of the full positive weighted-order law after erasing any
vertex subset, including conditional on the first chosen vertex.
This yields **IG-R3**, equality of the weighted-priority greedy-output
pushforward with the finite first-choice recurrence, for finite
simple undirected loopless graphs. Proof in
proof/PRIORITY_DELETION_CONSISTENCY.md.

Independent `fractions.Fraction` tests cover all subset restrictions
on several unequal rate vectors, first-choice conditional restrictions,
enumeration multiplicity and total weighted mass on <=6 vertices,
and the original independent full-permutation vs recursive
greedy-output oracles for multiple graph classes.
See experiments/priority_deletion.py and tests/test_s011.py.
Both Python and Lean jobs passed together for the unique-head module.

InverseGreedy/FullPermutationNormalization.lean now **proves in Lean**
that the `orderMass` values summed over the actual full permutation
list equal one for every positive real rate assignment. The proof uses
the unique-head decomposition, leaf mass identity and finite induction.
The exact branch SHA `a613bb87a5fa64b54303c66234a63791135e9ca0`
passed **both** Python and imported Lean jobs in push run 41196557142
and PR run 41196560831. This closes IG-L15; it does NOT prove the
law-level weighted deletion consistency or greedy pushforward in Lean,
nor the continuous exponential-clock law.

## Next workshop

sessions/S012.md is installed: first prove weighted order restriction
and the greedy law-level pushforward in Lean; then begin an
independent clock-equivalence bridge. No continuous exponential-clock
theorem is claimed from the paper identities or partial Lean lemmas.

S011 has **not** supplied new all-positive six-vertex EGU or non-EGU
certificates. Keep the connected n<=6 partial atlas **90/8/45**.
No novel-claim certificate, Palomar registration or arXiv release.

## Release verification

The S011 branch is `s011-priority-permutation-decomposition`.
Use the latest exact branch/PR SHA and its Python and Lean GitHub
Actions jobs before merging; update CLAIMS.md, README.md and this
handover to distinguish verified from pending proof claims.
