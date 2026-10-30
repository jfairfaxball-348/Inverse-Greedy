# S007 handover — 2026-10-30

## Repository
Base main SHA before session: `9903b669e939d9afa527be81b748a2f3308a13d4`,
with green Actions run 41127034157. S006 PR #5 was already merged.
S007 changes are on branch `research/s007-false-twin-classification`.
**Verify the final PR head and exact-head CI before declaring this merge
complete.** Read current GitHub run/PR status (rather than relying on
historical run numbers).

## Mathematical result
**IG-P7 — false-twin invariance:** for distinct nonadjacent vertices
with the same open neighbourhood, delete one and add its rate to the
other. The terminal MIS distributions match under the natural
bijection; the converse splits the parent rate between twins. Full
informal proof: `proof/FALSE_TWIN_INVARIANCE.md`.

19 formerly unresolved n=6 graphs lift exact S005 positive witnesses
(16 rational and 3 in Q(√3)); 3 formerly unresolved n=6 graphs
(connected indices **4,13,16**) contract to P5 and are non-EGU.
Each new graph's edges, parent and twin pair are recorded in
`results/S007_ATLAS.md`. Exact tests check the 19 positives via
full 720-order weighted permutation enumeration and independent
first-choice recursion, including quadratic field cases.

The connected n<=6 atlas is **89 positive / 7 negative /
47 unresolved**, of 143. Among n=6 alone: 59/6/47.

## Lean progress and scope
S006 proved normalisation of the **recursive** head-choice tree.
S007 adds `InverseGreedy/OrderLeafBridge.lean`, proving for every
duplicate-free ordered list that the conditional-first-choice
product of its successive head/tail sets equals its `orderMass`.
This is a single-leaf identity, NOT a proof of the bijection from
tree leaves to `List.permutations`, full-permutation sum = 1,
pushforward to `finiteRaceLaw`, or a continuous exponential-clock
equivalence. Imported Lean leaf bridge and full Python suite were both green in Actions run 41131451454 at exact SHA 543cfe9. This is not an end-to-end continuous-clock theorem. Final release-head CI and PR merge status must still be checked.

## Next
`sessions/S008.md` targets the missing finite permutation-sum and
greedy pushforward in Lean and the 47 remaining connected six-vertex
cases. Preserve earlier proofs and tests. Do not turn failed searches
into negative theorems, claim the induced P5 obstruction for arbitrary
supergraphs, or imply novelty/priority certification.
