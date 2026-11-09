# S044 — Burnside cross-check and kernel-checked edge-orbits (partial)

Date: 2026-11-09. Starting from verified S043 PR #43 merged to main as
`892ca2620b994efffd99395f7185310742bd99e1`
(push run 42615967435, PR run 42616010544, both complete green at
`a5d23a31a5c118e33eb2111ca358e32a534a9a88`).

## New independent argument for the six-vertex counts

Burnside's lemma for the action of S₆ on undirected simple graphs says
the number of unlabeled graphs is (1/720) Σ_σ 2^{c₂(σ)}, where c₂(σ)
is the number of cycles induced by σ on 15 unordered vertex pairs.

For connected graphs, replace 2^{c₂(σ)} by the number of σ-invariant
edge sets whose graph is connected. The exact program
`experiments/s044_burnside.py` counts fixed graphs by **edge orbits**
of 11 permutation cycle types, and tests connectivity by a separate
bitset reachability calculation; it does not call NetworkX or the
S042/S043 32768-graph orbit traversal.

Cycle type | class size | edge orbits | all fixed | connected fixed
--- | ---: | ---: | ---: | ---:
1^6 | 1 | 15 | 32768 | 26704
1^4 2 | 15 | 11 | 2048 | 1456
1^3 3 | 40 | 7 | 128 | 76
1^2 2^2 | 45 | 9 | 512 | 344
1^2 4 | 90 | 5 | 32 | 16
1 2 3 | 120 | 5 | 32 | 16
1 5 | 144 | 3 | 8 | 4
2^3 | 15 | 9 | 512 | 416
2 4 | 90 | 5 | 32 | 20
3^2 | 40 | 5 | 32 | 25
6 | 120 | 3 | 8 | 5

Weighted sums are 112320 = 720 × 156 for all graphs and
80640 = 720 × 112 for connected graphs. The same independent
algorithm reproduces the known unlabeled/connected sequences for n=1..6:
(1,2,4,11,34,156) / (1,1,2,6,21,112).
This is an additional exact **Python** proof-audit, distinct from
the earlier canonical-labelling computation. Burnside's lemma itself is
standard mathematics, not newly proven in Lean here.

## New Lean progress and precise boundary

`InverseGreedy/SixVertexBurnsideChecks.lean` builds explicit verified
two-swap permutations for **all 15 one-edge graphs**, and likewise for
all 15 one-missing-edge graphs. `IsoCheckB` is reduced by
`decide +kernel`; `iso_of_isoCheckB` promotes the checks to graph
isomorphism witnesses. These are two specific n=6 isomorphism orbits,
NOT a proof that there are exactly 156.

The same module hardcodes the independently computed Burnside rows and
kernel-checks weighted sums. This verifies numeric **arithmetic only**,
not the graph fixed-counts nor the Burnside group action. Do NOT claim
Lean has certified the 156/112 orbit count.

**Still open**: all-k `RealClockAEGU (starCoronaNb k)`,
including its MIS cardinality and first-choice lower-bound theorem;
a full Lean proof of the Burnside orbit action and invariant connected
counts (or a complete explicit permutation table); crosswalk certified
in Lean for all 112 connected atlas rows; 45 unresolved graphs.
Keep 90/8/45. No novelty, submission or registration assertion.

CI/release gate: full imported Lean + Python/exact/census at identical
final SHA in both push and PR Actions, then squash merge; if checks fail,
leave PR open. Next `sessions/S045.md`.
