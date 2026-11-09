# S043 — six-vertex encoding and atlas-to-orbit crosswalk (partial)

Date: 2026-11-09. Base: S042 verified `main` `6620998cacb22caabc4b04d7a65750bf2a7f4afb`.

## Formal progress

`InverseGreedy/SixVertexEdgeEncoding.lean` gives the explicit lexicographic 15-edge table and its inverse rank table. Kernel `decide +kernel` checks all pairs `i<j`; the already proven generic `nbOf_fOf` transports this to **every symmetric irreflexive graph on `Fin 6`**. The module is imported by the root. This is not a classification theorem, nor does it say that all six-vertex graphs form 156 orbits in Lean.

## Independent exact crosswalk

`experiments/s043_atlas_crosswalk.py` independently applies all 720 vertex permutations to each of S042's 156 representatives, checks their 156 orbits are disjoint and exhaust all 32768 edge codes, and verifies the least-code normal form of each representative. Unlike S042's adjacent-swap BFS, this checker directly permutes every edge pair. It then compares the 112 connected NetworkX atlas graphs, each encoded as a 15-bit vector, with the S042 orbit map. An explicitly rechecked permutation sends every atlas record to exactly one representative, and all 112 connected representatives appear exactly once. `--emit-json` exports `atlas_index`, `atlas_code`, `orbit_index`, `representative_code`, and `vertex_to_representative` for later Lean generation.

`tests/test_s043.py` checks the independent partition, full bijection, concrete edge encoding, malformed/duplicate edges, and invalid permutations. These are **exhaustive exact Python computations**, not Lean-kernel proofs of orbit completeness. The source atlas and its labelling come from NetworkX, but graph-isomorphism comparisons are not delegated to NetworkX.

## Remaining formal obligations

- The general all-m `RealClockAEGU (starCoronaNb k)` proof, MIS classification/count, conditional equal-rate matching and pointwise lower bound are **not** in Lean. The S042 mathematical argument stands; all-m non-EGU is already Lean.
- Prove 156 orbits / 112 connected classes **in Lean**, using independently compilable chunks of the permutation table and the new six-vertex encoding. Connect the certified orbit representatives to atlas graph certificates and unresolved labels.
- Do not reinterpret exact Python enumeration as an imported Lean result.
- Connected n≤6 atlas stays **90 EGU / 8 non-EGU / 45 unresolved**. No novelty or publication claim.

Next: `sessions/S044.md`. Release gate requires full Lean + Python/exact/census on the exact *final* push and PR heads.
