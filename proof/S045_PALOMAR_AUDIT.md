# S045 Palomar candidate and readiness audit — 2026-11-18

**Status: NOT SUBMITTED / BLOCKED.** This document is a research and packaging audit, **not** official Palomar Comparator output, a verified Palomar review, a registration ID, or an assertion of novelty. The owner requires a public, independently verifiable Palomar entry before any paper draft.

## Candidate decision

**Select IG-P5**, the graph classification up to five vertices, as the first substantive Palomar candidate. It concerns strictly positive independent Exp(rate) arrival clocks; vertices are greedily accepted unless an earlier accepted neighbour blocks them; the resulting law is uniform over **all maximal (not maximum) independent sets**. For n<=5, every finite simple graph admits positive rates giving the uniform law, **except** the five-vertex path P5, which has no positive-rate solution. The empty graph is included.

Exact source theorems (all in namespace `InverseGreedy`):

* `InverseGreedy/SmallGraphClassification.lean:1784` `graphs_le_five_classification (n : ℕ) (hn : n ≤ 5) (nb : Fin n → Finset (Fin n)) (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (hi : ∀ v, v ∉ nb v) : RealClockEGU nb ∨ ∃ e : Fin n ≃ Fin 5, ∀ a, p5Nb (e a) = (nb a).map e.toEmbedding`.
* Same file, line 1770: `fin5_realClockEGU_iff_not_P5 (nb : Fin 5 → Finset (Fin 5)) (hs : ∀ x y, y ∈ nb x → x ∈ nb y) (hi : ∀ v, v ∉ nb v) : RealClockEGU nb ↔ ¬ ∃ e : Fin 5 ≃ Fin 5, ∀ a, p5Nb (e a) = (nb a).map e.toEmbedding`.
* `InverseGreedy/RealClockGreedyLaw.lean:331` `realClockEGU_iff_firstChoiceEGU`: the genuine Mathlib independent exponential-clock law agrees with the first-choice recursion for symmetric neighbour maps. `RealClockEGU` is a **defined** predicate (same file), requiring existence of strictly positive real rates and equal output probabilities for all maximal independent sets.

**Crucial qualification:** `graphs_le_five_classification` alone is a *disjunction*, not a biconditional. The P5 non-EGU direction is supplied separately by `p5Nb_not_realClockEGU` in `SmallGraphObstructions.lean` and the isomorphism transport used in `fin5_realClockEGU_iff_not_P5`. Any Palomar Challenge must state the full no-other-exceptions claim, not quietly report the disjunction as an iff. Isomorphism needs the displayed neighbour-map transport, not identity of labelled graphs.

## Candidate comparison and evidence boundaries

| Candidate | Current evidence | Decision |
| --- | --- | --- |
| At-most-five-vertex iff classification | Imported Lean theorems, S041 complete stochastic-law bridge, prior dual-green CI at S041/S044 | **Primary**; substantial inverse-design classification but formal Challenge interface still needed |
| All finite cographs EGU | `CographEGU.lean` `IsCograph.realClockEGU`, Lean/S041 | Supporting; closure under unions/joins, not classification of all EGU |
| Disjoint-union and nonempty-join iff | `GraphOperationsEGU.lean`, `realClockEGU_union_iff`, `realClockEGU_join_iff` | Supporting; could enrich context, not necessary Comparator headline |
| False-twin invariance | `FalseTwins.lean`, `realClockEGU_twinExtend_iff` | Supporting structural transfer |
| All m>=2 star coronas NOT EGU | `GeneralFamilies.lean`, `starCorona_not_realClockEGU`, Lean/S041 | Alternative substantive infinite family |
| All m star coronas AEGU | Ordinary mathematics only; m=2 is Lean proved | **Do not register as fully Lean proved** |
| n=6 156/112 orbit exhaustiveness | Independent exact Python; partial Lean singleton/co-singleton evidence | **Do not register as Lean proved** |
| n<=6 EGU/non-EGU census 90/8/45 | 90/8 Lean certifications; 45 unresolved; n=6 exhaustive crosswalk Python only | **Not a complete classification** |

## Palomar rules and presently observed blockers

Official sources (accessed 2026-11-18):
- https://palomar-registry.org/how-to-submit
- https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
- https://github.com/PalomarRegistry/PalomarTemplate
- https://submit.palomar-registry.org/

At S045's initial `main` commit `ada7a67dfe85a4f69058e7775bf2b03a915d9550`, GitHub tree lists **95** tracked Lean source files and no root `LICENSE`/`LICENCE`/`COPYING`, `Challenge.lean`, `Solution.lean`, `comparator.json`, or `formalization.yaml`. Sampled imported files (`InverseGreedy.lean`, `SmallGraphClassification.lean`, `EdgeSetGraphs.lean`, `RealClockGreedyLaw.lean`, `GraphOperationsEGU.lean`, `CographEGU.lean`, `FalseTwins.lean`) begin with old-style `import`, not the required `module` header. The subsequent exact-head S045 CI preflight scanned all 95 tracked Lean files and reported **95/95 lacking modern module headers**. The report is a local heuristic structural diagnostic, not Lean's official module verifier.

Palomar requires **every** regular Lean source in the submitted repository (even unused files and contained projects) to have a modern module header and at most 10,000 physical lines. A Challenge has a stricter 1,000 lines / 100 KiB cap and transitive imports only from permitted core/Mathlib/Tau Ceti closure. Solution may use pinned local or Git dependencies; this **does not** exempt the substantive source tree from module checks. Adding `module` is not sufficient: public declarations/imports must be migrated and the entire proof rebuilt. All of this must be tested against official Comparator and its independent kernels, rather than assuming that prior `lake build` applies.

Current `lean-toolchain`: `leanprover/lean4:v4.35.0-rc3`; published minimum in PalomarSubmission `toolchains.json`: `v4.35.0-rc2`. The **Mathlib pin/toolchain must still be checked for exact compatibility**; supported minimum alone proves no build or Comparator result.

The required root licence is **owner-controlled and absent**. Do not select a licence unilaterally. `formalization.yaml` must disclose AI assistance honestly, distinguish original result vs source-based formalisation, identify responsible people, note unproved claims and source overlap, and use the correct structured fields. Challenge should express EGU and the clock-process mathematical meaning without importing private `InverseGreedy` modules; Solution must establish an exact bridge to existing imported formal proofs. Merely naming the theorem in Comparator is not enough.

## Source-specific preliminary literature review

* Pippenger (1989), *Random Sequential Adsorption on Graphs*, DOI 10.1137/0402034: original graph RSA process; the inspected abstract describes sequential occupancy, not an inverse positive-rate iff classification on <=5 vertices.
* Krivelevich, Mészáros, Michaeli, Shikhelman, *Greedy maximal independent sets via local limits*, DOI 10.1002/rsa.21200: random greedy MIS and its asymptotic local limits; inspected public treatment uses uniform random order rather than designed positive per-vertex rates.
* Random sequential adsorption with unequal rates is genuinely existing practice, e.g. *Percolation of even sites for random sequential adsorption* (2012; DOI 10.1016/j.spa.2012.01.007); therefore **unequal exponential clocks themselves are not novel**.
* Fairfax-Ball, *Greedy Uniformity on Trees: Exact Obstruction and Near-Uniform Spiders*, arXiv:2610.02276 (2026), concerns equal-rate random ordering; the changed rate-controllability question must be stated separately.
* No exact matching at-most-five positive-rate iff result was identified in this targeted search; **lack of a search hit is not a novelty or priority certificate**. A complete citation and forward-citation audit remains necessary.

Potential research audience: probabilistic combinatorics, random greedy algorithms, random sequential adsorption and inverse distribution design. Editorial uncertainty: Palomar may regard a five-vertex classification alone as insufficient research interest; structural union/join and infinite obstruction theorems can strengthen the motivation **without pretending they are the same classification**.

## Verification ledger

- Prior actual **S044** code head `39fc14da79ac8731cc5bb78706a4a842aab5e287`: dual-green push run 42635260726 and PR run 42635294288, before squash merge.
- Prior S044 main squash merge `ab48ecbd365951a2f661d70e7df773f8a28fcf20`.
- At audit time S045-installed `main` SHA `ada7a67dfe85a4f69058e7775bf2b03a915d9550`; workflow `44366116204` subsequently passed. S045 PR #45 code head `3595d041f97aa25ff2b6f8bc3255a745fcab08d6` passed both push and PR CI in runs 44368658437 / 44368676610, and was squash-merged as `ea4eb45bc78e5ecd565a6362e918cc826ebb902a`.
- S045 adds `experiments/palomar_preflight.py` plus isolated unit tests. This is **static structural preflight only**; running it can identify packaging blockers but cannot certify theorem proof, metadata truth, axioms or Comparator.
- Full imported Lean build and Python tests/exact/census: **verified by GitHub push and PR CI on the identical S045 PR code head** above. Local `#print axioms` for the proposed Comparator interface, official `lake comparator`, independent Palomar verification/editorial review and registration: **NOT EXECUTED / NOT VERIFIED**.
- No Palomar ID, status page or registration evidence exists in this audit. Submission **must not** occur against the current incomplete source.

## Next exact gates

1. Run `python experiments/palomar_preflight.py`; migrate every failing Lean file with `module` and public interfaces, preserve 10k cap, and rebuild. Preserve 90/8/45 census.
2. Get owner's explicit choice of root repository licence; commit that choice and match `formalization.yaml`.
3. Write compact independent Challenge with full mathematical semantics and no prohibited local imports; Solution importing the existing proof must match Comparator exact types. Validate provenance and AI disclosures.
4. Run full imported Lean build, Python/exact/census, `#print axioms`, and official `lake comparator` with recorded logs at exact committed SHA; dual-green push/PR for code and independent Palomar mechanical checks.
5. Authenticate and submit via https://submit.palomar-registry.org/ (owner login or documented agent protocol), review owner-only consent, then verify publicly served Palomar entry and permanent ID. **No paper until that final gate.**

Follow-up: `sessions/S046.md`. This audit is not a registration and is not a claim that S045 objectives were completed.
