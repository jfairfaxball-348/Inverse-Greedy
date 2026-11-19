# S047 — independent verification and Palomar registration gate (19 Nov 2026)

## S047 completion update — exact-head independent kernels VERIFIED; PR MERGED

The S047 full proof package **passed** all required code-head gates at `5c4317ca5cffd8dab389c543df9c09afdd599f11`:

| Gate | Exact evidence | Result |
|---|---|---|
| Full imported Lean + Python/exact/census push | [Research verification 44491400149](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44491400149) | **SUCCESS** (full Lean and Python jobs) |
| Full imported Lean, Challenge/Solution, independent Comparator and Python/exact/census PR | [Research verification 44491410029](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44491410029) | **SUCCESS** (both jobs) |
| Dedicated full modern module / independent official Comparator, schema and static source preflight push | [S046 migration trial 44491399887](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44491399887) | **SUCCESS** |
| Axiom closure | Above PR and dedicated logs | `[propext, Classical.choice, Quot.sound]` |
| Independent kernels | Above PR and dedicated logs | `con-ron kernel accepts the solution`; `nanoda kernel accepts the solution`; `Lean default kernel accepts the solution`; **`Your solution is okay!`** |
| Full scientific suite and structural compliance | Above push/PR CI | 172 unit tests; exact experiment; connected n≤6 90/8/45 census; 97 modern-header source files; blocking static preflight; pinned official v0.4 JSON Schema PASS |

The precise branch SHA is the source input for the verified *premerge* artifact. [PR #46](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/46) was marked ready, and **squash merged** with merge SHA `877f7461d5b8caf7c9b197f41a991c71ef2ed234`. Since a squash merge produces another public commit, separately check `main` post-merge CI; do not silently transfer the branch-head proof status onto an unverified postmerge SHA.

**Palomar status: NOT SUBMITTED / NOT REGISTERED; no public permanent identifier or version, and NO PAPER.** Full independent proof checking does not certify novelty, research importance, journal peer review or registry acceptance. Owner authentication, permissions and final public-registration consent remain outside these CI checks. Once the latest main SHA is itself fully green, use that **exact immutable full SHA** for owner-controlled Palomar submission; verify the live public ID against it before changing status.

---



**Current verdict (snapshot): NOT SUBMITTED / NOT REGISTERED; NO PAPER.** This evidence is deliberately bounded: an intermediate passing CI job is not a final-source proof certificate, a Comparator run is not a public Palomar record, and a staged submission is not registration.

## Exact source and checks

- Source branch: [s046-modern-lean-port](https://github.com/jfairfaxball-348/Inverse-Greedy/tree/s046-modern-lean-port); [draft PR #46](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/46); baseline `main` `c073675d83b29ae3c330efd504427f58ac2be066`.
- Historical fully migrated Lean checkout: S046 dedicated [run 44481531236](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44481531236), checked out `48ddd48af112215b3546e5f68fedf6011e45f7ee`, mechanically migrated 95 files, **full lake build 9054 jobs success**, then bot committed modernised sources `117e8ce9ebb44740ce1b3b3dcb4de6fb8df066c8`. At that same checkout, `lake env lean Challenge.lean` succeeded with the one deliberate Challenge sorry; `lake env lean Solution.lean` succeeded and logged:
  ```
  'PalomarEGU.graphs_le_five_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  No `sorryAx`, `admit`, custom axiom or `native_decide` appeared in that actual theorem axiom output. The historical official Comparator step **FAILED** with `error: unknown target 'Challenge'` and therefore is NOT a comparator certificate.
- S047 fixed the missing Lake `Challenge` and `Solution` library targets at `6f68e4b8c8f870ab4a37ca581736a514b4cfbf61`; actions [port 44489694637](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44489694637), [push 44489694757](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44489694757), [PR 44489704983](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44489704983). The push/PR standard Research verification jobs for this intermediate SHA completed green; dedicated Comparator job pending at this snapshot.
- S047 added the official [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate) source/line-cap scanner, blocking Palomar static preflight, and exact pinned [upstream formalization.yaml v0.4 schema](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema), with reproducible local validator, at `9151d64e2d68319dc32747d459ec9ea24e5ad527`. [Run 44490238324](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44490238324) showed header and source scanner passed and `STATIC_PREFLIGHT_PASSED` for **97 Lean files** (95 imported + Challenge + Solution); it then **FAILED** schema because `status.main_results[0]` was a string.
- S047 corrected `status.main_results` to the upstream v0.4 required object, commit `64d98e959eb2fad5d55b5ca0bb2cb1b600464c13`. Its [push Research 44490340280](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44490340280) and [PR Research 44490352441](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/44490352441) **Python jobs** passed **172 tests**, `experiments/exact.py`, `experiments/census.py --max-n 6 --max-rate 4`, source rules, blocking `palomar_preflight.py` and pinned v0.4 validation. Independent source checker found no violations; local metadata output: `formalization.yaml: upstream v0.4 JSON Schema PASS (locally pinned)`. Full Lean and comparator checks at this SHA were still underway when this note was drafted.
- S047 added explicit Challenge/Solution compilation and official independent-kernel Comparator checks to PR Research CI at `5bf15b316b22b8480e8353a2f4c2d07d1c764b9d`; current final-head CI **must** be inspected afresh.

## Scientific and policy limits

- Source theorem is the genuine positive-rate Exp-clock result, uniform on **inclusion-maximal** independent sets, with the only n≤5 exception P5 **up to whole-graph isomorphism**. The imported `graphs_le_five_classification` itself is a disjunction; the full iff uses strict non-EGU P5 obstruction and graph isomorphism transport. Challenge imports Mathlib only, Solution locally imports existing Lean proofs.
- Certified connected n≤6 atlas stays **90 EGU / 8 non-EGU / 45 unresolved**. Six-vertex 156/112 orbit *exhaustiveness* and all-m star-corona AEGU are **not** Lean-proved.
- `LICENSE` is the owner-selected Apache-2.0. Metadata discloses AI contribution, prior sources, research-interest doubts and verification limits. Schema passing does NOT establish truthful provenance, editorial acceptance or novelty.
- [Palomar submission policy](https://palomar-registry.org/how-to-submit) and [source policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md) require a public **exact 40-character SHA**, Comparator and independent kernel, editorial judgement and separate final owner authentication/consent. No login, submission confirmation, public Palomar entry, permanent ID or version verified here.

## Stop/go

**NO GO until** exact final source SHA passes: full modern imported Lean library, direct Challenge + Solution and actual axiom print, official `bash scripts/verify-comparator.sh` using bundled NanoDa and con-ron, complete Python/exact/census, blocking source/metadata preflight, and both push and PR CI. Inspect **complete** GitHub job logs at their URLs; do not infer success from step names or stale SHA. Only then mark PR ready and merge; independently recheck public merged commit.

**After code go:** owner authenticates and controls final submission registration consent at https://submit.palomar-registry.org/ ; only a verifiable public entry/ID/version matching the reviewed source changes status to REGISTERED. **No paper before that.** Next: [S048](../sessions/S048.md).
