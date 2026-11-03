# S025 execution handover — 2026-11-03

**Branch:** `s025-real-bin-cells` from `main` 500d7281f9ec.
The first new theorem block in `InverseGreedy/ExpBinCells.lean` is imported and **Lean-verified** at exact SHA `9336b4458a4ba0abf9c52e45c8cf0399837f8edd`: both imported Lean and all Python/exact/certified-census passed in [Actions 41598092129](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598092129). Before this success, earlier drafts had two Lean proof-script failures: incorrect `measure_sdiff` arguments and `ENNReal.ofReal_sub` orientation; both are repaired.

**Mathematical advancement (IG-L38):** From the *genuine* exponential survival measure in S024, prove the actual `Ioc a b` probability `exp(-ra)-exp(-rb)` for `r>0`, `0≤a≤b`. Deduce exact geometric real-bin mass `(1-e^{-rδ})e^{-rkδ}` for all positive real `r,δ` and `k : ℕ`; the proof uses exponential addition, induction and endpoint-measurable sets, not the S018 discrete priority law. S025 also adds a finite-coordinate event theorem; check its exact final CI separately.

**Exact tests:** `tests/test_s025.py` includes five `Fraction` consistency groups for real exponential-survival bin algebra, finite box products, and independent two-clock finite sums. `proof/S025_REAL_CLOCK_CELLS.md` sets out the rigorous distinction between a real-cell probability and an actual floor-valued bin map.

**Not completed in Lean:** floor/bin PMF, independence of binned clocks, `Pr(T_r<T_s)=r/(r+s)`, all strict sorting-chamber masses and continuous sorted greedy-output pushforward. `sessions/S026.md` installs these targets. Partial atlas remains **90 EGU / 8 non-EGU / 45 unresolved**; no independent novelty certificate.

**Release:** final PR/head CI and merge must be appended after both jobs pass at the *same final head*.

---

# S024 FINAL RELEASE — 2026-11-03

**Verified and merged:** [PR #23](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/23) exact final head `3dc4332ea304b15dcbc5b005f48eb5a7c4972837` passed BOTH the imported Lean build and complete Python/exact/certified-graph-census in [push Actions 41596092382](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41596092382) and [PR Actions 41596101126](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41596101126). Squash-merged to `main` as `be7859cce0dba3613acae9fb47b1f0017206396c`. S024 closes genuine one-clock exponential survival, actual finite-clock coordinate tails and almost-sure all-coordinate nonnegative support (IG-L36/IG-L37), with exact rational checks. Numerical unequal-rate pair race, finite geometric-bin measures, strict chamber masses and continuous greedy-output pushforward remain **Lean-open**. S025 is installed. Atlas **90 EGU / 8 non-EGU / 45 unresolved**; no independent novelty claim.

---

# S024 — genuine exponential survival, 2026-11-03

**Execution PR:** [#23](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/23),
branch `s024-exp-survival` based on main `5adfe08427d7`.
The first full imported Lean and Python/certified census verification
**passed on exact code SHA `8f52f3a8a1b9266bf2664a5b611f2194847d529e`**
in [Actions 41595641100](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41595641100).
An earlier draft `db78f855` failed on two minor elaboration errors
in the negative-time support lemma; both were repaired and CI passed
at `e98804be`, before the finite all-nonnegative theorem.

**Verified mathematics (IG-L36, IG-L37):**
`InverseGreedy/ExpSurvival.lean` proves, from actual Mathlib
exponential CDF and complement rather than a discrete assumed law,
`Pr(T_r>t)=exp(-r*t)` for all `r>0,t≥0`, correct negative-time
zero lower-tail support, and the exact finite coordinate survival
law. It also proves all coordinates of a finite independent Exp family
are nonnegative almost surely, for empty/singleton index types too.

**Independent exact regression:** `tests/test_s024.py` uses `Fraction`
for four consistency groups covering CDF, tail, bin differences,
finite partial sums, and independent family products at rational
survival bins. All four passed locally. These do not replace the
continuous measure proof.

**Release checkpoint:** Exact final PR head verification and squash
merge must be recorded only after both final-head CI jobs pass.
S025 is installed. The real-clock `Pr(T_r<T_s)=r/(r+s)`,
geometric-bin probability law, all finite strict chamber masses,
and continuous sorting/greedy pushforward are **Lean-open**.
`proof/S024_EXP_SURVIVAL.md` spells out the remaining obligations.
Graph atlas unchanged **90 EGU / 8 non-EGU / 45 unresolved**.
Independent novelty is not claimed.

---

# S023 FINAL RELEASE — 2026-11-02

**S023 FINAL RELEASE:** [PR #22](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/22) exact final branch head bfb0d2cd6d03ca874b026527b0e19c06cc471442 passed BOTH full imported Lean and Python/certified census in [push run 41536696192](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41536696192) and [PR run 41536741787](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41536741787). Squash-merged to main as 83a4390f69ac04621fa64498d41be93f74fc4c33. Only chamber measurability is Lean-verified, not continuous chamber mass or sorting pushforward. S024 installed. Atlas unchanged 90/8/45.

---

# S023 execution handover — 2026-11-02

**Branch:** s023-geometric-bin-chamber based on main c3c4721f802b45d839f229acee8f60296f655970.

**Verified checkpoint:** Imported Lean theorem strictClockChamber_measurable defines strict-order events for actual finite real-function clock spaces and proves their measurability. BOTH full imported Lean and Python/certified census passed at exact code SHA 6faf5ba21bf585a52412f8e2269e376a03b2de45; [Actions 41536043877](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41536043877). This checks event measurability only, not chamber probability. Re-check exact final PR head after subsequent changes.

**New mathematical bridge (IG-P13):** proof/S023_GEOMETRIC_BIN_CHAMBERS.md gives a complete alternative informal proof of arbitrary positive-real finite continuous exponential sorting probabilities using an explicit geometric-bin chamber product, a nonasymptotic pair-collision error bound and limit to the usual orderMass product. It builds on genuine exponential survival and independence, not the discrete weighted-priority law. This is **not Lean-verified** for the full limiting theorem.

**Regression:** tests/test_s023.py uses exact fractions and separate gap-versus-memoryless algorithms for integer-rate bin laws, as well as S022 pair-oracle checks, four/smaller vertex enclosures, and zero/one boundaries. Check final CI outcome.

**Next:** sessions/S024.md targets the true exponential survival theorem, bin distribution, pair ratio, all-chamber masses and sorting pushforward. These remain **Lean-open**. The graph atlas stays 90 EGU / 8 non-EGU / 45 unresolved; no novelty certificate.

---

# S022 FINAL RELEASE — 2026-11-02

**Merged:** [PR #21](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/21)
was squash-merged into `main` as
`71a84f55197fc79170bf98fc177ce33d6a86e58d`.
The **exact final PR head**
`c9df8f4aab9303b89eafb8072c3597909536ebc1`
passed BOTH imported Lean and full Python/certified census in
[Actions 41475826383](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41475826383).
The initial imported proof had one elaboration failure, corrected
in `946a9c92` which also passed both jobs. The new rational-bin
regressions passed together with full CI at `4a2a5cc7` and at
the exact final head.

**Verified new result (IG-L34):** Under the genuine Mathlib finite
product of strictly positive-real exponential measures, any distinct
two coordinate clocks have the exact independent product joint law;
therefore their tie event is null. The union of all distinct-clock
ties is null and the all-distinct-clock event has probability one
for **arbitrary finite index types including empty and singleton**.
This is actual continuous measure theory, not an algebraic or
discrete-law surrogate.

**Boundary:** The numerical unequal-rate probability
`P(T_r<T_s)=r/(r+s)`, probabilities of complete strict sorting
chambers and real-clock greedy output pushforward are **NOT**
Lean-verified by S022. `sessions/S023.md` is installed for those.
Independent novelty remains unverified. Connected n≤6 partial
atlas unchanged: **90 EGU / 8 non-EGU / 45 unresolved**.

---

# S022 execution checkpoint — 2026-11-02

**PR:** [#21](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/21),
branch `s022-finite-clock-no-ties`. New imported Lean module
`InverseGreedy/FiniteClockNoTies.lean` gives actual two-coordinate joint
laws and null ties, then probability-one pairwise-distinct times for
any finite clock family. Strictly positive real rates; empty and
singleton index types included. The proof invokes S020 independence
and actual marginal laws and S019 product-measure zero-diagonal,
not an assumed Plackett-Luce distribution.

**CI status:** first imported branch head `2cdf7e1d` failed Lean
because `measure_add_measure_compl` needed an explicit measure
parameter. Earlier goals had compiled. Corrected at `946a9c92`;
record the exact final dual-green SHA here only *after* verifying both
jobs. The four-method independent `tests/test_s022.py` exact rational
binned-Exp regression was also added. `proof/S022_FINITE_NO_TIES.md`
contains the measure proof and analytic boundaries.

**Still open:** numerical real-clock race probability, finite sorting
chamber law, continuous clock-output pushforward and the 45 unresolved
six-vertex connected graphs (atlas 90/8/45). `sessions/S023.md`
installed to continue.

---

# S021 FINAL RELEASE — 2026-11-02

**Merged:** [PR #20](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/20),
exact final head `ef41930888d2aca53f538777bbfd30604d81e358`
passed **both** imported Lean and complete Python/certified census in
[push Actions 41445715430](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41445715430)
and [PR Actions 41445751233](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41445751233).
Squash-merged into `main` as `e02afe3769d5f6ff2a787a21dbb8cc13330243fa`.

**Precisely certified (IG-L32, IG-L33):** genuine continuous unequal-rate
product-law swap and reverse-winner event equality; measurability of finite
pair-comparison, tie, all-distinct-clock and specified first-winner events.
No real-clock race ratio, pairwise null-tie probability for finite
products, full sorting law or end-to-end clock/greedy pushforward was
Lean-proved. The independent `tests/test_s021.py` replica oracle and
all existing Python/census tests passed on the exact final head.

**S022 installed:** `sessions/S022.md`; target actual
`P(T_r<T_s)=r/(r+s)` measure-level integral and finite null ties, sorted
chamber probabilities and continuous clock-to-greedy bridge.
Partial atlas unchanged: **90 / 8 / 45**. No independent novelty claim.

---

# S021 checkpoint — 2026-11-02

**Branch:** `s021-continuous-race-swap`.
**First verified imported Lean checkpoint:** exact commit
`d105af449ef545d8f12ea519db4f2816dac649ff`,
[Actions 41445042808](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41445042808):
both Lean and complete Python/certified census jobs succeeded.

**New true-measure Lean results (IG-L32):** At arbitrary positive real
rates the product of actual independent `expMeasure` laws transforms under
coordinate swap into the continuous product with swapped rates; therefore
the probability of the reverse strict-winner event at `(r,s)` equals the
probability of the forward event at `(s,r)`. Neither result assumes or
derives a discrete first-choice law.

**Event measurability (IG-L33):** Finite-indexed strict-comparison and
equality events were imported and compiled at the above SHA. The
all-pairwise-distinct and specified first-winner events were added later;
verify their own exact-head CI before upgrading that status.

**Independent exact checks:** `tests/test_s021.py` counts unit-rate
Exp(1) replica arrival permutations, testing the genuine grouped-minima
law with positive **integer** rates. Four tests passed locally, including
1:7 and 7:1 races, multi-clock chambers, relabelling, and empty/singleton
boundaries. See `proof/S021_CONTINUOUS_RACE_SYMMETRY.md`.

**Remaining major obligations:** the actual unequal-rate
`P(T_r<T_s)=r/(r+s)` integral identity in Lean, finite pairwise no-ties,
all-chamber probability `orderMass`, and the continuous clock-order
pushforward to S018's proved discrete greedy law. S022 is installed for
those gaps. No new EGU atlas cases: 90/8/45. No novelty claim.

**Release:** this entry is a verified *checkpoint*, not a claim of
final-head CI or merge. Record final verification and release below or
above once known.

---

# S020 FINAL RELEASE — 2026-11-02

**Merged:** [PR #19](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/19) final head `e55b90e13a9738d676d953aae8e2ae6c1df312dd` passed **both imported Lean and full Python/certified census** in [Actions run 41443533808](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41443533808). PR #19 was **squash-merged** into `main` as `9fe340889d9e08d9d1d3c3895795617676da30eb`. The code and docs in this release cover IG-L30 and IG-L31; `sessions/S021.md` is installed. The next open theorems are the arbitrary-rate comparison formula and the all-finite-clock sorting/chamber law. Atlas unchanged: 90 EGU / 8 non-EGU / 45 unresolved. No independent novelty claim.

---

# S020 continuous-race partition — 2026-11-02

**PR:** [#19](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/19),
branch `s020-continuous-race-partition`.

**Verified proof checkpoint:** Imported `InverseGreedy/ContinuousRacePartition.lean`
and the complete Python/certified census both passed at **exact code SHA
`253de8d502ec1b91a29d6eb134baf6422d44ba19`**, [GitHub Actions
41442175794](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41442175794).
This verifies the new true continuous product-measure statement,
not the full independent-clock-to-discrete-order equivalence.

**New formal results (IG-L30):** For any `r,s>0`, the disjoint
events `T_r<T_s` and `T_s<T_r` have probabilities summing to one,
by the S019 null-tie result and measure additivity. For equal rates,
`Measure.prod_swap` implies swap invariance and equal probability of
these two events, hence the balanced identity (informally each is 1/2).
The proof makes no assumption that the clock law equals the discrete
Plackett–Luce law. Formal code is at
`InverseGreedy/ContinuousRacePartition.lean` and the mathematical
explanation is at `proof/S020_TWO_CLOCK_PARTITION.md`.

**Finite-product checkpoint (IG-L31):** The imported `InverseGreedy/FiniteIndependentExp.lean`
defines a genuine `Measure.pi` product of positive-rate exponential measures
over any finite index type. It proves probability normalization (including the
empty index type), measurable coordinate projections, exact `expMeasure`
coordinate marginals, `iIndepFun` of the entire indexed clock family,
and the probability-zero fixed-time cylinder for each coordinate.
**Both imported Lean and Python/certified census passed** at exact code
SHA `f92f6c807f5241768b53ccba11cd38a60ed19968`,
[Actions 41443061251](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41443061251).
See `proof/S020_FINITE_CLOCK_MODEL.md`. No all-distinct-clock or sorting
event theorem has been formalized.

**Still open:** the arbitrary positive unequal-rate comparison
`P(T_r<T_s)=r/(r+s)` in Lean; finite indexed products, null ties,
sorting measurability, event probabilities `orderMass` and the
full real-clock greedy output pushforward. See `sessions/S021.md`.
The 143 connected graphs through six vertices remain 90 proven EGU,
8 proven non-EGU, 45 open. No novelty certification.

**Release status:** Verify dual-green **exact final PR #19 head**
after documentation commits; the initial code-only green checkpoint
does not automatically verify the final PR head. Record final SHA
and merge result once confirmed.

---

# S019 release and execution handover — 2026-11-02

**S019 exact-final-head release:** PR [#18](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/18) final head `d1a5c3d34fd2dbd10dec7a5691e9a79a8524d733` passed both imported Lean and full Python/certified census in [Actions 41421511927](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41421511927), and was squash-merged to `main` as `fafc4a43313494b1561ebea5d7c18658aa9c3397`. The S019 general continuous-clock ordering theorem remains Lean-open; `sessions/S020.md` is installed.


**Mathematical boundary:** The complete finite-dimensional exponential-order
density/chamber argument is now written down, but **the all-finite-clock
`orderMass` equivalence is NOT Lean formalised**. In Lean, S019 proves only
the genuine two-clock product measure, its probability normalisation,
the exponential coordinate marginals and independence, exponential
point-nullity, and zero probability of a tie.

**Verified code checkpoint:** All imported Lean modules and full
Python/certified census passed at code SHA
`b6417d43755f94b216ba1212772bd8b0563e45a7`,
[Actions 41421076123](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41421076123).
PR [#18](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/18)
on branch `s019-independent-exp-clocks` needs final-head
dual-green CI confirmation before merge; this code checkpoint is not
automatically the final documentation head.

**Files:** `InverseGreedy/IndependentExpPair.lean`, project import,
`proof/EXPONENTIAL_CLOCK_BRIDGE.md`, `tests/test_s019.py` and
`sessions/S020.md`. Two new deterministic analytic regression tests
passed locally and are included in the full Python job. The CI green
checkpoint is the stronger verification.

**Next:** S020 targets the actual two-clock comparison probability
directly from product measure, then finite indexed product measure and
sorting event probabilities. Retain strict positivity and empty/singleton
boundaries. Do not infer these further results from S019's independent
coordinates alone. Connected n≤6 census: **90 EGU / 8 non-EGU /
45 unresolved**. No publication or novelty certification.

---

# S018 execution handover — 2026-11-02

**Final S018 release:** S018 PR #17 was squash-merged to main at `34d3b9ce72e8413055dd6d0404c1d94081c99c78` after both imported Lean and full Python/certified census succeeded on the exact final PR head `217c38964f69a76cb3c7c93863a412ca27c4def1`, [Actions 41417531293](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41417531293).

**Branch:** `s018-greedy-pushforward`, PR #17. Code theorem Lean-verified; final PR-head release verification required.
The first major S018 theorem, `weighted_priority_projection_expectation`,
was **imported Lean verified** with complete Python/certified census at SHA
`75460ab146bf0dc3fbe646f198b729f1af788cdc`,
[Actions 41415466242](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41415466242).

Added formal modules `PriorityProjectionPushforward.lean`,
`PriorityProjectionEvent.lean` and `PriorityOutputPushforward.lean`,
plus `proof/GREEDY_OUTPUT_PUSHFORWARD.md` and `tests/test_s018.py`.
The paper proof deduces the conditional greedy first-choice recurrence
by deleting blocked tail priorities **in the weighted law**, then
identifies it with `finiteRaceLaw` by induction. The full imported
Lean pushforward theorem **compiled successfully at code SHA
`3a3ea03d12b0752815fa6f6f6111ab58bdd5f1ff`**, with both
Lean and Python/certified census passing in [Actions 41417057969](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41417057969).
PR [#17](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/17)
has been squash-merged after both jobs passed at its **exact final head**.
Follow later CI from the final commit for the actual release status.

Continuous independent Exp-clock ordering equivalence is a distinct
open obligation, handed to `sessions/S019.md`. No new EGU atlas
classification: 90 positive / 8 negative / 45 unresolved.

---

# S017 handover — 2026-11-02

**S017 released to main:** PR #16 was squash merged as
`bd67b5ccad0c429a3d1c10b73ba6105974088652`.
Exact final PR head
`7b1d6b127491bc0eb3bc71e5146ec767d1b17d8c`
passed both imported Lean and complete Python/certified census in
push [Actions 41409002580](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41409002580)
and PR [Actions 41409033377](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41409033377).
[PR #16](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/16).
The **full all-target theorem** (including off-support zero) compiled
at that head, not just the supported-order induction.


S017's central imported Lean proof is the *complete weighted
retained-permutation law*, valid for all finite active/retained
sets and strictly positive real rates. New
`InverseGreedy/FullProjectedOrderExact.lean` proves that
`projectedOrderMass` agrees with `orderMass` for each complete
retained list. S015's exact zero-support theorem supplies the
all-target extension. The proof uses S014's event-level head
recurrence and the now-public S016 fixed-point identity. It
inducts over actual complete permutations, not a postulated
independent restricted race.

**Verification:** imported Lean build and Python-exact/certified
census both succeeded on S017 code SHA `0330a640`, Actions
[41408600557](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41408600557).
An all-target Lean wrapper was subsequently added; verify its
own final-head CI before claiming it compiled or merging.
The independent Fraction tests in `tests/test_s017.py`
cover 95 retained subsets of nine unequal-rate vertices and
conditional residual laws on eight vertices.

**Open boundary:** `priorityOutputMass = finiteRaceLaw` in Lean
and the independent Exp-clock ordering semantics remain open.
No new atlas cases or independent novelty claim: still 90 EGU /
8 non-EGU / 45 unresolved connected graphs through six vertices.
S018 is installed in `sessions/S018.md`.

---

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
