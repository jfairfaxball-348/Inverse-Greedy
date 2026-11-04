# S039 provisional handover — 2026-11-04 (PR/CI pending)

## S039 partial execution — 2026-11-04 (CI/merge pending)

Branch `s039-clock-suffix-geometry` adds imported
`InverseGreedy/FiniteClockGapFactors.lean`: true exponential
geometric ratios `q_i=exp(-rates_i δ)` are strictly between 0 and 1
and every nonempty positional suffix product `Q_a` is likewise;
hence every proposed geometric denominator `1-Q_a` is positive.
These are formal preconditions for evaluating S038's true measured
countable gap series; they do **not** evaluate that series in Lean.

Independent exact `tests/test_s039.py` validates finite gap-monomial
factorisation and truncated/closed geometric products for up to four
coordinates. Proof note `proof/S039_SUFFIX_GEOMETRY.md`; next
`sessions/S040.md`. The multivariate ENNReal pointwise factorisation,
measured geometric closed product, δ↓0+, real-clock chamber formula,
measurable sorting and real greedy-output pushforward remain Lean-open.
**Do not call Lean-verified until exact-final-head CI is green in both
push and PR runs.** Atlas 90 EGU / 8 non-EGU / 45 unresolved, unchanged;
no novelty/registration claim.

**Release gate:** require final head SHA and successful complete Lean plus Python/exact/certified n≤6 census in BOTH push and PR runs before merge; record their workflow IDs and squash SHA afterward. No claim of full continuous theorem.

---

# S038 final handover — 2026-11-04 (verified partial release)

Exact final PR head `212f0d8a6e7aed1337f3fe6726cd88480f45d384` passed **both full imported Lean and complete Python/exact/certified connected n≤6 census** in **both** push [Actions 41896636575](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41896636575) and PR [Actions 41896648063](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41896648063); [PR #38](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/38) squash-merged into `main` as `f67768d261884cc87a729fbafa3d0632b1f34312`.

Branch `s038-measured-gap-reindex`, [PR #38](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/38), starts at verified S037 `main`. Verified imported modules `InverseGreedy/FiniteClockCompleteOrder.lean` and `InverseGreedy/FiniteClockMeasuredGapSeries.lean` make the no-repeat/full-coverage hypothesis explicit and use it to reindex **S035's actual independent Exp-clock measured countable series** via S037 finite gaps. This does not evaluate the multiple geometric sum or prove any n≥3 continuous-clock order mass. `tests/test_s038.py` provides separate exact rational tests; scope note `proof/S038_MEASURED_GAP_REINDEX.md`; next `sessions/S039.md`.

**Release gate fulfilled:** the exact final head is verified as successful in the imported Lean and Python/exact/certified census jobs in **both** push and PR workflow runs, and PR #38 was squash-merged. Next: `sessions/S039.md`. Preserve atlas **90 EGU / 8 non-EGU / 45 unresolved**, no novelty/registration claim.

---

# S037 final handover — 2026-11-04 (verified partial release)

Exact final PR head `8043465835fed9b1245b98f1e1e59bfe743dae8b` passed the complete imported Lean build and full Python/exact/certified connected n≤6 census in **both** push [Actions 41875794221](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41875794221) and PR [Actions 41875873962](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41875873962); [PR #37](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/37) squash-merged to `main` as `93c20facf8d3e396374aa066e6b46b266312431f`.

Work branch `s037-gap-inverse` extends S036 with imported `InverseGreedy/FiniteClockGapInverse.lean`: consecutive finite-difference gaps, both explicit inverse identities and `finiteGapBinEquiv n` (including `Fin 0`). The additional vector injectivity is different from S036's position-injectivity. Exact `tests/test_s037.py` checks *complete* finite permutations and refuses repeated/incomplete lists; these tests do not establish a genuine measured infinite series or stochastic limit. Proof note `proof/S037_GAP_INVERSE.md`; next `sessions/S038.md`.

Still pending: transfer the equivalence through complete vertex enumerations to S035's actual measured countable series; ENNReal multiple geometric evaluation and `δ↓0` analytic limit; genuine continuous-clock order law, measurable sorting and greedy-output pushforward. Census **90 EGU / 8 non-EGU / 45 unresolved** unchanged. No independent novelty or Palomar/arXiv submission.

---

# S036 final handover — 2026-11-04 (verified partial release)

Exact final PR head `badc40d639370827930a5a93681ae9c56daf43ff` passed **both imported Lean and complete Python/exact/certified connected n≤6 census** in push [Actions 41858484562](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41858484562) and PR [Actions 41858495527](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41858495527); [PR #36](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/36) squash-merged into `main` as `9161943595035a17a07a66ee1b3c6251e945f540`.

Starting from S035's **genuine continuous-clock** strict-bin chamber countable measure series, S036 adds imported `InverseGreedy/FiniteClockGapEncoding.lean`. For arbitrary `gaps : Fin n → ℕ`, its `gapBinValue` is `k_j=j+Σ_(a≤j)d_a`. Lean proves strict monotonicity, position-injectivity, `j≤k_j`, and the true adjacent recurrence `k_(j+1)=k_j+1+d_(j+1)`. These are strictly **forward** encoding lemmas, not the full gap-coordinate bijection or a measured geometric-series evaluation. Code was compiled at exact final head in both events.

Independent `tests/test_s036.py` exhaustively verifies the two-sided finite gap/bin encoding and exact rational monomial factorisation, but **does not** Lean-formalise them. `proof/S036_GAP_ENCODING.md` records the complete paper derivation and exact boundary, and `sessions/S037.md` is installed to tackle the Lean inverse, genuine S035 sum reindexing, multiple-geometric evaluation, zero-width n≥3 actual strict-clock chamber law, total measurable sort and continuous greedy-output pushforward. No conclusion about those pending proofs follows from the new gap lemmas. Connected n≤6 atlas remains **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty and registration not claimed.

# S035 final handover — 2026-11-04 (verified partial release)

Exact final PR head `2edf01c7da105403ac75c8959fce292a34da34ce` passed **complete imported Lean** and **full Python/exact/certified connected n≤6 census** in both [push Actions 41823819781](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41823819781) and [PR Actions 41823826234](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41823826234); [PR #35](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/35) was squash-merged to `main` as `4aa7459c5bd1a66a612134d106c467ff3d2d7000`.

Started from `main` `09912950920f4121a0750f002dbfb5598b83e21c`, after S034's verified merged release. The S035 branch `s035-positive-bin-series` introduced imported `InverseGreedy/FiniteClockBinSeries.lean`, independent `tests/test_s035.py`, `proof/S035_BIN_SERIES.md`, and installed `sessions/S036.md`.

The new formal result is an **actual-clock measure** statement: on all-positive one-based ceiling bins, the strict-bin chamber is exactly a disjoint countable union of measurable admissible joint cylinders; S032's genuine independent Exp joint law gives their masses. S033 zero-bin exception is null, so the resulting countable geometric series equals the full strict-bin chamber probability. The proof is not an assumed discrete ordering law and handles empty/singleton types without separate exceptions.

**Still Lean-open:** finite geometric evaluation of the multiple series, the δ→0 limit of that product to the discrete `orderMass` formula, continuous n≥3 strict-real-clock chamber probability, total measurable sorting and actual continuous greedy-output pushforward. S036 must proceed from the genuine S035 series, not an unverified sorting-law assumption. Connected n≤6 atlas remains **90 EGU / 8 non-EGU / 45 unresolved** with existing snapshot flags; no novelty/Palomar registration.

---

# S034 final handover — 2026-11-04 (verified partial release)

Exact final PR head `32c28558efe9d685d2ac7123bd2ba2887890c898` passed the **complete imported Lean** build and **full Python/exact/certified connected n≤6 census** in both [push Actions 41807976461](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41807976461) and [PR Actions 41807983429](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41807983429); [PR #34](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/34) was squash-merged into `main` as `e7947eb1382e8838485e7b761615f2bb8cf4442e`. 

Started from GitHub `main` `eb5966a0d284d9ed8c75ea8894e3eb2aa783c73e`, with S033 [PR #32](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/32) already merged and certified at its exact PR head. S034 [PR #34](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/34) adds imported `InverseGreedy/FiniteClockBinUnion.lean`, independent `tests/test_s034.py`, `proof/S034_FINITE_UNION.md` and `sessions/S035.md`. The imported Lean and complete Python/exact/certified census jobs were green at the exact final head in both push and PR Actions, and the PR was squash-merged.

The new finite ENNReal sum controls the genuine probability of some two *list positions* sharing an actual ceiling bin by the sum of S033's true exponential pair-marginal collision bounds. A hypothesis explicitly forbids repeated vertex indices across different list positions. There is no completeness condition, so all complete permutations qualify; empty and singleton lists have zero collision probability. Combining it with the true S033 chamber sandwich gives a quantitative `O(δ)` error for any fixed finite distinct list. This alone **does not** evaluate strict-bin chamber mass or prove the full n≥3 real chamber product; nor does it identify the real-clock sorting/greedy pushforward. S035 targets the remaining countable disjoint geometric summation and zero-width limit, then total sorting map.

Preserve n≤6 connected atlas **90 EGU / 8 non-EGU / 45 unresolved**, no novelty certification.

---

# S033 final handover — 2026-11-03 (verified partial release)

exact final PR head `6b57057e6711b4d17d183a277305a0e08376eba9` passed imported Lean and full Python/exact/certified connected-n≤6 atlas in BOTH [push Actions 41692437332](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41692437332) and [PR Actions 41692441926](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41692441926); [PR #32](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/32) squash-merged as `025cf356d0afa8fcefeb12191103b51703fe4d6a`.

[S033 PR #32](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/32) begins from `main` `3257a14e1d86ea8ed0f7d35a9e3c31bfee1d3227`; this `main` includes verified S032 PR #31 (`dffde518...` dual green and squash merge `c9659d7...`). Merged S033 branch `s033-finite-bin-chamber-sandwich` introduces `InverseGreedy/FiniteClockBinChambers.lean`, `InverseGreedy/FiniteClockPairBinCollision.lean`, exact `tests/test_s033.py`, `proof/S033_BIN_CHAMBER.md`, and `sessions/S034.md`.

**Lean-verified partial actual-clock results:** true-clock strict-bin ⊆ real-chamber ⊆ strict-bin ∪ list same-bin collision, its genuine finite exponential measure sandwich, and the true finite-family pair collision estimate `P(Kδ(T_i)=Kδ(T_j))≤δ·min(r_i,r_j)` for distinct indices. There is **no** complete Lean n≥3 chamber product or continuous greedy-output law yet. The finite list collision union bound, summation of strict-bin joint geometric cylinders, zero-width product limit, and measurable total sort remain precisely for S034. `tests/test_s033.py` independently checks the event implications and rational collision algebra, not a stochastic continuous proof.

**Release gate satisfied:** the exact final PR head passed both complete Lean and full Python/exact/certified connected n≤6 atlas in BOTH push and PR Actions and was squash-merged. No novelty or registration assertion. Atlas **90 EGU / 8 non-EGU / 45 unresolved**.

---

**S032 FINAL RELEASE (2026-11-03):** [PR #31](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/31) exact final head `dffde518c3727c4c1fcde4789dc2773ee65e6c62` passed **both imported Lean and complete Python/exact/certified connected-n≤6 census** in BOTH [push Actions 41677475236](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41677475236) and [PR Actions 41677479044](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41677479044). Squash-merged to main as `c9659d7b4b0ebcc7d7dd297852ba4ea5bca96602`. This verifies the **genuine full finite-family simultaneous ceiling-bin probability** and true two-item/repeated-index strict chamber facts; NOT the full n≥3 sorting-chamber product or real-clock greedy-output pushforward. An explicit multi-geometric gap-series formula has a separate informal mathematical derivation and exact rational regression, not Lean proof. `sessions/S033.md` installed. Atlas **90 EGU / 8 non-EGU / 45 unresolved**; novelty not independently certified.

# S032 final handover — 2026-11-03

The session started from `main` SHA `098f4f954aa3f85734c93af384db52e35815c992`, with verified S031 PR head `09d0b45d` and dual green push Actions 41650444708 / PR Actions 41650452725. S032's exact **final** head `dffde518c3727c4c1fcde4789dc2773ee65e6c62` is certified for **both imported Lean and full Python/exact/certified n≤6 graph census** in BOTH push [41677475236](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41677475236) and PR [41677479044](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41677479044); [PR #31](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/31) squash-merged to main `c9659d7b4b0ebcc7d7dd297852ba4ea5bca96602`.

The imported `InverseGreedy/FiniteClockJointBins.lean` now establishes a **genuine complete finite-coordinate geometric-bin joint law** from the actual independent real-clock product measure via Mathlib `Measure.pi_pi`, rather than assuming discrete priority law. It also verifies actual two-item chamber ratio and impossible repeated-index chambers. `tests/test_s032.py` independently checks rational finite-product geometric bins, exact multi-gap factorisation and deterministic chamber facts. `proof/S032_JOINT_BINS.md` provides the **informal** all-n strict-bin multiple-series formula and its positive-rate justification; it is **not yet a Lean proof**.

Still Lean-open: full real finite n≥3 strict chambers (sum the new geometric joint bins, control collisions and take zero-width limit), canonical measurable tie-broken total clock order, and the measured greedy-output identification with S018's Lean-proved discrete law. The next execution prompt `sessions/S033.md` is installed for these precise obligations. No new EGU graphs or certified novelty. Connected n≤6 **90 EGU / 8 non-EGU / 45 unresolved**.

---

**S031 FINAL RELEASE (2026-11-03):** [PR #30](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/30) exact final head `09d0b45ddcae35714c1cf0a03af57d62a900781c` passed **both imported Lean and Python/exact/certified connected-n≤6 census** in BOTH [push Actions 41650444708](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41650444708) and [PR Actions 41650452725](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41650452725). **Squash-merged into main as `06db312e37c7fa9bf05718d7297f43e2cf5405c0`.** Lean now proves genuine finite-family pairwise comparison probabilities and strict-chamber pair upper bounds, plus empty/singleton chamber mass one. The **full n≥3 continuous chamber product** and **true real-clock greedy-output pushforward** remain Lean-open. `sessions/S032.md` installed. Census **90 EGU / 8 non-EGU / 45 unresolved**; novelty not independently certified.

# S031 execution handover — 2026-11-03 (PR #30; merged and verified)

The next session is `sessions/S032.md`. The S031 branch
`s031-finite-clock-pair-chambers` originates at main
`b190fae9e42d6598d5b53873007ae349aa1f9e78`. Final verified merged release:
[PR #30](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/30)
and its **exact final SHA**, both imported Lean and complete Python/exact/
certified n≤6 census jobs in BOTH push and PR GitHub Actions, before merge.

Imported `InverseGreedy/FiniteClockPairOrder.lean` proves under the
**actual** finite `Measure.pi` exponential product and positive rates:
(1) any distinct-coordinate strict clock comparison has exact mass
`ENNReal.ofReal(rate_i/(rate_i+rate_j))`, transporting the genuine S030
two-clock result via S022's true pair joint map; (2) any strict chamber
is a subset of every required pair-comparison event, giving a true
measured rate-ratio upper bound; (3) universal chamber probability one
for empty and singleton proposed order lists. No discrete priority
measure is used to justify these actual-clock claims.

`tests/test_s031.py` adds exact independent `Fraction` regressions;
`proof/S031_FINITE_CLOCK_PAIR.md` records the rigorous proof and gap.
The **general n≥3 full chamber product is NOT formally established**:
pairwise ordering marginals cannot determine a full joint order law.
The measurable tie-broken sorting map, its true pushforward, and the
continuous greedy-output identification with S018's formal discrete
`finiteRaceLaw` also remain Lean-open; S032 targets these and must
land only verified partial results if a complete proof is not found.

Connected n≤6 census remains **90 EGU / 8 non-EGU / 45 unresolved**;
no independent novelty certificate, Palomar or arXiv submission.

---

**S030 FINAL RELEASE (2026-11-03):** [PR #29](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/29) exact final head `94cef7edb07d9e45de559d9c6d02cd1a3d60d572` passed **both complete imported Lean and Python/exact/certified connected-n≤6 census** on BOTH [push Actions 41647662604](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647662604) and [PR Actions 41647671351](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647671351); **squash-merged into `main`** at `abadb58e6b4583729d084b66c1e9096041ce1eb4`. Lean now formally proves the **actual independent continuous exponential two-clock inequality-event mass** `P(T_r<T_s)=ENNReal.ofReal (r/(r+s))` for any r,s>0, using the real analytic small-bin limit and S029 true measured-event squeeze. The full finite strict ordering chamber law and continuous-clock greedy-output pushforward remain **Lean-open**; `sessions/S031.md` installed. Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty unverified.

# S030 execution handover — 2026-11-03

**Branch/PR:** `s030-continuous-race-limit`, [PR #29](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/29), based on `main` `d3f75bf1d0f2100750f49a4b453ff066a1a674e0`.

**Certified code checkpoint:** `0144a168dd0dfd0ff90d4ea5f089f0bbc55ed319`, with imported Lean + complete Python exact tests, exact demo and certified connected graph n≤6 census, **both GREEN on exact same head**, [push 41647056971](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647056971) and [PR 41647064745](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647064745). `InverseGreedy/ContinuousRaceLimit.lean` imports S029 actual measured exponential-bin sandwich/collision bound; proves exponential CDF initial slope, strict-bin real analytic right-limit, ENNReal lift, and the actual continuous unequal-rate product-measure winner law `independentExpPair_realWinner_rateRatio`, not a declared priority surrogate. `tests/test_s030.py` adds independent symbolic regression; `proof/S030_RATE_RATIO.md` gives mathematical details.

**Outstanding release gate:** after docs updates, verify both push and PR Actions jobs on the exact *final* head SHA and squash-merge only when dual green. **Next session S031** installed: prove genuine finite exponential sorted strict chamber probabilities (empty/singleton included), measurable canonical tie-breaking sort, and real-clock greedy-output pushforward to prior discrete finiteRaceLaw. These are still Lean-open even with the pair theorem. Atlas 90 EGU / 8 non-EGU / 45 unresolved; no novelty or Palomar/arXiv certification.

---

**S029 FINAL RELEASE (2026-11-03):** [PR #28](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/28) exact final head `3c2150a8668fd3869318810f9e02eb65289d47e8` passed **both imported Lean and full Python/exact/certified connected-n≤6 graph census**, on BOTH [push Actions 41625700011](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41625700011) and [PR Actions 41625709665](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41625709665). **Squash-merged into `main`** as `bc586f6c679fe1a49db3e3127ab0e8c5f5727ca0`. Lean now verifies the genuine real-clock/bin-event measure sandwich, S028's exact real-fraction wrapper and the true collision bound `P(same ceiling bin) ≤ δ·min(r,s)` for all positive rates/widths. The **analytic zero-width limit**, continuous rate ratio `P(T_r<T_s)=r/(r+s)`, finite sorting-chamber masses and actual real-clock greedy-output pushforward remain **Lean-open**. `sessions/S030.md` installed. Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty unverified.

# S029 execution handover — 2026-11-03

**PR:** [#28](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/28); branch `s029-continuous-race-sandwich`, based on `main` `37f7ddfde2f56eae757191eacf2885950711e4b5`.

**Verified checkpoint:** imported Lean + complete Python/exact/certified connected graph census passed at SHA `06bd1baa4c53825290a335b1663637297bf4fa2c` ([Actions 41625241906](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41625241906)). `InverseGreedy/ContinuousRaceSandwich.lean` proves two exact pointwise set inclusions and the genuine independent real-clock product measure sandwich, including S028 closed real-fraction wrappers; `InverseGreedy/BinnedCollisionBound.lean` proves actual collision probability ≤ δ·min(r,s) for all positive reals. These are genuine stochastic measure statements, not priority proxy identities. New `tests/test_s029.py` checks exact negative, zero and endpoint bin cases and geometric algebra. Complete mathematical justification in `proof/S029_CONTINUOUS_SANDWICH.md`.

**Release gate:** check exact *final* PR SHA (including the added tests and documents) has both push and PR Actions green, then squash merge; no release is claimed yet. Next `sessions/S030.md` targets the remaining formal zero-width winner limit and genuine `P(T_r<T_s)=r/(r+s)` equality, followed by finite permutation chambers and real-clock greedy pushforward. Those results are **not** Lean-verified. Preserve 90 EGU / 8 non-EGU / 45 unresolved connected n≤6 census and separate independent novelty review.

---

**S028 FINAL RELEASE (2026-11-03):** [PR #27](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/27) exact final head `d44c27f5905eda93776d0c9f55d89535c5e97d67` passed **both imported Lean and full Python/exact/certified connected graph census** in [push Actions 41618104816](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41618104816) and [PR Actions 41618112258](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41618112258). **Squash-merged into `main`** at `17bcd1f707c25366d30ab7e73c535a72c605f124`. Actual two-clock same-ceiling-bin collision and strict-earlier-bin winner probabilities, their closed ENNReal geometric expressions and exact real-fraction wrappers, are **Lean-verified** for all positive real r,s,δ. Continuous real-clock ratio `Pr(T_r<T_s)=r/(r+s)`, collision-to-zero limit, general finite sorting chambers and real-clock greedy pushforward remain **Lean-open**. `sessions/S029.md` installed. Atlas n≤6 **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty unverified.

**S028 VERIFIED CODE MILESTONES (2026-11-03):** [PR #27](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/27) proves actual independent exponential pair **same-ceiling-bin collision** and **strict-earlier-bin winner** probabilities by deriving true countable geometric sums from S027, then transporting the ENNReal results to the exact `ENNReal.ofReal` real-fraction expressions. All imported Lean and complete Python/exact/certified connected-n≤6 graph census **passed** on code SHA `dc02f4b738a684a11dd86f9ac20726b93037a2b4` (push [Actions 41617713182](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41617713182)); S028 final PR/documentation-head dual-green verification remains to be confirmed. New `tests/test_s028.py` checks rational cylinder tails, three-category partition and symbolic small-width first-order limits independently; see `proof/S028_BINNED_GEOMETRIC.md`. **Not Lean-verified:** the real strict-clock winner ratio `r/(r+s)`, collision-to-zero error bound and limit, general finite chamber masses, and real-clock sorted-order/greedy-output pushforward. `sessions/S029.md` is installed. Connected n≤6: **90 EGU / 8 non-EGU / 45 unresolved**; no independently certified novelty.

**S028 handover:** Working branch `s028-binned-geometric-evaluation`, [PR #27](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/27). First true same-bin geometric result dual-green at `38c781c`; strict-bin theorem dual-green at `302bcc30`; complete **real fractions** dual-green at `dc02f4b` (push Actions 41617713182). Module `InverseGreedy/BinnedRaceGeometric.lean` imported from `InverseGreedy.lean`; new independent exact tests `tests/test_s028.py`, proof `proof/S028_BINNED_GEOMETRIC.md`, next execution prompt `sessions/S029.md`. The exact-final-docs-head check and merge remain the release gate. S029 focuses on the true unequal-rate real-clock comparison, then all finite clock-sorting chambers and measured greedy-output pushforward; none of these are claimed proved in Lean. Do not change S006/S007 census snapshots, or confuse actual clock measure with discrete race law.

**S027 FINAL RELEASE (2026-11-03):** [PR #26](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/26) exact final head `3ccaf4c60991bbe1584b093b3251de9c80747f06` passed **both imported Lean and full Python/exact/certified graph census** in [push Actions 41612710364](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41612710364) and [PR Actions 41612719952](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41612719952). **Squash-merged to `main`** as `ae4ee22030efaae32ee173c7168abccd4fc473dc`. Lean proves genuine first-bin cylinder probabilities and true strict-bin winner / same-bin collision **countable-series identities**; it does **not** yet evaluate their closed forms, establish the unequal-rate continuous winner ratio, or prove general finite sorting/output pushforward. S028 is installed. Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty not certified.

**S027 VERIFIED MILESTONE (2026-11-03):** [PR #26](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/26) adds imported genuine exponential first-bin survival cylinders, exact measure of each cylinder and its inclusion in the real winner event; countable disjoint decomposition and infinite-series *identities* for true strict-bin winner and same-bin collision under `independentExpPair`; and 3 independent `Fraction` regression groups. Both imported Lean and full Python/exact/certified census passed at code SHA `9b4ca4ea833233ffca4a2d892dabedc0f64aa27b` in [push Actions 41612217839](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41612217839). **The closed geometric sum evaluations, collision bound/limit, continuous unequal-rate ratio `Pr(T_r<T_s)=r/(r+s)`, full finite sorting-chamber masses and real-clock greedy pushforward are NOT Lean-verified.** `sessions/S028.md` is installed to pursue those obligations. Exact final PR head needs fresh push+PR dual-green verification before merge. Connected n≤6 atlas stays **90 EGU / 8 non-EGU / 45 unresolved**; novelty not certified.

**S026 FINAL RELEASE (2026-11-03):** [PR #25](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/25), exact final head `b65e54b36da5240ab44649246b600e56a22339da`, passed **both imported Lean and full Python/exact/certified graph census** in [push Actions 41608546306](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41608546306) and [PR Actions 41608555380](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41608555380). **Squash-merged to `main`** as `72e606464d1638dded0ab898bf280b0f6b112bc5`. This release verifies genuine measurable ceiling-bin PMFs, finite-bin `iIndepFun`, and true pair product-box masses; it does **not** prove the unequal-rate continuous race ratio, full sorting chambers or real-clock greedy pushforward. `sessions/S027.md` installed. Connected n≤6 atlas **90/8/45**; independent novelty unverified.

---

# S026 execution handover — 2026-11-03

**PR:** https://github.com/jfairfaxball-348/Inverse-Greedy/pull/25
**Branch:** `s026-genuine-ceiling-bins`, based on `main` at `ae9409cd4586f515665bb0f42594f8c71f44e1c3`.

S026 upgrades the *actual* exponential real-cell mass of S025 to the probability of a genuine measurable one-based ceiling bin random variable. The zero bin is null and every bin `k+1` has mass `(1-q)q^k` with `q=exp(-rate δ)` for arbitrary positive reals. This first milestone passed both imported Lean and full Python/census in [PR Actions 41607274017](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41607274017), code SHA `67c9b4a0a46cfac6e26cd436bdc115a60bce09c4`.

Subsequent module edits extend to measurable `iIndepFun` of every finite family of bins and an exact two-coordinate bin-box mass derived from the actual independent exponential product, not from the stipulated discrete priority model. Those extensions are **Lean-verified** at code SHA `48ea3c284632e2db7a2df438d45a5e263c81aa35`: both imported Lean and full Python/certified census passed in push Actions 41607939473 and PR Actions 41607949333. Recheck exact final PR head before merge. The `Fraction` test addition has four exact endpoint / box / collision / truncation groups; no historical census flags were changed.

**Still open in Lean:** numerical unequal-rate two-clock event `Pr(T_r<T_s)=r/(r+s)`, strict-bin winner and collision sums at the measure level, an analytic collision bound/limit, all finite sorting chamber probabilities and the genuine continuous greedy-output pushforward. The S023 mathematical proof and `Fraction` algebra must not be misrepresented as these Lean results. Atlas 90/8/45, no independent novelty claim. Next handoff: `sessions/S027.md`.

---

**S025 FINAL RELEASE (2026-11-03):** [PR #24](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/24) exact final head `1c8a32fb548242cebffe1ebde7e8386ee0bd79c1` passed BOTH imported Lean and full Python/exact/certified graph census in [push Actions 41598540982](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598540982) and [PR Actions 41598576216](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598576216). It was **squash-merged to `main`** as `e10fd67c08e80ea63c8d02b9308b54080fce8fd5`. `sessions/S026.md` is installed. The new genuine interval and finite-coordinate geometric-cell laws are Lean-verified; floor-valued bin independence, unequal-rate race ratio, all-chamber masses and real-clock greedy pushforward remain Lean-open. Atlas still **90/8/45**; no novelty certification.

---

# S025 execution handover — 2026-11-03

**Branch:** `s025-real-bin-cells` from `main` 500d7281f9ec.
The first new theorem block in `InverseGreedy/ExpBinCells.lean` is imported and **Lean-verified** at exact SHA `9336b4458a4ba0abf9c52e45c8cf0399837f8edd`: both imported Lean and all Python/exact/certified-census passed in [Actions 41598092129](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598092129). Before this success, earlier drafts had two Lean proof-script failures: incorrect `measure_sdiff` arguments and `ENNReal.ofReal_sub` orientation; both are repaired.

**Mathematical advancement (IG-L38):** From the *genuine* exponential survival measure in S024, prove the actual `Ioc a b` probability `exp(-ra)-exp(-rb)` for `r>0`, `0≤a≤b`. Deduce exact geometric real-bin mass `(1-e^{-rδ})e^{-rkδ}` for all positive real `r,δ` and `k : ℕ`; the proof uses exponential addition, induction and endpoint-measurable sets, not the S018 discrete priority law. S025 also adds the finite-coordinate geometric cylinder theorem (IG-L39), with BOTH imported Lean and complete Python/certified census green on exact code SHA `d081ccd117000efdf1c3a67f2767e792f67587c4`, [Actions 41598167342](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598167342).

**Exact tests:** `tests/test_s025.py` includes five `Fraction` consistency groups for real exponential-survival bin algebra, finite box products, and independent two-clock finite sums. `proof/S025_REAL_CLOCK_CELLS.md` sets out the rigorous distinction between a real-cell probability and an actual floor-valued bin map.

**Not completed in Lean:** floor/bin PMF, independence of binned clocks, `Pr(T_r<T_s)=r/(r+s)`, all strict sorting-chamber masses and continuous sorted greedy-output pushforward. `sessions/S026.md` installs these targets. Partial atlas remains **90 EGU / 8 non-EGU / 45 unresolved**; no independent novelty certificate.

**Release:** completed as recorded in the S025 final-release entry above.

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
