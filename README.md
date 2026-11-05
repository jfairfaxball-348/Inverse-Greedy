**S041 GRAPH THEOREMS IN LEAN (2026-11-05; PR #41; GitHub-verified):** Code head `adb420f3b93ccd2c98ef73127ebbf318d7548d0d` passed full imported Lean and Python/exact/certified n≤6 census in both [push 42065650195](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/42065650195) and [PR 42065663973](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/42065663973) ([PR #41](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/41)); earlier heads cd4021c and ed12c1d also dual-green. The project's proved graph theorems are now Lean theorems about **genuine exponential clocks** (`RealClockEGU`/`RealClockAEGU`) for all strictly positive real rates: union and join EGU iff (IG-P2, IG-P4), every cograph and complete multipartite graph EGU (IG-P1, IG-P4), relabelling invariance, false-twin invariance (IG-P7), every clique corona EGU (IG-P8), P5/C6/P6/cone(P5) not EGU (IG-N1–N4), **every** pendant star corona K_{1,m}∘K1 with m≥2 not EGU (IG-N5), and all **90 certified positives and 8 certified negatives** of the connected n≤6 atlas (`atlas_n_le_6_certified`, including P4 with √3 rates and atlas index 1). Approximate layer: C6 TV ≥ 4/45 and not AEGU, P5 and corona(P3) unattained AEGU with exact families, P6 TV ≥ 2√(2/5)−6/5, disjoint-union and join AEGU iff (IG-P9, IG-P10). Certificates use kernel `decide +kernel` (no native code), `field_simp; ring`, `positivity`, `linear_combination`. Modules: RaceTerms, RationalWitness, SmallGraphObstructions, GraphOperationsLaw/EGU, CographEGU, FalseTwins, GeneralFamilies, Atlas/Part00–16 + AtlasCertificates, ApproximateEGU, ApproximateJoin, EdgeSetGraphs, SmallGraphClassification; generators `experiments/gen_*.py`; tests `tests/test_s041_graphs.py`; note `proof/S041_GRAPH_THEOREMS_LEAN.md`. **IG-P5 exhaustive:** every graph on ≤5 vertices is EGU unless isomorphic to P5 (`graphs_le_five_classification`, kernel-checked certificate tables over all 2^10 labelled graphs). **Not formalised:** IG-N6 for m≥3, exhaustiveness of the connected n=6 enumeration (so the 45-unresolved count rests on NetworkX), the 45 open graphs and the classification (open problems), novelty (not a theorem). Atlas **90 / 8 / 45**.

**S041 REAL-CLOCK GREEDY LAW (2026-11-05; branch `ccr-64572a8e-98j7ug`, built on S040 PR #40; exact-head push+PR CI must be checked before calling it GitHub-verified):** Three new imported modules complete the stochastic foundation chain from Mathlib's *actual* independent exponential product measure to the greedy output law, for arbitrary finite vertex types and strictly positive real rates. `FiniteClockGapClosedForm.lean`: the measured strict-bin chamber equals the exact finite-width product `ofReal(∏_j (1-q_j) q_j^j/(1-Q_j))` (S038 monomial transport, S040 factorisation, finite-index ENNReal Tonelli, S039 geometric factors; n=0/1 included). `FiniteClockOrderLaw.lean`: **for every complete order, the real-clock strict chamber has probability `ofReal(orderMass rates order)`** (δ→0⁺ limit squeezed by S033/S034). `RealClockGreedyLaw.lean`: a measurable stable clock sort, `realClockGreedyOutput`, its law **equals `priorityOutputMass` and (symmetric neighbours) `finiteRaceLaw`**, and `realClockEGU_iff_firstChoiceEGU` shows the charter's genuine-clock EGU definition is equivalent to the first-choice-recursion definition. `RealClockGreedyMIS.lean`: for symmetric irreflexive neighbours every greedy output is a **maximal independent set**, so the real-clock output law is a probability distribution on the MIS family. First code head `4da0188` dual-green ([push 42039828348](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/42039828348), [PR 42039904870](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/42039904870), [PR #41](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/41)). Local full `lake build` green; headline theorems use only `propext`, `Classical.choice`, `Quot.sound`. Independent exact regression `tests/test_s041.py`; proof note `proof/S041_REAL_CLOCK_GREEDY_LAW.md`; next `sessions/S042.md`. **Not claimed:** Lean re-proofs of graph-specific obstructions in the real-clock language, any classification, novelty or Palomar status. Atlas **90 EGU / 8 non-EGU / 45 unresolved**.

**S040 WORK IN PROGRESS (2026-11-04; [PR #40](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/40)):** New imported `FiniteClockGapMonomial.lean` proposes a generic **ENNReal finite triangular monomial factorisation** for arbitrary factors and gaps, including n=0/1 and zero/infinite inputs. Exact `Fraction` regression in `tests/test_s040.py`, scope note `proof/S040_FINITE_GAP_MONOMIAL.md`, next `sessions/S041.md`. Verify complete imported Lean and Python/exact/certified connected n≤6 census on exact final push and PR head before treating this as verified or merging. **NOT YET PROVED:** that this positional monomial is S038's actual measured vertex-indexed monomial, the multivariate `ENNReal tsum` and finite-width measured closed product, δ↓0+ n≥3 chamber law, measurable sorting, or continuous greedy-output pushforward. Atlas **90 EGU / 8 non-EGU / 45 unresolved**; no novelty/registration claim.

**S039 FINAL VERIFIED PARTIAL RELEASE (2026-11-04):** Exact final PR head `516df6d5743aa637f4b244caf8f798b4c37b6c9a` passed the **complete imported Lean build** and **full Python/exact/certified connected n≤6 census** in both [push Actions 41902458188](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41902458188) and [PR Actions 41902473442](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41902473442). [PR #39](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/39) squash-merged into `main` as `3a0b60ada77e4feab90ec10852398924fec9b904`. New imported `InverseGreedy/FiniteClockGapFactors.lean` proves (i) genuine Exp-clock bin ratios `q_i = exp(-rates_i δ)` lie strictly in `(0,1)` for positive rates and width; (ii) every indexed nonempty suffix product `Q_a` lies in `(0,1)`, with strictly positive `1-Q_a`; and (iii) the **individual** geometric `ENNReal` series `Σ'_k (ofReal Q_a)^k = ofReal (1/(1-Q_a))`. A zero-length order has no suffix index, and singleton orders are covered. Independent `tests/test_s039.py` uses exact `Fraction` arithmetic to check all complete orders through four coordinates, finite gap-monomial factorisation and truncated multiple-geometric products. Proof note `proof/S039_SUFFIX_GEOMETRY.md`; next `sessions/S040.md`. **Not yet formally proved:** the multivariate ENNReal monomial factorisation and countable gap-tsum evaluation from S038's *actual measured probability*, its finite-width closed product, the δ→0+ n≥3 real-clock strict-order law, total measurable sorting, or the real-clock greedy-output pushforward. Preserve connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; no novelty/Palomar claim.

**S038 FINAL VERIFIED PARTIAL RELEASE (2026-11-04):** Exact final PR head `212f0d8a6e7aed1337f3fe6726cd88480f45d384` passed **both full imported Lean and complete Python/exact/certified connected n≤6 census** in **both** push [Actions 41896636575](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41896636575) and PR [Actions 41896648063](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41896648063); [PR #38](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/38) squash-merged into `main` as `f67768d261884cc87a729fbafa3d0632b1f34312`. This release includes imported `FiniteClockCompleteOrder.lean` and `FiniteClockMeasuredGapSeries.lean`. The complete-order witness explicitly certifies coverage and no repeated list indices, transports S035 valid bins to S037 nonnegative gaps, and reindexes the **genuine measured Exp-clock `tsum`** via a subtype sum and an equivalence (not an assumed PL law). Exact rational `tests/test_s038.py`, `proof/S038_MEASURED_GAP_REINDEX.md`, next `sessions/S039.md`. **Both new Lean modules are now verified on the exact final dual-green head**. Still open: measured multi-geometric evaluation, `δ↓0+`, general real-clock chamber theorem, total measurable sorting and actual continuous greedy-output pushforward. Connected n≤6 **90 EGU / 8 non-EGU / 45 unresolved**; no novelty/registration assertion.

**S037 FINAL VERIFIED PARTIAL RELEASE (2026-11-04):** Exact final PR head `8043465835fed9b1245b98f1e1e59bfe743dae8b` passed the complete imported Lean build and full Python/exact/certified connected n≤6 census in **both** push [Actions 41875794221](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41875794221) and PR [Actions 41875873962](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41875873962); [PR #37](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/37) squash-merged to `main` as `93c20facf8d3e396374aa066e6b46b266312431f`.  `InverseGreedy/FiniteClockGapInverse.lean` defines consecutive differences of ordered bins, proves both finite-vector inverse identities, packages the equivalence `finiteGapBinEquiv n` for every `n` including zero and singleton, and proves injectivity of the full gap-to-bin vector map. `tests/test_s037.py` checks complete enumerations, arbitrary reorderings, truncated exact geometric sums, positivity/bounds, and rejects repeated/incomplete lists. This *does not* reindex S035's genuine measured sum from arbitrary complete vertex lists or evaluate its multiple geometric product. Measured zero-width n≥3 chamber identity and genuine greedy-output pushforward remain Lean-open. See `proof/S037_GAP_INVERSE.md` and `sessions/S038.md`. Atlas **90 EGU / 8 non-EGU / 45 unresolved**; no independent novelty or registration claim.

**S036 FINAL VERIFIED PARTIAL RELEASE (2026-11-04):** Exact final PR head `badc40d639370827930a5a93681ae9c56daf43ff` passed **both imported Lean and complete Python/exact/certified connected n≤6 census** in push [Actions 41858484562](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41858484562) and PR [Actions 41858495527](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41858495527); [PR #36](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/36) squash-merged into `main` as `9161943595035a17a07a66ee1b3c6251e945f540`. Imported `InverseGreedy/FiniteClockGapEncoding.lean` proves forward gap-vector strict monotonicity, position injectivity, lower bounds and the adjacent successor recurrence `k_(j+1)=k_j+1+d_(j+1)`. Independent `tests/test_s036.py` checks the two-sided gap bijection and exact rational monomial factorisation (not formal Lean inverse). Proof scope: `proof/S036_GAP_ENCODING.md`; next `sessions/S037.md`. **Still Lean-open:** inverse gap bijection and reindexing the S035 genuine measured series, n≥3 real-clock chamber law, total measurable sort and continuous-clock greedy-output pushforward. Connected n≤6 census **90 EGU / 8 non-EGU / 45 unresolved**; novelty unverified.

**S035 FINAL VERIFIED PARTIAL RELEASE (2026-11-04):** Exact final PR head `2edf01c7da105403ac75c8959fce292a34da34ce` passed **complete imported Lean** and **full Python/exact/certified connected n≤6 census** in both [push Actions 41823819781](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41823819781) and [PR Actions 41823826234](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41823826234); [PR #35](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/35) was squash-merged to `main` as `4aa7459c5bd1a66a612134d106c467ff3d2d7000`. Imported `InverseGreedy/FiniteClockBinSeries.lean` proves true-clock strict-bin chamber probability is a countable sum over disjoint measurable positive-bin geometric cylinders using S032 joint mass and S033 zero-bin nullity. Independent rational `tests/test_s035.py`, `proof/S035_BIN_SERIES.md` and `sessions/S036.md` included. **Full multi-geometric closed product, n≥3 real-clock zero-width chamber theorem, measurable sorting and continuous greedy pushforward remain Lean-open.** Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; no novelty certificate.

**S034 FINAL VERIFIED PARTIAL RELEASE (2026-11-04):** Exact final PR head `32c28558efe9d685d2ac7123bd2ba2887890c898` passed the **complete imported Lean** build and **full Python/exact/certified connected n≤6 census** in both [push Actions 41807976461](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41807976461) and [PR Actions 41807983429](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41807983429); [PR #34](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/34) was squash-merged into `main` as `e7947eb1382e8838485e7b761615f2bb8cf4442e`. Imported `FiniteClockBinUnion.lean` proves the genuine finite exponential same-ceiling-bin collision union estimate for a list of distinct indices and adds its explicit finite pair-rate error to the real/bin chamber sandwich; empty/singleton cases are included. `tests/test_s034.py` adds exact regressions, `proof/S034_FINITE_UNION.md` records the proof and scope, and `sessions/S035.md` is installed. The general n≥3 continuous chamber formula, multi-geometric evaluation, and measurable sorting/greedy-output pushforward remain Lean-open. Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; novelty not independently established.

**S033 FINAL VERIFIED PARTIAL RELEASE (2026-11-03):** exact final PR head `6b57057e6711b4d17d183a277305a0e08376eba9` passed imported Lean and full Python/exact/certified connected-n≤6 atlas in BOTH [push Actions 41692437332](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41692437332) and [PR Actions 41692441926](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41692441926); [PR #32](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/32) squash-merged as `025cf356d0afa8fcefeb12191103b51703fe4d6a`. Imported Lean `FiniteClockBinChambers.lean` establishes the **actual** finite real-clock / strict-ceiling-bin chamber event sandwich; `FiniteClockPairBinCollision.lean` transports S029's `P(Kδ(T_i)=Kδ(T_j)) ≤ δ·min(r_i,r_j)` to distinct coordinates within an **arbitrary** genuine finite exponential family. `tests/test_s033.py` supplies independent deterministic/exact checks and `proof/S033_BIN_CHAMBER.md` explains the scope. These are **partial** S033 obligations: the complete finite bin-collision union bound, general n≥3 strict-bin multiple-geometric summation, continuous-chamber product, and actual sorting/pushforward law are still Lean-open. `sessions/S034.md` installed. Connected n≤6 atlas remains **90 EGU / 8 non-EGU / 45 unresolved**; novelty unverified. All listed S033 partial Lean claims are now verified at this exact head; the full n≥3 chamber and greedy pushforward are not.

**S032 FINAL RELEASE (2026-11-03):** [PR #31](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/31) exact final head `dffde518c3727c4c1fcde4789dc2773ee65e6c62` passed **both imported Lean and complete Python/exact/certified connected-n≤6 census** in BOTH [push Actions 41677475236](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41677475236) and [PR Actions 41677479044](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41677479044). Squash-merged to main as `c9659d7b4b0ebcc7d7dd297852ba4ea5bca96602`. This verifies the **genuine full finite-family simultaneous ceiling-bin probability** and true two-item/repeated-index strict chamber facts; NOT the full n≥3 sorting-chamber product or real-clock greedy-output pushforward. An explicit multi-geometric gap-series formula has a separate informal mathematical derivation and exact rational regression, not Lean proof. `sessions/S033.md` installed. Atlas **90 EGU / 8 non-EGU / 45 unresolved**; novelty not independently certified.

**S031 FINAL RELEASE (2026-11-03):** [PR #30](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/30) exact final head `09d0b45ddcae35714c1cf0a03af57d62a900781c` passed **both imported Lean and Python/exact/certified connected-n≤6 census** in BOTH [push Actions 41650444708](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41650444708) and [PR Actions 41650452725](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41650452725). **Squash-merged into main as `06db312e37c7fa9bf05718d7297f43e2cf5405c0`.** Lean now proves genuine finite-family pairwise comparison probabilities and strict-chamber pair upper bounds, plus empty/singleton chamber mass one. The **full n≥3 continuous chamber product** and **true real-clock greedy-output pushforward** remain Lean-open. `sessions/S032.md` installed. Census **90 EGU / 8 non-EGU / 45 unresolved**; novelty not independently certified.

**S031 EXECUTION (2026-11-03; [PR #30](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/30), exact-head CI/merge now certified above):** Imported `InverseGreedy/FiniteClockPairOrder.lean` transports S030's **actual continuous two-clock** exponential race ratio through S022's true finite-coordinate joint law. For **any finite family** of positive-rate independent exponential clocks and distinct i,j, Lean proves `P(T_i<T_j)=ENNReal.ofReal(rate_i/(rate_i+rate_j))`; each genuine finite strict-order chamber is bounded by every required distinct pair comparison. It also proves genuine empty/singleton strict-comparison chamber events have mass one. Independent exact `Fraction` regression `tests/test_s031.py`, rigorous scope note `proof/S031_FINITE_CLOCK_PAIR.md`, and S032 prompt installed. **Not yet proved in Lean:** full 3+-clock chamber probability, measurable canonical sorted-order law, continuous-clock greedy-output pushforward. Preserve n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; no novelty claim. Final S031 verification and merge are certified in the release entry above.

**S030 FINAL RELEASE (2026-11-03):** [PR #29](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/29) exact final head `94cef7edb07d9e45de559d9c6d02cd1a3d60d572` passed **both complete imported Lean and Python/exact/certified connected-n≤6 census** on BOTH [push Actions 41647662604](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647662604) and [PR Actions 41647671351](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647671351); **squash-merged into `main`** at `abadb58e6b4583729d084b66c1e9096041ce1eb4`. Lean now formally proves the **actual independent continuous exponential two-clock inequality-event mass** `P(T_r<T_s)=ENNReal.ofReal (r/(r+s))` for any r,s>0, using the real analytic small-bin limit and S029 true measured-event squeeze. The full finite strict ordering chamber law and continuous-clock greedy-output pushforward remain **Lean-open**; `sessions/S031.md` installed. Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty unverified.

**S030 VERIFIED CODE CHECKPOINT (2026-11-03):** [PR #29](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/29) imports `InverseGreedy/ContinuousRaceLimit.lean`, which now Lean-proves the real exponential initial-slope / positive-width bin-winner analytic limit, the corresponding `ENNReal.ofReal` limit, and **the actual continuous independent exponential pair theorem** `independentExpPair_realWinner_rateRatio`: for every r,s>0, `P(T_r<T_s)=ENNReal.ofReal(r/(r+s))`. The full imported Lean and complete Python/exact/connected n≤6 census are GREEN at exact code SHA `0144a168dd0dfd0ff90d4ea5f089f0bbc55ed319`, in both [push Actions 41647056971](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647056971) and [PR Actions 41647064745](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41647064745). S030 final docs-head dual green and merge pending. S031 is installed for the genuine finite strict permutation chamber formula and continuous-clock greedy-output pushforward, **neither yet proved in Lean**. Atlas remains 90 EGU / 8 non-EGU / 45 unresolved; independent novelty unverified.

**S029 FINAL RELEASE (2026-11-03):** [PR #28](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/28) exact final head `3c2150a8668fd3869318810f9e02eb65289d47e8` passed **both imported Lean and full Python/exact/certified connected-n≤6 graph census**, on BOTH [push Actions 41625700011](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41625700011) and [PR Actions 41625709665](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41625709665). **Squash-merged into `main`** as `bc586f6c679fe1a49db3e3127ab0e8c5f5727ca0`. Lean now verifies the genuine real-clock/bin-event measure sandwich, S028's exact real-fraction wrapper and the true collision bound `P(same ceiling bin) ≤ δ·min(r,s)` for all positive rates/widths. The **analytic zero-width limit**, continuous rate ratio `P(T_r<T_s)=r/(r+s)`, finite sorting-chamber masses and actual real-clock greedy-output pushforward remain **Lean-open**. `sessions/S030.md` installed. Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty unverified.

**S029 VERIFIED CODE CHECKPOINT (2026-11-03):** [PR #28](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/28) adds genuine continuous-clock/ceiling-bin event inclusions, the **true exponential measure sandwich**, exact S028-fraction bounds and the quantified true-measure collision bound **P(same bin) ≤ δ·min(r,s)** for arbitrary positive real r,s,δ. The two imported Lean modules and full Python/exact/certified n≤6 graph census passed at code SHA `06bd1baa4c53825290a335b1663637297bf4fa2c` in [Actions 41625241906](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41625241906). New `tests/test_s029.py` checks exact bin-order boundary cases and collision algebra. Final PR/docs-head CI/merge is pending. **Not yet Lean-proved:** the δ→0 analytic rate-ratio limit, `Pr(T_r<T_s)=r/(r+s)`, full finite chamber masses, or continuous greedy-law pushforward. `sessions/S030.md` installed. Atlas **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty unverified.

**S028 FINAL RELEASE (2026-11-03):** [PR #27](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/27) exact final head `d44c27f5905eda93776d0c9f55d89535c5e97d67` passed **both imported Lean and full Python/exact/certified connected graph census** in [push Actions 41618104816](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41618104816) and [PR Actions 41618112258](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41618112258). **Squash-merged into `main`** at `17bcd1f707c25366d30ab7e73c535a72c605f124`. Actual two-clock same-ceiling-bin collision and strict-earlier-bin winner probabilities, their closed ENNReal geometric expressions and exact real-fraction wrappers, are **Lean-verified** for all positive real r,s,δ. Continuous real-clock ratio `Pr(T_r<T_s)=r/(r+s)`, collision-to-zero limit, general finite sorting chambers and real-clock greedy pushforward remain **Lean-open**. `sessions/S029.md` installed. Atlas n≤6 **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty unverified.

**S028 VERIFIED CODE MILESTONES (2026-11-03):** [PR #27](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/27) proves actual independent exponential pair **same-ceiling-bin collision** and **strict-earlier-bin winner** probabilities by deriving true countable geometric sums from S027, then transporting the ENNReal results to the exact `ENNReal.ofReal` real-fraction expressions. All imported Lean and complete Python/exact/certified connected-n≤6 graph census **passed** on code SHA `dc02f4b738a684a11dd86f9ac20726b93037a2b4` (push [Actions 41617713182](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41617713182)); S028 final PR/documentation-head dual-green verification remains to be confirmed. New `tests/test_s028.py` checks rational cylinder tails, three-category partition and symbolic small-width first-order limits independently; see `proof/S028_BINNED_GEOMETRIC.md`. **Not Lean-verified:** the real strict-clock winner ratio `r/(r+s)`, collision-to-zero error bound and limit, general finite chamber masses, and real-clock sorted-order/greedy-output pushforward. `sessions/S029.md` is installed. Connected n≤6: **90 EGU / 8 non-EGU / 45 unresolved**; no independently certified novelty.

## S028 — genuine binned race closed probabilities

Two new imported Lean theorems in `InverseGreedy/BinnedRaceGeometric.lean` evaluate the **actual** independent exponential measure of (1) same-positive-ceiling-bin collisions and (2) strictly earlier-ceiling-bin wins for arbitrary positive real r,s,δ. The zero bins are null and S027's event partition is the starting point; these are not postulated geometric priority variables. Both formulas have precise `ENNReal.ofReal` real-fraction wrappers. Imported Lean + complete Python/certified census passed at SHA `dc02f4b` in Actions 41617713182. Exact final docs-head CI/merge still must be verified. S029 next targets the continuous real-clock winner ratio and sorted-clock greedy pushforward; these **are not yet Lean-verified**. Partial connected n≤6 atlas remains 90/8/45.

**S027 FINAL RELEASE (2026-11-03):** [PR #26](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/26) exact final head `3ccaf4c60991bbe1584b093b3251de9c80747f06` passed **both imported Lean and full Python/exact/certified graph census** in [push Actions 41612710364](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41612710364) and [PR Actions 41612719952](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41612719952). **Squash-merged to `main`** as `ae4ee22030efaae32ee173c7168abccd4fc473dc`. Lean proves genuine first-bin cylinder probabilities and true strict-bin winner / same-bin collision **countable-series identities**; it does **not** yet evaluate their closed forms, establish the unequal-rate continuous winner ratio, or prove general finite sorting/output pushforward. S028 is installed. Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**; independent novelty not certified.

**S027 VERIFIED MILESTONE (2026-11-03):** [PR #26](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/26) adds imported genuine exponential first-bin survival cylinders, exact measure of each cylinder and its inclusion in the real winner event; countable disjoint decomposition and infinite-series *identities* for true strict-bin winner and same-bin collision under `independentExpPair`; and 3 independent `Fraction` regression groups. Both imported Lean and full Python/exact/certified census passed at code SHA `9b4ca4ea833233ffca4a2d892dabedc0f64aa27b` in [push Actions 41612217839](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41612217839). **The closed geometric sum evaluations, collision bound/limit, continuous unequal-rate ratio `Pr(T_r<T_s)=r/(r+s)`, full finite sorting-chamber masses and real-clock greedy pushforward are NOT Lean-verified.** `sessions/S028.md` is installed to pursue those obligations. Exact final PR head needs fresh push+PR dual-green verification before merge. Connected n≤6 atlas stays **90 EGU / 8 non-EGU / 45 unresolved**; novelty not certified.

# Inverse Greedy

**S026 FINAL RELEASE (2026-11-03):** [PR #25](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/25), exact final head `b65e54b36da5240ab44649246b600e56a22339da`, passed **both imported Lean and full Python/exact/certified graph census** in [push Actions 41608546306](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41608546306) and [PR Actions 41608555380](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41608555380). **Squash-merged to `main`** as `72e606464d1638dded0ab898bf280b0f6b112bc5`. This release verifies genuine measurable ceiling-bin PMFs, finite-bin `iIndepFun`, and true pair product-box masses; it does **not** prove the unequal-rate continuous race ratio, full sorting chambers or real-clock greedy pushforward. `sessions/S027.md` installed. Connected n≤6 atlas **90/8/45**; independent novelty unverified.


## S026 — Genuine measurable ceiling-bin clocks (2026-11-03)

The newly imported `InverseGreedy/ClockBins.lean` defines the **real-to-natural measurable** map `clockCeilBin δ t = Nat.ceil (t/δ)`. For every real `δ>0`, its positive cell `Kδ=k+1` is **exactly** `(kδ,(k+1)δ]`, even at boundaries; `Kδ=0` iff `t≤0` and has genuine Exp(rate) probability zero. S025's actual exponential measure thus gives the positive-cell geometric PMF for **all** positive real rates, including k=0. The finite-coordinate marginal, complete finite-index bin-family independence under actual `finiteIndependentExp`, two-clock product-bin PMF and distinct-coordinate finite-product pair PMF are imported **Lean-verified** theorems at code SHA `48ea3c284632` (both imported Lean and full Python/certified census passed in push Actions 41607939473 and PR Actions 41607949333). The exact final PR head is rechecked before merge.

The independent `tests/test_s026.py` checks rational endpoint conventions (including negative inputs), exact geometric box products, two-clock bin-winner/collision algebra and geometric tails with `Fraction`. The unequal-rate **continuous** probability `Pr(T_r<T_s)=r/(r+s)` remains **Lean-open**, as do full chamber masses and the actual greedy-law pushforward. The 90/8/45 atlas and novelty boundary are unchanged. See `proof/S026_MEASURABLE_BINS.md`, `sessions/S027.md`, PR #25.


## S025: real exponential bin-cell probability

**S025 FINAL RELEASE (2026-11-03):** [PR #24](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/24) exact final head `1c8a32fb548242cebffe1ebde7e8386ee0bd79c1` passed BOTH imported Lean and full Python/exact/certified graph census in [push Actions 41598540982](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598540982) and [PR Actions 41598576216](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598576216). It was **squash-merged to `main`** as `e10fd67c08e80ea63c8d02b9308b54080fce8fd5`. `sessions/S026.md` is installed. The new genuine interval and finite-coordinate geometric-cell laws are Lean-verified; floor-valued bin independence, unequal-rate race ratio, all-chamber masses and real-clock greedy pushforward remain Lean-open. Atlas still **90/8/45**; no novelty certification.

`InverseGreedy/ExpBinCells.lean` proves directly from Mathlib's
**genuine** exponential survival law that for every real `r>0`,
`δ>0`, and natural `k`,

```
P(kδ < T ≤ (k+1)δ) = (1-exp(-rδ)) exp(-rδ)^k.
```

The underlying actual real-interval mass theorem, not a stipulated
geometric distribution, passed imported Lean and complete Python/certified
census at SHA `9336b4458a4b` in
[Actions 41598092129](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598092129).
The finite-clock coordinate cylinder extension was also formally verified at SHA `d081ccd11700`, with BOTH imported Lean and complete Python/census green in [Actions 41598167342](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41598167342). Five new exact
`Fraction` regressions check bin partition and two-clock finite-sum
algebra. Full mathematical argument:
`proof/S025_REAL_CLOCK_CELLS.md`.

**Scope:** neither a measurable `floor(T/δ)` map, nor independence
of those binned variables, nor the actual unequal-rate race probability
`P(T_r<T_s)=r/(r+s)` has yet been Lean-proved. All finite
strict-order chamber masses and continuous greedy-output pushforward
remain formally open. `sessions/S026.md` continues the bridge.
Partial connected six-vertex atlas unchanged: **90 EGU / 8 non-EGU /
45 unresolved**. Independent novelty not certified.


**Exact Uniformity and Controllability of Random Greedy Independent Sets**

Author: John Fairfax-Ball. Programme started 2026-10-30.

## Research question
For a finite simple graph G assign independent Exp(λ_v) arrival clocks
to vertices, with **strictly positive rates**. Greedily accept each
vertex when none of its already accepted neighbours exists. The output
is a maximal independent set (MIS). Which graphs permit rates making
the output exactly **uniform over all MIS**? Such graphs are called EGU.

## S024: actual continuous exponential survival, finite support

`InverseGreedy/ExpSurvival.lean` derives genuine Mathlib
`expMeasure` CDF and survival formulas for arbitrary positive real
rates, using `cdf_expMeasure_eq`, `ofReal_cdf` and the complement
identity, not an assumed weighted priority law. It also proves that
each coordinate of a genuine finite exponential product has this
same tail and that **all** coordinates are nonnegative almost surely,
including empty and singleton families. The imported Lean build and
complete Python/certified census passed at code SHA `8f52f3a8a1b9`,
[Actions 41595641100](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41595641100).
**Final S024 release:** exact PR #23 head `3dc4332ea304b15dcbc5b005f48eb5a7c4972837` passed **both** imported Lean and complete Python/certified census in [push Actions 41596092382](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41596092382) and [PR Actions 41596101126](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41596101126); squash-merged to `main` as `be7859cce0dba3613acae9fb47b1f0017206396c`. See `HANDOVER.md` for release provenance.

`proof/S024_EXP_SURVIVAL.md` explains the true measure proof.
`tests/test_s024.py` adds four exact `Fraction` consistency checks
for rational exponential-bin boundaries. These are algebraic tests,
**not** measure-level proofs of bin laws. The numerical
`Pr(T_r<T_s)=r/(r+s)`, complete strict-chamber probabilities
and the real clock-to-greedy pushforward remain **Lean-open**.
S025 is installed. Graph atlas stays **90 EGU / 8 non-EGU /
45 unresolved**; no novelty certificate.

## S023: geometric-bin continuous sorting bridge

InverseGreedy/FiniteClockChambers.lean defines genuine real-clock strict-order events and proves their measurability. Imported Lean plus complete Python/census were BOTH green at exact code SHA 6faf5ba21bf585a52412f8e2269e376a03b2de45 in [Actions 41536043877](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41536043877). This is event measurability, **not** a computation of chamber probability.

proof/S023_GEOMETRIC_BIN_CHAMBERS.md supplies a complete alternative **informal** proof of all-real finite exponential sorting-chamber probabilities via geometric-bin products and a collision error bound delta times the sum of min(rate_i,rate_j) over pairs. tests/test_s023.py checks two independently derived exact rational bin formulas for integer rates and rigorous collision enclosures. The numerical unequal-rate probability and real-clock greedy pushforward remain **Lean-open**. S024 is installed. The atlas is still **90 / 8 / 45**.

**S023 FINAL RELEASE:** [PR #22](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/22) exact final branch head bfb0d2cd6d03ca874b026527b0e19c06cc471442 passed BOTH full imported Lean and Python/certified census in [push run 41536696192](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41536696192) and [PR run 41536741787](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41536741787). Squash-merged to main as 83a4390f69ac04621fa64498d41be93f74fc4c33. Only chamber measurability is Lean-verified, not continuous chamber mass or sorting pushforward. S024 installed. Atlas unchanged 90/8/45.

## S022: real finite-clock pair marginals and almost-sure no ties

`InverseGreedy/FiniteClockNoTies.lean` closes a genuine continuous-clock
measure-theory gap. From S020's independent exponential coordinate family,
it derives the exact two-coordinate product law for distinct indices.
Pulling back S019's zero-measure diagonal proves that any two distinct
real exponential clocks almost surely never tie, then a finite union
gives probability **one** of pairwise distinct arrival times for **any
finite index type**, including the empty and singleton cases.

This does **not** establish the numerical unequal-rate probability
`P(T_r<T_s)=r/(r+s)`, the probabilities of all finite sorting
chambers or a continuous-clock-to-greedy-output pushforward.
The independent `tests/test_s022.py` regression uses exact rational
binned versions of genuine exponential arrivals; mathematical details
are in `proof/S022_FINITE_NO_TIES.md`.
**Verification:** Imported Lean and full Python/certified census passed on the **exact final PR #21 head** `c9df8f4aab9303b89eafb8072c3597909536ebc1`, [Actions 41475826383](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41475826383). Squash-merged into `main` as `71a84f55197fc79170bf98fc177ce33d6a86e58d`.
S023 targets the remaining numerical race law and sorting bridge.
Connected n≤6 atlas remains **90 / 8 / 45**.

## S021: unequal-rate product-law swap and finite comparison events

`InverseGreedy/ContinuousRaceSwap.lean` proves **genuine continuous
product-law rate swapping** at arbitrary strictly positive exponential
rates and the reverse-winner event identity. It also makes finite
coordinate comparisons and clock-tie events measurable, and formalises
the all-distinct/first-winner event predicates. All listed formal statements passed imported Lean and complete
Python/certified census at **exact final PR #20 head**
`ef41930888d2aca53f538777bbfd30604d81e358`,
[Actions 41445751233](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41445751233).
[PR #20](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/20)
was squash-merged as `e02afe3769d5f6ff2a787a21dbb8cc13330243fa`.
An earlier imported-code checkpoint also passed at `d105af449e`.

`tests/test_s021.py` independently counts all orderings of labelled
unit-rate exponential replicas (up to eight replicas), exactly checking
the ordered-chamber formula for integer rates, including 1:7 and empty/
singleton boundary cases. Its independent continuous-clock interpretation
is proved in `proof/S021_CONTINUOUS_RACE_SYMMETRY.md`.

**Still open in Lean:** unequal-rate numerical identity
`P(T_r<T_s)=r/(r+s)`, a.s. no ties of distinct coordinates in
finite products, genuine continuous sorted-chamber probabilities, and
clock-to-greedy pushforward. `sessions/S022.md` is installed as their
continuation. The graph atlas is unchanged at **90/8/45**.

## S020: true continuous two-clock race partition

`InverseGreedy/FiniteIndependentExp.lean` additionally constructs the **genuine
finite-indexed exponential product measure** for arbitrary finite vertex
sets (including the empty set). It proves probability normalisation,
measurability and correct exponential marginal of every coordinate,
**joint independence of all coordinates** and singleton-clock-time
nullity. Imported Lean and the full Python/certified census both passed at
exact code SHA `f92f6c807f5241768b53ccba11cd38a60ed19968`,
[Actions 41443061251](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41443061251).
See `proof/S020_FINITE_CLOCK_MODEL.md`. This does not yet prove
pairwise clock tie-nullity or probabilities of finite ordering chambers.

`InverseGreedy/ContinuousRacePartition.lean` derives the measure-one
strict-winner partition for two actual independent exponential clocks
at any strictly positive rates, and proves coordinate-swap invariance
and equal-rate symmetry. The balanced equal-rate identity implies a
probability of 1/2 for either strict winner. The mathematical argument
is in `proof/S020_TWO_CLOCK_PARTITION.md`; PR
[#19](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/19)
contains the imported Lean module. At exact final PR #19 head `e55b90e13a9738d676d953aae8e2ae6c1df312dd`, both imported Lean and complete Python/census passed in [Actions 41443533808](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41443533808). PR #19 was squash-merged as `9fe340889d9e08d9d1d3c3895795617676da30eb`. See `CLAIMS.md` for exact claim boundaries.

**Open:** Lean proof of the unequal-rate event probability
`r/(r+s)`, finite-coordinate pairwise no-ties, almost-sure finite sorting and its `orderMass` pushforward. Those
are distinct from S018's verified discrete first-choice law.
`sessions/S021.md` is installed. Atlas remains 90/8/45.

## S019: genuine independent exponential clocks (two-clock Lean foundation)

`InverseGreedy/IndependentExpPair.lean` constructs the actual product of
Mathlib exponential measures on `ℝ × ℝ`, proves it is a probability measure
for positive rates, proves both coordinate marginal laws and independence,
and proves that individual exponential times and the two-clock tie event
have probability zero. These imported Lean results and the full
Python/certified census passed together at code SHA `b6417d43`,
[Actions 41421076123](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41421076123).
The complete all-finite-rate arrival-order formula has a full **informal
density/chamber proof**, not a Lean proof, in
`proof/EXPONENTIAL_CLOCK_BRIDGE.md`. Deterministic quadrature tests for
two and three clocks are in `tests/test_s019.py`.
PR #18 final head `d1a5c3d3` also passed both jobs in Actions 41421511927 and was squash-merged as `fafc4a43`.
The general continuous product-space/sorting pushforward to `orderMass`
remains open in Lean; `sessions/S020.md` is the next task.
No EGU atlas changes (90/8/45).

## S018: exact discrete greedy-output law — formally verified

The S018 imported Lean proof in `InverseGreedy/PriorityOutputPushforward.lean`
establishes the intended exact equality
`priorityOutputMass rates neighbours active target =
finiteRaceLaw rates neighbours active.card active target` for every
finite target, every finite symmetric neighbour map, and strictly
positive real rates. It uses the genuine all-target S017 weighted
priority deletion theorem. `PriorityProjectionPushforward.lean`
proves the weighted expectation identity for arbitrary retained-order
statistics, and `PriorityProjectionEvent.lean` handles the discrete
greedy-event and support lemmas.

**Verification:** the full imported Lean pushforward and complete Python/certified census passed at code SHA `3a3ea03d12b0752815fa6f6f6111ab58bdd5f1ff`, Actions 41417057969; exact final PR #17 head `217c38964f69a76cb3c7c93863a412ca27c4def1` also passed both jobs in Actions 41417531293, and PR #17 was squash merged as `34d3b9ce72e8413055dd6d0404c1d94081c99c78`. The weighted expectation lemma separately passed both at `75460ab`, Actions 41415466242. The full bridge is proved on paper in
`proof/GREEDY_OUTPUT_PUSHFORWARD.md` and independently tested exactly
in `tests/test_s018.py`. Independent Exp-clock sorting semantics are
still open and assigned to `sessions/S019.md`.

## Current mathematical results
- **IG-L25 (S017, Lean):** full weighted deletion consistency for the
  actual complete-permutation law. For every retained subset A⊆V,
  every strictly positive real rate assignment and **every target list**,
  the weighted mass of complete orders whose projection equals that
  target is exactly its intrinsic Plackett–Luce order mass when the
  list is a complete permutation of A, and zero otherwise. This includes
  A=∅ and conditional deletion after any prescribed first overall
  vertex. See `InverseGreedy/FullProjectedOrderExact.lean` and
  `proof/FULL_ORDERED_PROJECTION.md`. The complete all-target Lean theorem
  passed at exact S017 PR #16 head `7b1d6b127491`, in both
  push Actions 41409002580 and PR Actions 41409033377;
  squash merged as `bd67b5cc`. **Neither
  greedy-output pushforward nor independent exponential-clock semantics
  has yet been formally proved.**
- **IG-L24 (S016, Lean):** the *actual complete-permutation event* that
  vertex i is the first among any nonempty retained subset A of the
  active vertices has mass exactly r_i / Σ(A rates), for every strictly
  positive real rate vector. This closes first-retained-winner
  conditioning, **not** full ordered-subsequence deletion consistency
  or the greedy pushforward. See
  `InverseGreedy/FirstRetainedExact.lean` and
  `proof/FIRST_RETAINED_WINNER.md`. Exact tests include all subsets
  of nine strongly unequal-rate vertices. Initial dual-green CI:
  [run 41345774024](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41345774024).
- **IG-R1:** exact first-choice weighted recurrence of the terminal law.
- **IG-R2/IG-R3 (S011):** the finite positive weighted priority-order
  law is **deletion-consistent**: erasing any subset, including after
  conditioning on the first vertex, yields the size-biased order law
  on the retained set. Consequently its greedy-output pushforward
  satisfies exactly the recursive first-choice law, for finite simple
  graphs. Both theorems have complete informal proofs and independent
  exact arithmetic tests, and the *law-level Lean pushforward* is formally verified in S018
  at code SHA `3a3ea03d`, Actions 41417057969. See proof/PRIORITY_DELETION_CONSISTENCY.md.
- **IG-P1:** complete multipartite graphs are EGU; a star's centre gets
  the sum of the leaf rates.
- **IG-P2:** disjoint union is EGU iff every component is EGU.
- **IG-P3:** P4 is EGU with symmetric positive algebraic rate ratio
  (1+√3)/2.
- **IG-P4 (S002):** join G∨H is EGU iff both factors are EGU.
  Rescaling factor totals by their MIS counts gives uniformity.
  Consequently **every finite cograph** (P4-free graph) has a
  constructive positive **rational-rate** witness.
- **IG-P5 (S005):** complete connected n=5 classification: 20 EGU,
  the sole non-EGU graph is P5. Consequently, among *all* simple
  graphs on at most five vertices, only P5 is non-EGU (by union
  closure). Seven new exact witnesses (six integer and one Q(√3))
  close all seven open instances.
- **IG-P6 (S006):** six-vertex connected atlas index 1 (edges
  01,12,14,15,23) is EGU with strictly positive integer rates
  (3,6,4,5,3,3); all three MIS have probability 1/3 exactly.
  An explicit positive rational one-parameter family also works.
- **IG-P7 (S007):** false-twin invariance. Contracting two
  nonadjacent vertices with identical open neighbourhoods and adding
  their exponential rates preserves the entire terminal greedy law;
  conversely split the contracted rate. This settles 19 additional
  six-vertex graphs as EGU (16 exact rational and 3 exact Q(√3)
  lifted witnesses) and 3 more as non-EGU by contraction to P5.
  See proof/FALSE_TWIN_INVARIANCE.md and tests/test_s007.py.
- **IG-P8 (S008):** for every m>=1, the clique K_m with one private
  pendant leaf attached to each clique vertex is EGU. Give leaves rate
  1 and all clique vertices rate (m+1)^(1/m)-1 > 0; each of the m+1
  MIS then has probability 1/(m+1). At m=3 this proves connected n=6
  atlas index 8 EGU with the exact algebraic rates
  (1,1,1,cuberoot(4)-1,cuberoot(4)-1,cuberoot(4)-1), verified
  independently by first-choice recursion and all 720 weighted
  permutations in Q(cuberoot(4)). See proof/CLIQUE_CORONA.md.
- **IG-N1:** C6 cannot be EGU: product of the three opposite-pair
  probabilities ≤1/729, while uniformity would require 1/125.
- **IG-N1b (S012):** C6 is not even *approximately* EGU (AEGU).
  For **every positive rate vector** its greedy-output law has
  total-variation distance at least **4/45** from the uniform law on
  its five MIS. The existing three opposite-pair probability product
  bound forces one pair outcome to have mass at most 1/9, while the
  uniform target assigns 1/5. The 4/45 bound need not be sharp.
  See proof/C6_TV_GAP.md and tests/test_s012_c6_gap.py.
- **IG-N2 (S002):** P5 cannot be EGU: its four probabilities obey a
  strict minor p024*p13 > p03*p14. Since all graphs on ≤4 vertices
  are EGU, P5 is a **smallest-order obstruction**.
- **IG-N2b (S012): P5 is approximately but not exactly EGU.**
  With strictly positive rates **(1,1,t,1,1)** on P5 (t>0),
  its four-output law has exact total variation
  **t(3t+10)/[4(t+2)(t+4)] < 5t/16** from uniformity.
  Thus TV approaches zero as t→0+, but exact EGU remains
  impossible by the strict P5 minor. Since every graph on at most
  four vertices is exactly EGU, **P5 is the smallest-order
  unattained AEGU graph**. This is a second primitive boundary
  mechanism, distinct from star coronas. See
  proof/P5_APPROXIMATE_UNIFORMITY.md and tests/test_s012_p5_approx.py.
- **IG-N3 (S003):** P6 cannot be EGU: independent triple-race events
  produce an exact two-event bottleneck. Its output law has total
  variation distance **at least 1/25** from uniform, for all positive rates.

- **IG-N5 (S009):** every pendant corona of a star K_(1,m),
  m>=2, is **non-EGU for all strictly positive rates**, by a
  strict 2x2 probability minor among four spoke-selection outputs.
  Its smallest member is the corona of P3, connected n=6 atlas
  index 3; this supplies an eighth exact negative certificate.
  The same family has **unattained TV infimum zero**: a positive
  one-parameter rate family approaches uniform arbitrarily closely.
  See proof/STAR_CORONA_OBSTRUCTION.md and
  proof/CORONA_P3_OBSTRUCTION.md.
- **IG-N4 (S004):** the six-vertex cone over P5 (K1∨P5) is not EGU by the join theorem; it is atlas index 68.

- **IG-P9/IG-P10 (S010):** Define *approximately EGU* (AEGU) by
  infimum zero of total variation from the uniform MIS law, without
  requiring exact attainment. A disjoint union is AEGU iff both
  components are AEGU; a join of two nonempty graphs is AEGU iff both
  factors are AEGU. The S009 star coronas therefore generate further
  **unattained** AEGU families: C_m disjoint union K2 and C_m join K1,
  with explicit positive rates and exact TV identities.
  See proof/APPROXIMATE_EGU_CLOSURE.md and tests/test_s010.py.

These are self-contained informal mathematical proofs. Lean verification
and independent novelty certification must be distinguished; see
CLAIMS.md. Proofs in proof/FOUNDATIONS.md,
proof/JOIN_COGRAPHS.md, proof/P5_OBSTRUCTION.md,
proof/C6_OBSTRUCTION.md, proof/P6_OBSTRUCTION.md.

## Run experiments

Standard-library-only exact rational arithmetic:

    python -m unittest discover -s tests -v
    python experiments/exact.py

Optional NetworkX atlas enumeration:

    python -m pip install 'networkx>=3.4,<4' 'sympy>=1.13,<2'
    python experiments/census.py --max-n 6 --max-rate 4
    python experiments/census.py --max-n 6 --max-rate 4 --json

The **143 connected unlabeled graphs through six vertices**
currently have **90 proven positive**, **8 proven negative
(P5, P6, C6, K1∨P5, three false-twin P5 expansions and
star-corona(P3))**, and
**45 unresolved** instances. This is an
exhaustive enumeration but NOT an exhaustive classification:
a failed finite rate search or numerical optimisation does not
prove impossibility. See results/S009_ATLAS.md.

Optional numerical only:

    python -m pip install scipy numpy networkx
    python experiments/scan_small.py --max-n 6 --starts 4

## Lean
Lean 4/Mathlib are pinned. Compile using `lake exe cache get` and
`lake build` or inspect the latest GitHub Actions run.
InverseGreedy/ExponentialRace.lean formalises one pair formula identity;
InverseGreedy/CubicAMGM.lean formalises the cubic SOS inequality.
InverseGreedy/C6Product.lean **compiles the sharp six-factor bound**
(CI run #35, commit 181cda3), and P6Bottleneck.lean compiles the
P6 algebraic contradiction at the same SHA. Its quantitative TV
lemma was also verified at SHA b4e6fdd (CI run #40).
S004 adds a finite weighted-selection/ordering model, greedy output map,
first-choice normalisation and bounded output-law recurrence in
InverseGreedy/FiniteRace.lean (CI run #67 at de1b562b passed).
InverseGreedy/P6Orders.lean introduces explicit finite-order event
predicates and worked examples (verified in CI #75 at 030fc3aa);
the all-720-orders Lean proof is
still open, though the exhaustive Python check passed in S003. Check CLAIMS.md and the exact CI SHA
for whether the imported module compiled.
S005 formally proves positivity of individual finite order masses
(CI #82 at commit 62916d4). S006 adds a structural Lean proof of
**total head-choice tree mass = 1** for positive rates, verified in green CI #92 at commit 95314a7 (see CLAIMS.md); this is not yet
the theorem equating the tree leaves with the original `orderMass`
of permutations or their pushforward law.
S007 adds OrderLeafBridge.lean, identifying each duplicate-free
priority leaf's product of first-choice probabilities with
`orderMass` (Lean-verified at SHA 543cfe9, green CI run 41131451454); the full
permutation summation and greedy pushforward are still open.
S009 adds CoronaP3Minor.lean, with the strictly positive algebraic
four-corner minor for the star-corona obstruction. This was imported
and verified at exact PR SHA ed0d02d4 (successful push and PR runs
41188364427 / 41188368166);
the independent-clock event factorisation remains a paper proof.
S008 adds FullPermutationSupport.lean: the actual Mathlib
List.permutations enumerates exactly the nodup lists whose underlying
finset is active, and all members obey the S007 leaf-mass equality.
It is **not yet** the normalization of the full permutation sum or the
pushforward identity to finiteRaceLaw. CI status is tracked in CLAIMS.md.
**S011:** FullPermutationDecomposition.lean proves in Lean that the
actual Mathlib full permutation list decomposes into distinct heads
and all corresponding tail permutations, *with multiplicity one*;
exact Python and imported Lean CI passed at SHA 00fb0afe (run
41195940431). FullPermutationNormalization.lean proves that the weighted `orderMass`
values of **all actual full permutations sum to exactly 1**, for every
positive real rate vector. Both imported Lean and Python CI passed at
exact final PR #10 SHA 1850e94398964fba7e021b29b6a6fa460f8c73c1
(PR run 41196801662), merged as 0e5949b4. The theorem first passed
at SHA a613bb87. The S011 independent Fraction tests
and paper proof establish the finite deletion-consistency and greedy
pushforward statements mathematically; the full formal law-level
pushforward remains open.

**S012 verified Lean advances:** GreedyBlockedErasure.lean proves the
pointwise first-choice residual identity for symmetric neighbour maps:
after accepting a vertex, its later neighbours may be deleted without
changing the final accepted set; scanning nonneighbours is independent
of the seed containing the first vertex. PriorityOutputLaw.lean defines
the weighted full-permutation greedy-output event mass and proves it
is between zero and one for each target using S011 normalization.
C6TVGap.lean formally derives a 4/45 uniform-event deficit from the
existing C6 product bound (pure algebra, not the full stochastic
event-to-TV identification). P5ApproximateBoundary.lean formalises the separate rational TV
identity and a positive linear upper bound for the new unattained
P5 approximate-uniformity family; its compilation status is
in CLAIMS.md. Full Python+Lean CI verification and SHAs
are in CLAIMS.md. **Weighted restriction and law-level
priorityOutputMass = finiteRaceLaw remain unproved in Lean**; S013
targets those separately. C6's quantitative non-AEGU theorem is a
complete paper result, with exact finite tests, not independently
certified as novel.

**S013 discrete law progress:** PriorityHeadConditioning.lean proves
in Lean that every weighted statistic of the first vertex and suffix,
summed over the *actual* full List.permutations, factors as a
firstChoice-weighted sum over all possible heads and their remaining
priority permutations (IG-L20, green full Python+Lean Actions at SHA
5cce19f). PriorityHeadEvents.lean applies this to arbitrary events
and the S012 first-choice deterministic greedy residual equation
(IG-L21; compiled status in CLAIMS.md). Its conditional tail still
includes blocked vertices: **the law-level weighted restriction to the
induced residual vertex subset and the equality
`priorityOutputMass = finiteRaceLaw` remain unproved in Lean**.
Continuous independent Exp-clock equivalence is separate and open.
See proof/WEIGHTED_HEAD_EVENTS.md and tests/test_s013.py.

**S014 projected-order bridge:** ProjectedOrderLaw.lean defines the *actual* weighted mass of a List.filter-projected priority-order event and proves its retained/discarded first-head equation, extending S013's general head law. It also adds an algebraic retained-winner rate cancellation and the empty-retained-set boundary. The structural head recurrence compiled with complete Python+Lean CI at PR SHA 4008362 (Actions run 41223548014); final-head status of additional lemmas is in CLAIMS.md. The event-level **first-retained-winner probability itself is not yet proved in Lean**, nor is full weighted deletion consistency or the complete greedy pushforward. Paper argument and exact tests: proof/WEIGHTED_PROJECTION_HEAD.md; tests/test_s014.py. S015 is installed.

**An equivalence to independent exponential clocks and the P6/C6
symbolic event-law formulas have NOT been formalised end-to-end in Lean.** Never report more than the
specific build SHA proves.

**S010 finite-law Lean step:** FiniteLawFuel.lean establishes
strict cardinality decrease afterChoice, fuel independence of
finiteRaceLaw above active.card, and deletion of a blocked vertex from
a complete priority scan. Green Python+Lean CI at final PR SHA 8064bde, Actions run
41193924574 (PR #9 merged as 8c61154), for these imported lemmas; the complete `List.permutations` sum and
pushforward are **still open**. The closure theorem IG-P9/IG-P10
is an informal proof with exact Python checks, not Lean-formalised.


**S015 support-level projection formalization:** The new ProjectionSupport.lean proves that projecting an actual complete priority permutation yields an actual complete permutation of the retained set. It follows that unsupported projected target orders have exactly zero mass, and the unique singleton-retained projected order has probability one for every positive real rate vector. Seven-vertex exact rational tests now check all 128 retained subsets. Both full Python/census and imported Lean passed on exact final PR #14 head 3583f27d (Actions run 41290187561); squash merged as fd08c64a. Thus these support/singleton statements are Lean-verified. This does **not** establish the first-retained-winner probability for multiple retained vertices, all-order deletion consistency, or the greedy pushforward. See proof/PROJECTED_SUPPORT.md and sessions/S016.md.

## Navigation
proof/FALSE_TWIN_INVARIANCE.md — S007 structural closure and obstructions;
results/S009_ATLAS.md — new 90/8/45 partial census;
proof/CLIQUE_CORONA.md — all-size constructive clique-corona EGU theorem;
proof/GREEDY_RESIDUAL_IDENTITY.md — S012 deterministic Lean proof;
proof/WEIGHTED_HEAD_EVENTS.md — S013 full priority event head law;
proof/WEIGHTED_PROJECTION_HEAD.md — S014 retained/discarded projection head recursion;
proof/C6_TV_GAP.md — S012 non-AEGU C6 TV lower bound;
proof/P5_APPROXIMATE_UNIFORMITY.md — S012 smallest unattained AEGU;
proof/FIVE_VERTEX_ATLAS.md — full n=5 theorem;
proof/SIX_VERTEX_INDEX1.md and results/S006_ATLAS.md — new n=6 witness;
CLAIMS.md — rigorous status ledger;
AGENTS.md — execution and honesty rules;
HANDOVER.md and ROADMAP.md — progress/next work;
sessions/S020.md — installed next session;
PRIOR_ART.md — preliminary literature, not priority certificate.

The separate [Greedy Uniformity on Trees](https://github.com/jfairfaxball-348/Greedy-Uniformity-on-Trees)
(arXiv:2610.02276) is the **equal-rate** predecessor, read-only.
No Inverse Greedy arXiv publication or Palomar registration is claimed.

See also proof/STAR_CORONA_OBSTRUCTION.md for the S009 all-size non-EGU family.
