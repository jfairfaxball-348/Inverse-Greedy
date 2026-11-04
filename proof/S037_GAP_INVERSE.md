# S037 — Finite gap/bin equivalence, verified scope and outstanding measured series

**Date:** 2026-11-04. **Merged release:** [PR #37](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/37).

Exact final PR head `8043465835fed9b1245b98f1e1e59bfe743dae8b` passed the complete imported Lean build and full Python/exact/certified connected n≤6 census in **both** push [Actions 41875794221](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41875794221) and PR [Actions 41875873962](https://github.com/jfairfaxball-348/Inverse-Greedy/actions/runs/41875873962); [PR #37](https://github.com/jfairfaxball-348/Inverse-Greedy/pull/37) squash-merged to `main` as `93c20facf8d3e396374aa066e6b46b266312431f`.

S035 proves in imported Lean the **genuine measured** strict-bin countable series `finiteIndependentExp_strictBin_series` from independent real Exp clocks. S036 built the forward sum map

`gapBinValue(d,j) = j + Σ_(a≤j) d_a`

and proved the successor recurrence.

## New S037 mathematical argument

For nonempty length `n+1`, define `gapDifferenceSucc(k)` by `d_0=k_0` and `d_(j+1) = k_(j+1) - k_j - 1` in natural subtraction. On every gap vector S036's recurrence gives `(k_(j+1)-k_j)-1=d_(j+1)`; at index zero the only prefix contribution is `d_0`. Thus `gapDifferenceSucc(gapBinValue(d))=d`.

Conversely, if `k` is strictly increasing, then `k_(j+1)≥k_j+1`. By induction on the position, the prefix-sum recurrence and the natural-difference definition give `gapBinValue(gapDifferenceSucc(k),j+1)=k_(j+1)`. Together these two statements yield `finiteGapBinEquiv n : (Fin n→ℕ) ≃ {bins : Fin n→ℕ // StrictMono bins}` for all finite lengths. The empty index case is the unique map between singleton function spaces.

The Lean source `InverseGreedy/FiniteClockGapInverse.lean` encodes the argument with `gapDifferenceSucc_gapBinValue`, `gapBinValue_gapDifferenceSucc`, and `finiteGapBinEquiv`. The module is imported by `InverseGreedy.lean`. These are **Lean-verified** on the exact final PR head with both Lean and Python/census green in push and PR Actions.

## Independent exact regression

`tests/test_s037.py` enumerates complete order permutations, uses rational rates represented by `q_i∈(0,1)`, and checks equality of finite *truncated* sorted-bin and constrained-gap sums; it separately checks monotone truncations and the classical analytic untruncated product upper bound. Repeated and incomplete coordinate lists are rejected. These finite tests are not an infinite-measure argument, and the closed-product bound is not a Lean theorem.

## Critical remaining gap

The equivalence acts on positional `Fin n` vectors. S035 sums over `ι→ℕ` and tests `strictBinAssignment order bins`. A formal transfer must **require** a proof that the list enumerates every coordinate of `ι` exactly once (and handle `ι` empty). Next use an ENNReal `tsum` reindexing theorem, genuine positive-clock cell masses, finite monomial factorisation, exchange of the geometric countable sums and their evaluation. Without those steps the continuous n≥3 exponential chamber probability, `δ→0` limit and measured greedy-output pushforward remain open.

Connected n≤6 atlas **90 EGU / 8 non-EGU / 45 unresolved**, independent novelty not certified.
