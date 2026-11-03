# S033 companion — genuine finite-family zero-bin nullity

Date: 2026-11-03. Imported Lean file:
`InverseGreedy/FiniteClockBinExceptions.lean`.

## Purpose

The ceil-bin variable is `Kδ(t) = Nat.ceil(t / δ)` for `δ>0`.
Its exceptional cell `Kδ(t)=0` equals `t≤0`; all positive
one-based cells are of the form `k+1` for `k∈ℕ`.
S026 proves this zero cell has exactly zero mass for each genuine
positive-rate exponential clock. Before applying the S032 joint
cylinder masses to a finite family, the whole family must avoid the
exceptional zero cell almost surely.

## Results (formal proofs; CI status must be checked at exact commit)

For a finite type `ι` (including empty and singleton), strictly
positive real `rates : ι → ℝ`, `δ>0`, and
`μ = finiteIndependentExp rates`:

1. For each `i : ι`, `μ {ω | Kδ(ω i)=0} = 0`.
   Proof: transport the preimage event through the actual marginal
   map `ω ↦ ω i`, use S020's finite coordinate law, and
   apply S026's one-clock zero-bin theorem.
2. `μ {ω | ∃ i, Kδ(ω i)=0} = 0`.
   Proof: this set is the finite-index union of the preceding
   coordinate events and measure countable/finite union nullity.
3. `μ {ω | ∀ i, Kδ(ω i)≠0} = 1`.
   Proof: the all-positive-bin event is measurable as an intersection
   of preimages of complements of integer singleton sets.
   Its complement is the zero-mass union in (2). The product
   measure has total mass one.

These are genuine results about continuous exponential product
measure, not declarations of a surrogate geometric-bin distribution.

## Separation from the parallel S033 work

PR #32 supplies the strict real-clock / strict-bin collision
sandwich and lifts the pair collision bound. This companion avoids
duplicating those theorems. Together with S032's joint positive-bin
cylinder result, it supports an eventual exhaustive decomposition
of finite strict-bin chambers. It does **not** supply that countable
joint series, a finite collision union bound, its width-zero limit,
the complete `n≥3` real-clock chamber mass or the measurable
greedy-output pushforward.

The partial connected graph atlas remains **90 EGU / 8 non-EGU /
45 unresolved**. No novelty, Palomar, or arXiv claim is made.
