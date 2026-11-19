# Inverse Greedy — visual manuscript brief

**Direction set by owner: 19 November 2026.**
**Registered result supplied by owner:** [PALOMAR-2026-11-19-000021 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-19-000021&version=1).
**Source of mathematical claim:** `Challenge.lean`, `Solution.lean`, `formalization.yaml`, and imported Lean proof modules. Verify the public registry JSON's source SHA and exact theorem before finalising the manuscript metadata; the interactive entry page was not independently machine-readable when this brief was created.

## Editorial objective

Write a rigorous, readable, **highly visual** paper on the complete classification for finite simple graphs with **at most five vertices** under **independent Exp(rate) arrival clocks with strictly positive real rates**: random greedy selection of an **inclusion-maximal** independent set can be made exactly uniform over all MIS if and only if the whole graph is **not isomorphic to P5**.

An exposition, not a transcript of the Lean development. The article should earn publication on mathematical clarity, accurate attribution, independently reviewable arguments and substantive contribution; Palomar registration is proof checking, **not novelty certification or peer review**.

Draft title: **Uniformising random greedy maximal independent sets on graphs with at most five vertices**. Treat title as provisional until the completed prior-art audit and journal choice.

## Figure-first storyboard (target 6–8, adjust to content)

Every figure must answer a specific mathematical question. No decorative stock art.

| Fig. | Intended figure | Mathematical message / validation |
| --- | --- | --- |
| 1 | **Exponential-clock greedy scan**: an explicitly labelled small graph, vertex arrival timeline and accepted/rejected states in successive panels | Exactly explain algorithm and why terminal set is inclusion-maximal. Draw a mathematically valid clock order, not an invented sampled distribution. |
| 2 | **Control by rates on P3**: `1—2—3`; rates `(1,2,1)`; two terminal sets `{2}` and `{1,3}`, each with probability `1/2` | Analytic law: `Pr({2})=λ₂/(λ₁+λ₂+λ₃)`, `Pr({1,3})=(λ₁+λ₃)/(λ₁+λ₂+λ₃)`. Show exact computation beside visual. |
| 3 | **P5's four maximal independent sets**: four copies of labelled path `1—2—3—4—5` with selected sets `{1,3,5}`, `{1,4}`, `{2,4}`, `{2,5}` | Make target uniform distribution `1/4` transparent. Do **not** imply a numerical optimisation failure is the obstruction proof. |
| 4 | **P5 obstruction mechanism**: diagram of the actual necessary inequalities / incompatibility extracted from the formalised obstruction argument | Only include once the inequalities and arrow implications are checked against source lemmas. The picture must explain, not replace, a rigorous proof. |
| 5 | **Small-graph classification atlas**: panel or carefully grouped strip of isomorphism classes through five vertices, singling out the sole P5 exception | Validate source enumeration and distinguish up-to-isomorphism counts from labelled graphs; ensure visual density remains legible. |
| 6 | **Positive-rate witness gallery**: representative EGU graphs including the instructive P4 noncograph case with verified rate assignments and exact output masses | Extract witnesses from Lean or exact certificates; verify all rates strictly positive and the law exactly uniform. No decimal-only certificates. |
| 7 | **Proof architecture**: true Exp product measure → random order law → greedy-output law → constructive cases and P5 obstruction → iff classification | Distinguish formal theorem dependencies from conceptual simplification; link to named source lemmas. |
| 8 (optional) | **Formal assurance and scope**: independent Challenge/Solution, Comparator and kernels, pinned registry result | Accurately separate machine-checked theorem, exact-computation aids, ordinary-math supplementary arguments and still-open n=6 research. |

If a figure fails to clarify the proof or result, remove it rather than chase a quota. Provide explanatory proofs in text; graphics are supporting arguments.

## Visual standards

- Figures must be **vector-first** (TikZ/PGFPlots or reproducible SVG/PDF, sources checked into `manuscript/figures/`). Avoid bitmaps/screenshots for graph drawings.
- Use consistent vertex labels and rates. Adopt a restrained, colourblind-aware palette: selected vertices teal/blue, blocked vertices light grey, exceptional/obstructed path amber/red; never rely on colour alone. Use shape, stroke and legend redundantly.
- Each figure receives a standalone descriptive caption: assumptions, exact meaning of shading/arrows, source of any data, and whether the example is schematic.
- Every graph illustration is checked against actual edge lists, MIS enumeration, and rate certificates. Every plot is generated from exact data or openly labelled simulation with reproducible parameters and seed. No decorative or fabricated curves, error bars or frequencies.
- Keep the body readable in black and white, at single-column size and in PDF accessibility-conscious text; use embedded fonts and vector line work.
- Maintain a figure ledger (`manuscript/figures/README.md`) noting source script, validation command, claim and manuscript citation. All included figures must be referred to in text.

## Target manuscript structure

1. Abstract (scope, main theorem, method, formality — no priority overclaims).
2. Introduction and careful distinction from uniform-priority RSA and uniform MIS sampling.
3. Definitions, true independent Exp(rate) model, greedy MIS and EGU.
4. Worked example and stochastic recursion (Figs 1–2).
5. Statement of exact `n≤5` classification and P5 example (Figs 3 and 5).
6. Proof: positive constructions / closure cases and strict P5 obstruction (Figs 4 and 6).
7. Formalisation: mathematical-to-Lean correspondence, genuinely checked stochastic foundation (Fig 7; optional 8).
8. Related work, limitations and open directions (label n=6 statements by their actual verification tier).
9. References; optional appendix for exhaustive finite certificates and figure generation.

## Mandatory scientific boundaries

- The registered **n≤5 iff** is the centrepiece, not a claimed classification of all finite graphs.
- **Maximal** means inclusion-maximal, not maximum cardinality.
- EGU requires strictly positive **finite real** rates; limiting constructions demonstrate only approximate uniformity unless proved otherwise.
- The exclusion of P5 is by **whole-graph isomorphism**, not by mere appearance as an induced path.
- Six-vertex atlas status **90 EGU / 8 non-EGU / 45 unresolved** applies to the connected n=6 atlas and is separate from the registered theorem; full Lean exhaustiveness of the 156/112 orbit decomposition and all-m AEGU are not to be asserted.
- Do not claim Palomar certifies novelty, significance, informal proof correctness or journal acceptance; explicitly disclose the automation contribution in the paper as appropriate.
- Literature/priority audit must cover cited sources and direct competitors, not only repository notes; assess whether the small-order classification warrants a standalone paper, versus expanding it with independently proven graph families.
- Do not start a new proof-checking workflow merely to update manuscript prose. Preserve pinned formal source and cite its exact registered commit once verified.

## Acceptance criteria for first complete visual draft

- `manuscript/main.tex`, `references.bib`, figure sources, build instructions, one PDF draft and figure ledger.
- At least five **mathematically useful** fully captioned figures in the first complete draft, aiming at six to eight where justified.
- Accurate proof narrative traceable to Lean source, with independent checking of every nontrivial displayed calculation, witness and diagram.
- All claims consistently classified as formal / exact computational / ordinary mathematical / open; every graphic has a provenance record.
- Reproducible figure and LaTeX build, legibility check at typical print scale, citations audited and no unsubstantiated novelty/priority language.
