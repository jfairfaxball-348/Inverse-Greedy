# Inverse Greedy paper — S049 working draft

The complete draft is `main.tex`, with four cited references in `references.bib`, seven numbered mathematical figures, an exact certificate appendix, and the independent, reproducible figure-check scripts in `figures/`.

## Reproduce

Requires Python 3, `networkx`, `sympy`, `matplotlib`, a standard TeX Live installation with TikZ/rotating/natbib, `bibtex` and `latexmk`.

```sh
cd manuscript
python figures/validate.py
python figures/generate_atlas.py
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The two Python commands test the finite graph enumerations and exact displayed numerical/algebraic assertions, then generate vector `figures/atlas.pdf`. Other six figures are authored in `figures/visuals.tex` (TikZ), fully vector on PDF export. `main.pdf` is an **editorial draft**, not a Palomar proof artifact. The PDF may be generated with the instructions above rather than checked in as a binary.

## Status and boundaries

- Centrepiece: registered n<=5 true independent-Exp(rate) positive-rate EGU iff non-P5 graph **up to graph isomorphism**. Excludes neither arbitrary larger graphs nor induced P5 graphs in general.
- P5 strict obstruction: four exact law formulas and positive-coefficient polynomial gap, traceable to `InverseGreedy/SmallGraphObstructions.lean`.
- Positive direction: formal kernel-checked finite witness classes and graph-isomorphism transfer in `InverseGreedy/SmallGraphClassification.lean`; the article gives a certified finite proof narrative, not a hand-enumerated 53-case appendix.
- Public entry supplied by owner: `PALOMAR-2026-11-19-000021` v1. **The exact immutable source SHA recorded in the live entry could not be independently extracted during S049**; manuscript says so candidly, and S050 must resolve before submission.
- Literature search is targeted, not exhaustive. The manuscript is not yet journal ready without independent critical editorial review, better bibliography breadth, and prioritisation/novelty audit. Palomar is not a journal, and its kernel checks do not certify novelty.
- No change to Lean source, registry submission, CI/preflight or the n=6 90/8/45 atlas.

See `figures/README.md` for a figure-by-figure ledger and `PRIOR_ART_AUDIT.md` for the competing-literature comparison.