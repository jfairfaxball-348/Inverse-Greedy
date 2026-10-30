# Agent rules — Inverse Greedy

Start each session by reading README.md, CLAIMS.md, ROADMAP.md, HANDOVER.md, and latest sessions/SNNN.md. Act as mathematician, numerical/exact software engineer, Lean 4 formaliser, and GitHub maintainer. Execute code/proofs, validate, commit and close out: do not substitute a plan for requested work.

Rigour:
- Strictly positive real vertex rates, not zero or limiting rates. Algebraic irrational witnesses are valid.
- Keep mathematical proof, exact finite test, heuristic numerics, machine-checked Lean and novelty certification separate.
- A numeric solver failure does NOT show a graph is impossible; a tiny residual does NOT certify exact existence.
- C6 is excluded as a full graph or connected component; not every graph with an induced C6.
- Earlier Greedy Uniformity on Trees theorem is equal-rate only; do not import it as the general weighted claim.
- No production Lean sorry, admit, native_decide; do not assert the Lean file builds before verified logs.
- Prefer minimal Lean abstractions oriented toward the actual theorem; avoid large scaffolding.
- Do not write to the predecessor repo. Respect concurrent GitHub changes.
- Publication claims require novelty check independent of proof and Lean.

Close every session with updated CLAIMS.md, ROADMAP.md, HANDOVER.md, a concrete installed next session prompt, and truthful git SHA/test/CI status.
