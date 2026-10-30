# S001 charter — Inverse Greedy

John Fairfax-Ball; 2026-10-30. Finite, simple, undirected graphs G=(V,E). Independent arrival clocks T_v ~ Exp(lambda_v), strictly 0 < lambda_v < infinity. Greedy accept a vertex iff no previously accepted neighbour. For each terminal maximal independent set I, P_{G,lambda}(I) is its probability.

Definition: G is **EGU** (exponentially greedily uniformisable) iff there exists a strictly positive lambda so every maximal independent set has probability 1/|M(G)|. The empty graph is EGU with its unique empty MIS. Scaling all rates in a component does not change the component output law.

Research objectives:
1. Exact probability recurrences and distributional constraints.
2. Positive explicit rate constructions on significant graph classes.
3. Rigorous impossibility certificates (inequalities, elimination).
4. Complete exact small-graph census, with **certificates** distinct from numerical fits.
5. Lean 4 formalisation of publication-grade theorem statements, prioritising mathematical simplicity.
6. Novelty audit and peer-review-quality manuscript only after a substantial theorem package.

Do not confuse: uniform terminal sets vs uniform permutations, uniform set sizes, maximum independent sets, well-coveredness, weighted-set Gibbs measures. Positive real rates may be irrational; rates zero or limiting rates do not qualify. No general closure under taking induced subgraphs is assumed.

Tracks: exact rational law; constructive rate design; negative obstructions; certified small graph atlas; Lean; literature/novelty audit. Final-boss direction: structural classification of all EGU finite graphs (or attainable output laws).

Research integrity: exact computation tests particular finite inputs; numerical optimisation suggests leads only; written proof != Lean checked proof; proof != new publication priority.
