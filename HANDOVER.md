# S003 handover — 2026-10-30

## Main advance: IG-N3, path P6 is not EGU
A complete elementary event proof gives impossibility for all strictly
positive exponential rates on P6. Let u be probability that vertex 1
wins the race within {0,1,2}, and v for vertex 4 within {3,4,5}.
These races are independent. Greedy output {1,4} has probability uv;
output {0,2,5} or {0,3,5} has combined probability ≤(1-u)(1-v).
Uniform five-MIS output would require uv=1/5 and
(1-u)(1-v)≥2/5, impossible by (u-v)^2≥0. Stronger:
TV distance from uniform is always at least **1/25** using the two
events and their complement product bounds. Neither statement rests
on a numerical rate search. Full proof: proof/P6_OBSTRUCTION.md.

## Atlas
Python CI run #32 at c6460366: all 14 tests passed and connected
NetworkX n≤6 enumerated 143 graphs, **62 positive / 3 negative /
78 unresolved**. n6 negative indices: P6=5, C6=18. n5 P5=2.
Atlas results file: results/S003_ATLAS.md. Rate search bound 4
does not imply the other 78 are negative.

## Lean
S003 repaired C6Product.lean by keeping the six-factor polynomial
normalisation and field operations factored. Run #35 at commit
181cda3 successfully built imported Lean C6 six-factor inequality,
opposite pair product bound and 1/5 contradiction; also compiled the
P6 elementary algebraic contradiction. **Neither proof formalises
the stochastic greedy law/event probabilities**. The further Lean conditional algebraic 1/25-TV-gap lemma was verified
on commit b4e6fdd in GitHub CI run #40 (both jobs green).

## Verification and priority
P6 exact tests checked all 720 permutations for the event equivalence,
729 vectors in {1,2,3}^6 against exact Fraction recursion, plus
an independent weighted-permutation oracle. Bound TV≥1/25 also
tested on 729 vectors. External novelty audit remains provisional:
classic random sequential adsorption and iid random-priority papers
address related processes but have not been proven to settle the
positive-rate inverse-uniformity question.

## Next
sessions/S004.md: formal finite weighted-race/output model end-to-end,
then further exact graph classifications; preserve the C6 CI gain.
