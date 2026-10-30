# S002 handover — 2026-10-30

**Mathematics.** IG-P4: joining two nonempty graphs preserves EGU exactly when each factor is EGU. Scale their total rates proportionally to their numbers of maximal independent sets. With disjoint-union closure, this constructively proves every finite cograph EGU, with positive rational rates. IG-N2: P5 is not EGU: p024*p13 > p03*p14 strictly at every positive rate vector. See proof/P5_OBSTRUCTION.md for the complete rational identity. Cographs plus P4 witness prove all graphs on ≤4 vertices EGU, so P5 is a smallest-order counterexample. C6 remains an independent obstruction.

**Census.** All 143 connected unlabeled graphs with n≤6 were enumerated via NetworkX graph_atlas_g(). Exact certificates: 62 positive, 2 negative (P5 index 2 at n5, C6 index 18 at n6), 79 **unresolved**. P6 is a numerical lead, NOT a negative theorem. Commands and bounds: results/S002_ATLAS.md, experiments/census.py.

**Verification.** tests/test_s002.py checks the P5 identity on all 243 positive integer rate vectors in {1,2,3}^5, and checks cograph rates via exact Fraction recursion through six vertices. Lean SOS AM-GM lemma was verified by GitHub Actions PR run #9 at SHA 59b05ba. InverseGreedy/C6Product.lean is an **UNVERIFIED DRAFT**: earlier CI runs #12–#19 failed due to elaboration timeouts for a large proof. It is intentionally NOT imported into the verified library root InverseGreedy.lean. S003 must repair, compile and re-enable the proof with verified logs before promotion. The stochastic greedy event-to-law is also not formalised in Lean. Inspect the latest branch CI before claiming a green build.

**Publication.** Independent novelty/priority audit still open; see PRIOR_ART.md. Do not confuse exponential priorities with random objective weights for maximum-weight independent sets. Do not infer any obstruction from an induced P5/C6 in a connected supergraph.

**Next session:** sessions/S003.md. First prove the C6 algebraic theorem reliably in Lean and connect to the actual stochastic race. Certify further atlas cases, prioritising P6. Close with observed SHA/status.
