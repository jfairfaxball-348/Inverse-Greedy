import InverseGreedy.SixVertexEdgeEncoding

/-!
# S044: two formally certified six-vertex orbits and Burnside arithmetic

The 15 possible singleton-edge graphs are all isomorphic, by explicit
two-swap permutations and kernel Boolean certificates. The same is true
for the 15 complements (graphs with a unique missing edge).

The numeric Burnside rows below are derived in exact independent PYTHON.
Lean proves only their weighted ARITHMETIC; it does NOT yet prove that the
rows enumerate all fixed graphs or formalise Burnside's lemma. In particular
these checks do not certify 156/112 graph orbits in the Lean kernel.
-/

namespace InverseGreedy

/-- A graph with exactly one undirected edge, at position e. -/
def singletonEdgeVector6 (e : Fin 15) : Fin 15 → Bool :=
  fun j => decide (j = e)

/-- Complement of a one-edge graph (one missing edge). -/
def missingEdgeVector6 (e : Fin 15) : Fin 15 → Bool :=
  fun j => !(singletonEdgeVector6 e j)

/-- Swap the first endpoint of edge e to vertex zero. -/
private def oneEdgeSwapFirst6 (e : Fin 15) : Equiv.Perm (Fin 6) :=
  Equiv.swap (pair6 e).1 0

/-- Swap the image of the other endpoint to vertex one. -/
private def oneEdgeSwapSecond6 (e : Fin 15) : Equiv.Perm (Fin 6) :=
  Equiv.swap (oneEdgeSwapFirst6 e (pair6 e).2) 1

def oneEdgeToBase6 (e : Fin 15) : Fin 6 → Fin 6 :=
  fun v => oneEdgeSwapSecond6 e (oneEdgeSwapFirst6 e v)

def baseToOneEdge6 (e : Fin 15) : Fin 6 → Fin 6 :=
  fun v => oneEdgeSwapFirst6 e (oneEdgeSwapSecond6 e v)

/-- All 15 single-edge isomorphism witnesses checked by the Lean kernel. -/
theorem s044_singleton_edges_certified :
    ∀ e : Fin 15,
      IsoCheckB rank6 (singletonEdgeVector6 e) (singletonEdgeVector6 0)
        (oneEdgeToBase6 e) (baseToOneEdge6 e) = true := by
  decide +kernel

/-- All 15 one-missing-edge isomorphism witnesses checked by the kernel. -/
theorem s044_missing_edges_certified :
    ∀ e : Fin 15,
      IsoCheckB rank6 (missingEdgeVector6 e) (missingEdgeVector6 0)
        (oneEdgeToBase6 e) (baseToOneEdge6 e) = true := by
  decide +kernel

/-- Actual graph isomorphism, not merely a Boolean equality. -/
theorem s044_singleton_edges_isomorphic (e : Fin 15) :
    ∃ p : Fin 6 ≃ Fin 6,
      ∀ v, nbOf rank6 (singletonEdgeVector6 0) (p v) =
        (nbOf rank6 (singletonEdgeVector6 e) v).map p.toEmbedding :=
  iso_of_isoCheckB rank6 _ _ _ _ (s044_singleton_edges_certified e)

/-- Corresponding isomorphism for complements of singleton-edge graphs. -/
theorem s044_missing_edges_isomorphic (e : Fin 15) :
    ∃ p : Fin 6 ≃ Fin 6,
      ∀ v, nbOf rank6 (missingEdgeVector6 0) (p v) =
        (nbOf rank6 (missingEdgeVector6 e) v).map p.toEmbedding :=
  iso_of_isoCheckB rank6 _ _ _ _ (s044_missing_edges_certified e)

/-- Each row gives (permutations of a cycle type, invariant graphs,
invariant CONNECTED graphs). Values imported from an independent exact
Burnside enumeration, and NOT Lean-proved graph counts. -/
def s044BurnsideRows : List (Nat × Nat × Nat) :=
  [(1, 32768, 26704),
   (15, 2048, 1456),
   (40, 128, 76),
   (45, 512, 344),
   (90, 32, 16),
   (120, 32, 16),
   (144, 8, 4),
   (15, 512, 416),
   (90, 32, 20),
   (40, 32, 25),
   (120, 8, 5)]

/-- The conjugacy-class multiplicities sum to |S6| = 720 (table arithmetic). -/
theorem s044_burnside_multiplicities :
    (s044BurnsideRows.map (fun row => row.1)).sum = 720 := by
  decide +kernel

/-- If these rows are proved to be exact fixed-graph counts, their
Burnside quotient is 156. This theorem checks ONLY the arithmetic. -/
theorem s044_burnside_all_arithmetic :
    (s044BurnsideRows.map (fun row => row.1 * row.2.1)).sum = 720 * 156 := by
  decide +kernel

/-- Analogous arithmetic check for the conditional connected count 112. -/
theorem s044_burnside_connected_arithmetic :
    (s044BurnsideRows.map (fun row => row.1 * row.2.2)).sum = 720 * 112 := by
  decide +kernel

end InverseGreedy
