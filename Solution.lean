module

public import Mathlib
public import InverseGreedy.SmallGraphClassification

@[expose] public section

/-!
# Independent mathematical interface: inverse exponential-clock greedy uniformity

Only core/Mathlib is imported. Vertices have independent exponential clocks
with *strictly positive* rates. Vertices are greedily accepted in increasing
clock order; the target distribution is uniform over **maximal** (not maximum)
independent sets. The five-vertex path is identified up to graph isomorphism.

The solution uses the original imported Lean proof, after matching this
independent mathematical interface definitionally.
-/

open MeasureTheory ProbabilityTheory

namespace PalomarEGU

variable {α : Type*}

/-- A deterministic clock-comparison pattern. -/
noncomputable def clockComparisonPattern (ω : α → ℝ) : α → α → Bool :=
  fun i j => decide (ω i ≤ ω j)

/-- Stable sorting (ties are null under positive exponential rates). -/
noncomputable def clockSortedOrder [Fintype α] (ω : α → ℝ) : List α :=
  (Finset.univ : Finset α).toList.mergeSort (clockComparisonPattern ω)

/-- Accept a vertex unless it has an already accepted neighbour. -/
def greedyAccept [DecidableEq α] (neighbours : α → Finset α)
    (accepted : Finset α) (v : α) : Finset α :=
  if (neighbours v ∩ accepted).Nonempty then accepted else insert v accepted

/-- Deterministic greedy scan through a priority list. -/
def greedyOutput [DecidableEq α] (neighbours : α → Finset α)
    (order : List α) : Finset α :=
  order.foldl (greedyAccept neighbours) ∅

/-- Real-clock greedy output, with a deterministic null-event tie break. -/
noncomputable def realClockGreedyOutput [Fintype α] [DecidableEq α]
    (neighbours : α → Finset α) (ω : α → ℝ) : Finset α :=
  greedyOutput neighbours (clockSortedOrder ω)

/-- A finite independent set. -/
def IsIndependentSet (neighbours : α → Finset α) (I : Finset α) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, v ∉ neighbours u

/-- Maximality under inclusion, not maximum cardinality. -/
def IsMaximalIndependentSet (neighbours : α → Finset α) (I : Finset α) : Prop :=
  IsIndependentSet neighbours I ∧ ∀ v, v ∉ I → ∃ u ∈ I, v ∈ neighbours u

instance IsIndependentSet.decidable [DecidableEq α]
    (neighbours : α → Finset α) (I : Finset α) :
    Decidable (IsIndependentSet neighbours I) := by
  unfold IsIndependentSet
  infer_instance

instance IsMaximalIndependentSet.decidable [Fintype α] [DecidableEq α]
    (neighbours : α → Finset α) (I : Finset α) :
    Decidable (IsMaximalIndependentSet neighbours I) := by
  unfold IsMaximalIndependentSet
  infer_instance

/-- All inclusion-maximal independent sets. -/
def maximalIndependentSets [Fintype α] [DecidableEq α]
    (neighbours : α → Finset α) : Finset (Finset α) :=
  (Finset.univ : Finset (Finset α)).filter
    (IsMaximalIndependentSet neighbours)

/-- The real independent Exp(rate) product measure from Mathlib. -/
noncomputable def finiteIndependentExp [Fintype α] (rates : α → ℝ) :
    Measure (α → ℝ) :=
  Measure.pi (fun i => expMeasure (rates i))

/-- Exactly uniform on all maximal independent sets using strictly positive
real rates for the independent exponential clocks. -/
def RealClockEGU [Fintype α] [DecidableEq α]
    (neighbours : α → Finset α) : Prop :=
  ∃ rates : α → ℝ, (∀ v, 0 < rates v) ∧
    ∀ I ∈ maximalIndependentSets neighbours,
      finiteIndependentExp rates
          {ω : α → ℝ | realClockGreedyOutput neighbours ω = I} =
        ENNReal.ofReal (1 / ((maximalIndependentSets neighbours).card : ℝ))

/-- Labelled path 0–1–2–3–4. -/
def p5Nb : Fin 5 → Finset (Fin 5) :=
  ![{1}, {0, 2}, {1, 3}, {2, 4}, {3}]

/-- The full iff classification, for every graph on at most five vertices,
including the empty graph. The exception is *graph-isomorphism to P5*.
The positive-rate quantifier is inside RealClockEGU and is never relaxed. -/
theorem graphs_le_five_iff (n : ℕ) (hn : n ≤ 5)
    (nb : Fin n → Finset (Fin n))
    (hs : ∀ x y, y ∈ nb x → x ∈ nb y)
    (hi : ∀ v, v ∉ nb v) :
    RealClockEGU nb ↔
      ¬ ∃ e : Fin n ≃ Fin 5,
          ∀ a, p5Nb (e a) = (nb a).map e.toEmbedding := by
  have hbridge : RealClockEGU nb ↔ InverseGreedy.RealClockEGU nb := Iff.rfl
  have hp5 : p5Nb = InverseGreedy.p5Nb := rfl
  constructor
  · intro h hIso
    have hOld : InverseGreedy.RealClockEGU nb := hbridge.mp h
    obtain ⟨e, he⟩ : ∃ e : Fin n ≃ Fin 5,
        ∀ a, InverseGreedy.p5Nb (e a) = (nb a).map e.toEmbedding := by
      simpa only [hp5] using hIso
    have hp : InverseGreedy.RealClockEGU InverseGreedy.p5Nb :=
      (InverseGreedy.realClockEGU_congr_equiv e nb InverseGreedy.p5Nb
        he hs InverseGreedy.p5Nb_symm).mp hOld
    exact InverseGreedy.p5Nb_not_realClockEGU hp
  · intro hNotIso
    have hOldNotIso : ¬ ∃ e : Fin n ≃ Fin 5,
        ∀ a, InverseGreedy.p5Nb (e a) = (nb a).map e.toEmbedding := by
      simpa only [hp5] using hNotIso
    rcases InverseGreedy.graphs_le_five_classification n hn nb hs hi with h | h
    · exact hbridge.mpr h
    · exact (hOldNotIso h).elim

end PalomarEGU

-- Audit the actual declaration, not a guess about the proof's axiom closure.
#print axioms PalomarEGU.graphs_le_five_iff
