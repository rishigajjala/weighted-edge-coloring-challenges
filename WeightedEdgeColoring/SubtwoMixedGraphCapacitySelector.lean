import WeightedEdgeColoring.SubtwoMixedGraphPairSupport
import WeightedEdgeColoring.FinitePartialResamplingPackingSelection
import WeightedEdgeColoring.FinitePartialResamplingPackingMeanSelection
import WeightedEdgeColoring.FinitePartialResamplingNumericsBounds

/-!
# Packing selection on concrete mixed graph words

The finite selector sees one common packed word per vertex.  Each word
decodes one actual `Option (Σ label, local profile)` atom per color.  A
per-color family of capacity rows lifts to these words with exact row means
and only the explicit `|Color|` column factor.  The selected packed states
have positive product probability and therefore decode to genuine labelled
words.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

variable (RowAt : Color → Type*)
  [∀ c, Fintype (RowAt c)] [∀ c, DecidableEq (RowAt c)]

abbrev MixedGraphCapacityRow := Σ c : Color, RowAt c

def mixedGraphWordCapacityUse
    (atomUse : ∀ v c,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c → RowAt c → ℝ)
    (v : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (row : MixedGraphCapacityRow RowAt) : ℝ :=
  atomUse v row.1
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R v packed row.1)
    row.2

/-- Apply the finite packing selector to actual mixed graph atoms.  The
resulting row bound is directly on the decoded state used by the edge
candidate and matching constructions. -/
theorem exists_mixedGraphPackedWord_capacity_lt
    (omega meanBound columnBound : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hmeanBound : 0 < meanBound) (hcolumnBound : 0 ≤ columnBound)
    (atomUse : ∀ v c,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c → RowAt c → ℝ)
    (hatom0 : ∀ v c z row, 0 ≤ atomUse v c z row)
    (hatom1 : ∀ v c z row, atomUse v c z row ≤ 1)
    (hmean : ∀ c row,
      (∑ v, ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        G.smoothedMixedGraphProbability
          proposal edgeLabel qLaw R omega v c z *
          atomUse v c z row) ≤ meanBound)
    (hcolumn : ∀ v c z,
      ∑ row : RowAt c, atomUse v c z row ≤ columnBound) :
    ∃ choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R,
      (∀ v, 0 < G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega v (choice v)) ∧
      ∀ row : MixedGraphCapacityRow RowAt,
        (∑ v, atomUse v row.1
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
            v (choice v) row.1) row.2) <
          meanBound +
            FinitePartialResamplingNumerics.packingDeviation meanBound
              (Fintype.card Color * columnBound) := by
  classical
  let prob := G.paddedMixedGraphWordProbability
    proposal edgeLabel qLaw R omega
  let use := G.mixedGraphWordCapacityUse
    proposal edgeLabel qLaw R RowAt atomUse
  have hcolumnWhole : 0 ≤ Fintype.card Color * columnBound :=
    mul_nonneg (Nat.cast_nonneg _) hcolumnBound
  have hprob0 : ∀ v packed, 0 ≤ prob v packed := by
    intro v packed
    exact G.paddedMixedGraphWordProbability_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 v packed
  have hprobSum : ∀ v, ∑ packed, prob v packed = 1 := by
    intro v
    exact G.sum_paddedMixedGraphWordProbability
      proposal edgeLabel qLaw R omega v
  have huse0 : ∀ v packed row, 0 ≤ use v packed row := by
    intro v packed row
    exact hatom0 v row.1
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        v packed row.1) row.2
  have huse1 : ∀ v packed row, use v packed row ≤ 1 := by
    intro v packed row
    exact hatom1 v row.1
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        v packed row.1) row.2
  have hmeanPacked : ∀ row : MixedGraphCapacityRow RowAt,
      FiniteCategoricalSelection.rowMean prob use row ≤ meanBound := by
    intro row
    change (∑ v, ∑ packed,
      prob v packed * use v packed row) ≤ meanBound
    have heq : (∑ v, ∑ packed,
        prob v packed * use v packed row) =
      ∑ v, ∑ z : G.MixedGraphAtom
        proposal edgeLabel qLaw R v row.1,
        G.smoothedMixedGraphProbability
          proposal edgeLabel qLaw R omega v row.1 z *
          atomUse v row.1 z row.2 := by
      apply Finset.sum_congr rfl
      intro v _
      exact Subtwo.sum_paddedLabelledProbability_mul_decode_coordinate
        (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
        (fun _ _ ↦ none)
        (mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r))
        (fun v c ↦ G.mixedGraphAtom_card_le
          proposal edgeLabel qLaw R v c)
        (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
        (fun v c ↦ G.sum_smoothedMixedGraphProbability
          proposal edgeLabel qLaw R omega v c)
        v row.1 (fun z ↦ atomUse v row.1 z row.2)
    rw [heq]
    exact hmean row.1 row.2
  have hcolumnPacked : ∀ v packed,
      (∑ row : MixedGraphCapacityRow RowAt,
        use v packed row) ≤ Fintype.card Color * columnBound := by
    intro v packed
    rw [Fintype.sum_sigma]
    calc
      (∑ c : Color, ∑ row : RowAt c,
        use v packed ⟨c, row⟩) ≤
          ∑ _c : Color, columnBound := by
        apply Finset.sum_le_sum
        intro c _
        exact hcolumn v c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R v packed c)
      _ = Fintype.card Color * columnBound := by simp
  obtain ⟨choice, hchoicePos, hchoiceLoad⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_packingThreshold
      meanBound (Fintype.card Color * columnBound)
      hmeanBound hcolumnWhole prob use
      hprob0 hprobSum huse0 huse1 hmeanPacked hcolumnPacked
  refine ⟨choice, hchoicePos, ?_⟩
  intro row
  have hload := hchoiceLoad row
  have hthreshold :=
    FinitePartialResamplingNumerics.packingThreshold_le_base_add_deviation
      hmeanBound hcolumnWhole
  exact lt_of_lt_of_le hload hthreshold

end WeightedMultigraph

end

end WeightedEdgeColoring
