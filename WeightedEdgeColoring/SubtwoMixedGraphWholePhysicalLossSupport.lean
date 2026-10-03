import WeightedEdgeColoring.SubtwoMixedGraphWholePhysicalLoss
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeExtraCaptureBuckets

/-! The dyadic weight ratio is needed only on residual support. -/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Class : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

theorem uncolored_selectedMixed_joint_starWeight_le_of_support
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma ratio : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (T : Finset G.E) (hT : ∀ e, e ∈ T ↔ G.weight e < beta)
    (decision : {e : G.E // e ∈ T} → Option (Fin (Fintype.card Color)))
    (hdisjoint : Disjoint
      (G.ordinarySelectedEdges
        ((G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
          residual x M).map
            (OrdinarySlotChoice.colorEquiv
              (Fintype.equivFin Color)).toEmbedding)) T)
    (hr0 : ∀ e, 0 ≤ residual e) (hreserve : 0 < reserve)
    (hgamma1 : gamma < 1)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (hratio : ∀ e, 0 < residual e →
      upper (bucket e) ≤ ratio * G.weight e)
    (largeLoss tinyLoss : G.V → ℝ)
    (hlarge : ∀ v, G.uncoveredLargeStarWeight
      ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))
      beta M v ≤ largeLoss v)
    (htiny : ∀ v, G.tinyResidualIntegralLossLoad decision v ≤ tinyLoss v)
    (v : G.V) :
    (∑ e ∈ Finset.univ \ (G.ordinarySelectedEdges
        ((G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
          residual x M).map
            (OrdinarySlotChoice.colorEquiv
              (Fintype.equivFin Color)).toEmbedding) ∪
        G.tinyDecisionColoredEdges T decision),
      if G.Inc v e then G.weight e else 0) ≤
      largeLoss v +
        2 * ratio * G.weightedResidualStar residual v / (1 - gamma) +
        2 * (1 + (reserve : ℝ)) * ∑ h, upper h + tinyLoss v := by
  rw [G.uncolored_selectedMixed_joint_starWeight_eq K N beta bucket gamma
    reserve residual x M T hT decision hdisjoint v]
  have hremain := G.dyadicLargeRemainingStarWeight_le_uncovered_add_extra
    K N beta bucket gamma reserve residual x M hM v
  have hextra :=
    G.selectedDyadicExtraEdges_starWeight_le_weightedResidual_of_support
      K N bucket gamma ratio reserve residual x M hM hr0 hreserve
      hgamma1 upper hupper0 hweight hratio v
  linarith [hlarge v, htiny v]

end WeightedMultigraph

end
end WeightedEdgeColoring
