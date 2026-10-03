import WeightedEdgeColoring.SubtwoQuotientFiniteTinyLabelFactory
import WeightedEdgeColoring.FiniteHarmonicClassEncoding

/-! Canonical finite/tiny threshold classes on any actual packet-base residual. -/

namespace WeightedEdgeColoring.WeightedMultigraph

noncomputable section
universe u
namespace GeneralColoredPacketBase
variable {G : WeightedMultigraph.{u}} {K : ℕ}
variable (C : G.GeneralColoredPacketBase K)

noncomputable def quotientFiniteEdges (T : ℕ) : Finset C.residualGraph.E :=
  Finset.univ.filter fun e => (1 : ℝ) / T ≤ C.residualGraph.weight e

private theorem quotientFiniteWeightLower (T : ℕ)
    (e : (C.residualGraph.edgeRestriction (C.quotientFiniteEdges T)).E) :
    (1 : ℝ) / T ≤
      (C.residualGraph.edgeRestriction (C.quotientFiniteEdges T)).weight e := by
  exact (Finset.mem_filter.mp e.property).2

noncomputable def quotientThresholdClass (T : ℕ) (hT : 0 < T)
    (e : C.residualGraph.E) : Fin T :=
  if h : e ∈ C.quotientFiniteEdges T then
    (C.residualGraph.edgeRestriction (C.quotientFiniteEdges T)).finiteHarmonicClassOf
      T hT (C.quotientFiniteWeightLower T) ⟨e, h⟩
  else ⟨0, hT⟩

theorem quotientThresholdClass_weight_le (T : ℕ) (hT : 0 < T)
    (e : C.residualGraph.E) (he : e ∈ C.quotientFiniteEdges T) :
    C.residualGraph.weight e ≤
      (1 : ℝ) / finiteClassSize (C.quotientThresholdClass T hT e) := by
  rw [quotientThresholdClass, dif_pos he]
  exact (C.residualGraph.edgeRestriction (C.quotientFiniteEdges T)).weight_le_inv_finiteClassSize_finiteHarmonicClassOf
      T hT (C.quotientFiniteWeightLower T) ⟨e, he⟩

theorem quotientThresholdClass_charge (T : ℕ) (hT : 0 < T)
    (e : C.residualGraph.E) (he : e ∈ C.quotientFiniteEdges T) :
    harmonicCharge (C.residualGraph.weight e) =
      (1 : ℝ) / finiteClassSize (C.quotientThresholdClass T hT e) := by
  rw [quotientThresholdClass, dif_pos he]
  exact (C.residualGraph.edgeRestriction (C.quotientFiniteEdges T)).harmonicCharge_eq_inv_finiteClassSize_finiteHarmonicClassOf
      T hT (C.quotientFiniteWeightLower T) ⟨e, he⟩

theorem quotientTinyWeight_le (T : ℕ) (e : C.residualGraph.E)
    (he : e ∉ C.quotientFiniteEdges T) :
    C.residualGraph.weight e ≤ (1 : ℝ) / T := by
  simp only [quotientFiniteEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, not_le] at he
  exact he.le

end GeneralColoredPacketBase
end
end WeightedEdgeColoring.WeightedMultigraph
