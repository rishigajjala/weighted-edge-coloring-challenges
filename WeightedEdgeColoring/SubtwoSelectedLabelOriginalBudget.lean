import WeightedEdgeColoring.SubtwoActualLabelBudget

/-! Turn the actual threshold law and decoder count into the physical endpoint budget. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem quotientThreshold_selectedLabels_originalBudget
    (block : G.V → Q) (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K n : ℕ} (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (T : ℕ) (hT : 160 ≤ T) (hn : 0 < n)
    (hlocal : G.LocallyPacksInto n) (hK : (K : ℝ) ≤ 4*n)
    (tau eta : ℝ) (htau : 0 ≤ tau)
    (x : C.residualGraph.E → Fin K → ℝ)
    (hmass : ∀ e, ∑ c, x e c ≤ 1)
    (qLaw : ∀ q : Q, Fin K → Finset (C.residualGraph.StarEdge q) → ℝ)
    (hlabel : ∀ q c l,
      subsetLabelMass (G.subtwoQuotientResidualEdgeLabel block hfiber C q) (qLaw q c) l ≤
      (∑ e : {e : C.residualGraph.StarEdge q // e.1 ∈ C.quotientFiniteEdges T},
        if G.subtwoQuotientResidualEdgeLabel block hfiber C q e.1 = l then
          x e.1.1 c / (finiteClassSize (C.quotientThresholdClass T (by omega) e.1.1) : ℝ)
        else 0) +
      (∑ e : {e : C.residualGraph.StarEdge q // e.1 ∉ C.quotientFiniteEdges T},
        if G.subtwoQuotientResidualEdgeLabel block hfiber C q e.1 = l then
          C.residualGraph.weight e.1.1 * x e.1.1 c else 0) /
            (1 - (1 : ℝ) / T) + (T + 1 : ℝ) * (100 / n))
    (selectedLabel : Q → Fin K → Option (Fin 6))
    (hselected : ∀ q label,
      ((Finset.univ.filter fun c : Fin K => selectedLabel q c = some label).card : ℝ) <
        (∑ c, subsetLabelMass (G.subtwoQuotientResidualEdgeLabel block hfiber C q)
          (qLaw q c) label) + K*tau + eta*(4*n)) :
    ∀ v : G.V,
      ((Finset.univ.filter fun c : Fin K => selectedLabel (block v) c =
        some (G.subtwoLocalSixLabel block hfiber (block v) v)).card : ℝ) ≤
      G.chargeOn harmonicCharge
        (G.subtwoCrossingSelectedEdges block Finset.univ \ F) v +
        (2*((1:ℝ)/T)+4*tau+4*eta)*n + 400*(T+1:ℝ) := by
  intro v
  have hs := G.sum_quotientThresholdLabelMass_le_original
    block hfiber C F hfull T hT hn (block v) v rfl hlocal
    (by simpa only [Fintype.card_fin] using hK)
    x (fun c => subsetLabelMass
      (G.subtwoQuotientResidualEdgeLabel block hfiber C (block v))
      (qLaw (block v) c) (G.subtwoLocalSixLabel block hfiber (block v) v)) hmass
    (fun c => hlabel (block v) c (G.subtwoLocalSixLabel block hfiber (block v) v))
  exact selectedLabelCount_le_originalResidualBudget htau hK hs
    (hselected (block v) (G.subtwoLocalSixLabel block hfiber (block v) v)).le

end
end WeightedEdgeColoring.WeightedMultigraph
