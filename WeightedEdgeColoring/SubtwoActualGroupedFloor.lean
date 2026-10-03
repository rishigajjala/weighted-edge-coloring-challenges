import WeightedEdgeColoring.SubtwoActualObjectGrouping
import WeightedEdgeColoring.SubtwoIdentityTinyFloorTransfer

/-! The singleton adapter preserves the finite-menu one-tiny floor premise
for the actual globally grouped mixed-object graph. -/

set_option maxHeartbeats 4000000

namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {S : ℕ}
  (P : G.GeneralTinyThresholdPacketization ((1 : ℝ)/S)) (M : ℕ)

theorem coreGroupedPacketization_oneTinyFloor (hS : 0 < S) :
    WeightedMultigraph.FloorBundleAtMostOneTiny
      ((P.coreGroupedPacketization M).mixedObjectGraph) (2*M) S := by
  let H := P.coreGroupedGraph M
  have hmenu : ∀ k,
      Fintype.card (H.EdgeSetWeightType (H.floorBundle k)) ≤ (2*M)+1 :=
    P.coreGroupedGraph_card_bundle_weight_types_le M
  have h := H.identityTinyPacketization_floorBundleAtMostOneTiny
    ((1 : ℝ)/S) (by positivity) (P.coreGroupedGraph_below_endpoint_injective M)
    (2*M) S hS rfl hmenu
  exact h

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
