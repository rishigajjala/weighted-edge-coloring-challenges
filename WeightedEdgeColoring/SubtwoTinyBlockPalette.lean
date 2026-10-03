import WeightedEdgeColoring.SubtwoTinyBlockDeletion
import WeightedEdgeColoring.SubtwoPaletteDeleteEdges
import WeightedEdgeColoring.SubtwoThreeInducedPalette
import WeightedEdgeColoring.SubtwoFiveInducedPalette

/-! Delete the endpoint-simple tiny objects *after* choosing the dense
block. The reserved palette keeps its original selected block and its
original exterior reservation; deleted coordinates have zero demand. -/

namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

theorem smallObject_not_core {o : P.Object} (ho : o ∈ P.smallObjects) :
    o ∉ P.coreObjects := by
  simp [coreObjects, ho]

def coreInternalDemand (S : Finset G.V) (n : ℕ) (o : P.Object) : ℝ :=
  if o ∈ P.coreObjects then
    P.mixedObjectGraph.subtwoFiveInternalDemand S n o else 0

theorem coreInternalDemand_zero_of_small (S : Finset G.V) (n : ℕ)
    {o : P.Object} (ho : o ∈ P.smallObjects) :
    P.coreInternalDemand S n o = 0 := by
  simp [coreInternalDemand, P.smallObject_not_core ho]

theorem coreInternalDemand_eq_of_core (S : Finset G.V) (n : ℕ)
    {o : P.Object} (ho : o ∈ P.coreObjects) :
    P.coreInternalDemand S n o =
      P.mixedObjectGraph.subtwoFiveInternalDemand S n o := by
  simp [coreInternalDemand, ho]

theorem rankOneThree_core_palette_attainable
    {n : ℕ} (hn : 0 < n) (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (hrank : P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 1) :
    let H := P.mixedObjectGraph
    let S := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
    (fun o : H.E => if o ∈ P.coreObjects then H.subtwoFiveInternalDemand S n o else 0) ∈
      WeightedEdgeColoring.Subtwo.PaletteAttainable
        (WeightedEdgeColoring.Subtwo.reservedPaletteBudget (1999/1000:ℝ)
          (H.subtwoFiveReservedCharge S n)) H.subtwoReservedColorPattern := by
  dsimp only
  exact P.mixedObjectGraph.paletteAttainable_keepEdges P.coreObjects _ _
    (P.mixedObjectGraph.rankOneThree_palette_attainable hn hlocal b hrank)

theorem rankTwoFive_core_palette_attainable
    {n : ℕ} (hn : 0 < n) (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (hrank : P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 2) :
    let H := P.mixedObjectGraph
    let S := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
    (fun o : H.E => if o ∈ P.coreObjects then H.subtwoFiveInternalDemand S n o else 0) ∈
      WeightedEdgeColoring.Subtwo.PaletteAttainable
        (WeightedEdgeColoring.Subtwo.reservedPaletteBudget (1999/1000:ℝ)
          (H.subtwoFiveReservedCharge S n)) H.subtwoReservedColorPattern := by
  dsimp only
  exact P.mixedObjectGraph.paletteAttainable_keepEdges P.coreObjects _ _
    (P.mixedObjectGraph.rankTwoFive_palette_attainable hn hlocal b hrank)

theorem rankOneThree_retained_induced_palette_attainable
    {n : ℕ} (hn : 0 < n) (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (hrank : P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 1) :
    let H := P.mixedObjectGraph
    let S := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
    let R : Finset (H.vertexRestriction S).E :=
      Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
    (fun _ : ((H.vertexRestriction S).edgeRestriction R).E => (1:ℝ)/n) ∈
      WeightedEdgeColoring.Subtwo.PaletteAttainable
        (WeightedEdgeColoring.Subtwo.reservedPaletteBudget (1999/1000:ℝ)
          (fun v : (H.vertexRestriction S).V =>
            H.subtwoExteriorHarmonicCharge S v.val / n))
        ((H.vertexRestriction S).edgeRestriction R).subtwoReservedColorPattern := by
  dsimp only
  let H := P.mixedObjectGraph
  let S := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction S).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  have h := H.rankOneThree_induced_palette_attainable hn hlocal b hrank
  exact (H.vertexRestriction S).edgeRestriction_paletteAttainable R _ _ h

theorem rankTwoFive_retained_induced_palette_attainable
    {n : ℕ} (hn : 0 < n) (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (hrank : P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 2) :
    let H := P.mixedObjectGraph
    let S := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
    let R : Finset (H.vertexRestriction S).E :=
      Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
    (fun _ : ((H.vertexRestriction S).edgeRestriction R).E => (1:ℝ)/n) ∈
      WeightedEdgeColoring.Subtwo.PaletteAttainable
        (WeightedEdgeColoring.Subtwo.reservedPaletteBudget (1999/1000:ℝ)
          (fun v : (H.vertexRestriction S).V =>
            H.subtwoExteriorHarmonicCharge S v.val / n))
        ((H.vertexRestriction S).edgeRestriction R).subtwoReservedColorPattern := by
  dsimp only
  let H := P.mixedObjectGraph
  let S := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction S).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  have h := H.rankTwoFive_induced_palette_attainable hn hlocal b hrank
  exact (H.vertexRestriction S).edgeRestriction_paletteAttainable R _ _ h

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
