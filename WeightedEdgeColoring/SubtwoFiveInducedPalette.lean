import WeightedEdgeColoring.SubtwoFivePhysicalPaletteDual
import WeightedEdgeColoring.SubtwoVertexRestrictionPalette

/-! The actual dense-five palette, now on precisely its five original
vertices, with no zero-budget labels for the rest of the graph. -/

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem rankTwoFive_induced_palette_attainable
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2) :
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
    (fun _ : (G.vertexRestriction S).E => (1 : ℝ) / n) ∈
      Subtwo.PaletteAttainable
        (Subtwo.reservedPaletteBudget (1999/1000 : ℝ)
          (fun v : (G.vertexRestriction S).V => G.subtwoExteriorHarmonicCharge S v.val / n))
        (G.vertexRestriction S).subtwoReservedColorPattern := by
  dsimp only
  let S : Finset G.V :=
    G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
  have hold := G.rankTwoFive_palette_attainable hn hlocal b hrank
  have h := G.vertexRestriction_paletteAttainable S (1999/1000 : ℝ)
    (G.subtwoFiveReservedCharge S n)
    (by intro v hv; simp [subtwoFiveReservedCharge, hv])
    (G.subtwoFiveInternalDemand S n) hold
  have hd : (fun e : (G.vertexRestriction S).E => G.subtwoFiveInternalDemand S n e.val) =
      (fun _ => (1 : ℝ) / n) := by
    funext e
    simp [subtwoFiveInternalDemand, e.property]
  have hq : (fun v : (G.vertexRestriction S).V => G.subtwoFiveReservedCharge S n v.val) =
      (fun v => G.subtwoExteriorHarmonicCharge S v.val / n) := by
    funext v
    simp [subtwoFiveReservedCharge, v.property]
  rw [hd, hq] at h
  exact h

end
end WeightedEdgeColoring.WeightedMultigraph
