import WeightedEdgeColoring.SubtwoK6PhysicalPriceTransfer
import WeightedEdgeColoring.SubtwoVertexRestrictionPatterns
import WeightedEdgeColoring.SubtwoFiveVertexLocalBound
import WeightedEdgeColoring.SubtwoPhysicalFiveObjective

/-! Apply the universal five-vertex local theorem to the actual induced
five-block, retaining every original parallel edge type. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoFivePhysicalData n)

theorem vertexSet_card : D.vertexSet.card = 5 := by
  classical
  simp [SubtwoFivePhysicalData.vertexSet, Finset.card_image_of_injective,
    D.vertex_injective]

theorem physical_local_five_bound (hlocal : G.LocallyPacksInto n) :
    (∑ e : Fin 10, D.demandPrice e) ≤ (157/80:ℝ) := by
  let H := G.vertexRestriction D.vertexSet
  let priceH : H.E → ℝ := fun e => D.price e.1
  have hcard : Fintype.card H.V ≤ 5 := by
    change Fintype.card (G.vertexRestriction D.vertexSet).V ≤ 5
    rw [G.vertexRestriction_card D.vertexSet, D.vertexSet_card]
  have hlocalH : H.LocallyPacksInto n :=
    G.vertexRestriction_locallyPacksInto D.vertexSet hlocal
  let B := H.localPackingFractionalBins D.n_pos hlocalH
  have hpriceH : ∀ e : H.E, 0 ≤ priceH e := fun e => D.price_nonneg e.1
  have hbound := WeightedEdgeColoring.Subtwo.FiveVertexLocalBound.local_bound_price
    H hcard (fun _ : H.E => 1 / (n : ℝ)) priceH B hpriceH
    (H.localPackingFractionalBins_total D.n_pos hlocalH)
  have hmax := G.vertexRestriction_colorPriceMax_le D.vertexSet D.price
  have hn : (0:ℝ) < n := by exact_mod_cast D.n_pos
  have hR := D.price_max_pos
  have hsum : (∑ e : H.E, priceH e * (1 / (n : ℝ))) =
      G.subtwoInternalCost D.price D.vertexSet / n := by
    calc
      _ = (∑ e : H.E, D.price e.1) / n := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro e _
        simp [priceH]
        ring
      _ = _ := by
        rw [G.vertexRestriction_sum D.vertexSet D.price]
  rw [hsum] at hbound
  rw [D.demandPrice_sum_eq_internal_price]
  have hproduct : G.subtwoInternalCost D.price D.vertexSet ≤
      (157/80:ℝ) * G.subtwoColorPriceMax D.price * n := by
    have hdiv := (div_le_iff₀ hn).mp hbound
    nlinarith [hmax]
  exact (div_le_iff₀ (mul_pos hn hR)).mpr (by nlinarith [hproduct])

theorem physical_reserved_price_bound
    (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2)
    (hset : D.vertexSet =
      G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b) :
    (∑ e : Fin 10, D.demandPrice e) +
      (∑ v : Fin 5, D.avoidingLoss v) < (1999/1000:ℝ) := by
  exact D.physical_reserved_price_transfer_of_local_bound hlocal b hrank hset
    (D.physical_local_five_bound hlocal)

end WeightedEdgeColoring.WeightedMultigraph.SubtwoFivePhysicalData
