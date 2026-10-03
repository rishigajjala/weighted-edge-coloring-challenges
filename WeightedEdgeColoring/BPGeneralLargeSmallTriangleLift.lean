import WeightedEdgeColoring.BPGeneralLargeSmallPacketBaseLift
import WeightedEdgeColoring.BPGeneralFloorPacketTriangle

/-!
# Triangle accounting for approximate bundle packings

The three minimum exact-demand costs around a triangle sum to at most `2n`.
Therefore any packet construction using at most `(1 + delta)` times the
minimum cost on each endpoint pair has triangle density at most
`2(1 + delta)n`.  If `delta n <= d`, this is exactly the `2(n+d)` hypothesis
used by `exists_uniform_largeSmallGeneralColoredPacketBase`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance.ExactDemandPatternCover

noncomputable section

universe u v w

variable {A : BinPackingInstance.{u}} {B : BinPackingInstance.{v}}
  {Cinst : BinPackingInstance.{w}}
variable {firstDemand : A.Item → ℕ} {secondDemand : B.Item → ℕ}
  {thirdDemand : Cinst.Item → ℕ}

/-- Pairwise integral packings give the `2n` inequality directly for three
chosen minimum exact-demand costs. -/
theorem three_minimumExactCosts_le_two_mul_of_pairwisePacksInto
    (CA : A.ExactDemandPatternCover firstDemand)
    (CB : B.ExactDemandPatternCover secondDemand)
    (CC : Cinst.ExactDemandPatternCover thirdDemand)
    (hCA : CA.IsMinimumCost) (hCB : CB.IsMinimumCost)
    (hCC : CC.IsMinimumCost)
    (hfirstPos : ∀ a, 1 ≤ firstDemand a)
    (hsecondPos : ∀ b, 1 ≤ secondDemand b)
    (hthirdPos : ∀ c, 1 ≤ thirdDemand c)
    {n : ℕ}
    (hAB : PacksInto (B := A.sum B)
      (sumDemand firstDemand secondDemand) n)
    (hAC : PacksInto (B := A.sum Cinst)
      (sumDemand firstDemand thirdDemand) n)
    (hBC : PacksInto (B := B.sum Cinst)
      (sumDemand secondDemand thirdDemand) n) :
    CA.cost + CB.cost + CC.cost ≤ 2 * (n : ℝ) := by
  obtain ⟨Jab, hJab⟩ := exists_cost_eq_of_packsInto hAB
  obtain ⟨Jac, hJac⟩ := exists_cost_eq_of_packsInto hAC
  obtain ⟨Jbc, hJbc⟩ := exists_cost_eq_of_packsInto hBC
  exact three_minimumExactCosts_le_two_mul_of_pairwiseCovers
    hfirstPos hsecondPos hthirdPos CA CB CC hCA hCB hCC Jab Jac Jbc
      hJab.le hJac.le hJbc.le

end

end BinPackingInstance.ExactDemandPatternCover

namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- The three minimum exact-demand covers selected by the global floor
construction have total cost at most `2n` around every triangle. -/
theorem three_floorBundleCoverCosts_le_two_mul_of_packsStarsInto
    (a b c : G.V) (n : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpackA : G.PacksStarInto a n)
    (hpackB : G.PacksStarInto b n)
    (hpackC : G.PacksStarInto c n) :
    (G.floorBundleCover (G.floorPairKey a b)).cost +
      (G.floorBundleCover (G.floorPairKey a c)).cost +
      (G.floorBundleCover (G.floorPairKey b c)).cost ≤ 2 * (n : ℝ) := by
  let FAB := G.floorBundle (G.floorPairKey a b)
  let FAC := G.floorBundle (G.floorPairKey a c)
  let FBC := G.floorBundle (G.floorPairKey b c)
  have hFAB : FAB = G.exactDemandEdgesBetween Finset.univ a b :=
    G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab
  have hFAC : FAC = G.exactDemandEdgesBetween Finset.univ a c :=
    G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a c hac
  have hFBC : FBC = G.exactDemandEdgesBetween Finset.univ b c :=
    G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween b c hbc
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    G.exactDemandEdgesBetween_pairwise_disjoint Finset.univ hab hac hbc
  have hincABa : ∀ e ∈ FAB, G.Inc a e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween (hFAB ▸ he)
  have hincABb : ∀ e ∈ FAB, G.Inc b e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween (hFAB ▸ he)
  have hincACa : ∀ e ∈ FAC, G.Inc a e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween (hFAC ▸ he)
  have hincACc : ∀ e ∈ FAC, G.Inc c e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween (hFAC ▸ he)
  have hincBCb : ∀ e ∈ FBC, G.Inc b e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween (hFBC ▸ he)
  have hincBCc : ∀ e ∈ FBC, G.Inc c e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween (hFBC ▸ he)
  have hpairA :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto FAB FAC a
      (by simpa [hFAB, hFAC] using hABAC) hincABa hincACa hpackA
  have hpairB :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto FAB FBC b
      (by simpa [hFAB, hFBC] using hABBC) hincABb hincBCb hpackB
  have hpairC :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto FAC FBC c
      (by simpa [hFAC, hFBC] using hACBC) hincACc hincBCc hpackC
  exact
    BinPackingInstance.ExactDemandPatternCover.three_minimumExactCosts_le_two_mul_of_pairwisePacksInto
        (G.floorBundleCover (G.floorPairKey a b))
        (G.floorBundleCover (G.floorPairKey a c))
        (G.floorBundleCover (G.floorPairKey b c))
        (G.floorBundleCover_minimum (G.floorPairKey a b))
        (G.floorBundleCover_minimum (G.floorPairKey a c))
        (G.floorBundleCover_minimum (G.floorPairKey b c))
        (G.edgeSetWeightDemand_pos FAB)
        (G.edgeSetWeightDemand_pos FAC)
        (G.edgeSetWeightDemand_pos FBC)
        hpairA hpairB hpairC

namespace Packetization

variable {G} (P : G.Packetization)

/-- Pairwise packet-count domination by `(1 + delta)` times the selected
minimum bundle cost implies the corresponding scaled triangle bound. -/
theorem triangleEdgeCountAtMost_of_pairCount_le_scaled_floorBundleCost
    (selected : Finset P.Packet) (n : ℕ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hlocal : G.LocallyPacksInto n)
    (hpair : ∀ u v, u ≠ v →
      ((P.groupedGraph.edgesBetween selected u v).card : ℝ) ≤
        (1 + delta) * (G.floorBundleCover (G.floorPairKey u v)).cost) :
    P.groupedGraph.TriangleEdgeCountAtMost selected
      (2 * (1 + delta) * (n : ℝ)) := by
  intro T hT
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT
  rw [P.groupedGraph.card_internalEdges_triple selected hab hac hbc]
  push_cast
  calc
    ((P.groupedGraph.edgesBetween selected a b).card : ℝ) +
        (P.groupedGraph.edgesBetween selected a c).card +
        (P.groupedGraph.edgesBetween selected b c).card ≤
      (1 + delta) * (G.floorBundleCover (G.floorPairKey a b)).cost +
        (1 + delta) * (G.floorBundleCover (G.floorPairKey a c)).cost +
        (1 + delta) * (G.floorBundleCover (G.floorPairKey b c)).cost := by
      gcongr
      · exact hpair a b hab
      · exact hpair a c hac
      · exact hpair b c hbc
    _ = (1 + delta) *
        ((G.floorBundleCover (G.floorPairKey a b)).cost +
          (G.floorBundleCover (G.floorPairKey a c)).cost +
          (G.floorBundleCover (G.floorPairKey b c)).cost) := by ring
    _ ≤ (1 + delta) * (2 * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (G.three_floorBundleCoverCosts_le_two_mul_of_packsStarsInto
          a b c n hab hac hbc (hlocal a) (hlocal b) (hlocal c))
        (by linarith)
    _ = 2 * (1 + delta) * (n : ℝ) := by ring

/-- Natural additive slack `d` absorbs the scaled triangle loss whenever
`delta n <= d`. -/
theorem triangleEdgeCountAtMost_additive_of_pairCount_le_scaled_floorBundleCost
    (selected : Finset P.Packet) (n d : ℕ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hdeltaN : delta * (n : ℝ) ≤ d)
    (hlocal : G.LocallyPacksInto n)
    (hpair : ∀ u v, u ≠ v →
      ((P.groupedGraph.edgesBetween selected u v).card : ℝ) ≤
        (1 + delta) * (G.floorBundleCover (G.floorPairKey u v)).cost) :
    P.groupedGraph.TriangleEdgeCountAtMost selected
      (2 * ((n + d : ℕ) : ℝ)) := by
  have hscaled := P.triangleEdgeCountAtMost_of_pairCount_le_scaled_floorBundleCost
    selected n delta hdelta hlocal hpair
  exact fun T hT ↦ (hscaled T hT).trans (by
    push_cast
    nlinarith)

end Packetization

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.BinPackingInstance.ExactDemandPatternCover.three_minimumExactCosts_le_two_mul_of_pairwisePacksInto
#print axioms WeightedEdgeColoring.WeightedMultigraph.three_floorBundleCoverCosts_le_two_mul_of_packsStarsInto
#print axioms WeightedEdgeColoring.WeightedMultigraph.Packetization.triangleEdgeCountAtMost_additive_of_pairCount_le_scaled_floorBundleCost
