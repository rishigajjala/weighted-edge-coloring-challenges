import WeightedEdgeColoring.SubtwoBundleCharge

/-!
# Exact fractional triangle costs from the original star packings

The actual three minimum bundle covers cost at most twice the original
local bin bound. This is stronger than only bounding their integer floors.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_three_floorBundleCosts_le_two_mul
    (a b c : G.V) (n : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpackA : G.PacksStarInto a n)
    (hpackB : G.PacksStarInto b n)
    (hpackC : G.PacksStarInto c n) :
    (G.floorBundleCover (G.floorPairKey a b)).cost +
      (G.floorBundleCover (G.floorPairKey a c)).cost +
      (G.floorBundleCover (G.floorPairKey b c)).cost ≤ 2 * n := by
  classical
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
  obtain ⟨JA, hJA⟩ := BinPackingInstance.ExactDemandPatternCover.exists_cost_eq_of_packsInto hpairA
  obtain ⟨JB, hJB⟩ := BinPackingInstance.ExactDemandPatternCover.exists_cost_eq_of_packsInto hpairB
  obtain ⟨JC, hJC⟩ := BinPackingInstance.ExactDemandPatternCover.exists_cost_eq_of_packsInto hpairC
  exact BinPackingInstance.ExactDemandPatternCover.three_minimumExactCosts_le_two_mul_of_pairwiseCovers
    (G.edgeSetWeightDemand_pos FAB) (G.edgeSetWeightDemand_pos FAC) (G.edgeSetWeightDemand_pos FBC)
    (G.floorBundleCover (G.floorPairKey a b))
    (G.floorBundleCover (G.floorPairKey a c))
    (G.floorBundleCover (G.floorPairKey b c))
    (G.floorBundleCover_minimum _) (G.floorBundleCover_minimum _) (G.floorBundleCover_minimum _)
    JA JB JC hJA.le hJB.le hJC.le

end WeightedEdgeColoring.WeightedMultigraph
