import WeightedEdgeColoring.SubtwoThreePhysicalCostDomain

/-! The actual triangle bundle prices satisfy the three reserved-palette rows. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph.SubtwoThreePhysicalData

universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoThreePhysicalData n)

private theorem vertex_not_opposite (i : Fin 3) :
    D.vertex i ∉ ({D.first i, D.second i} : Finset G.V) := by
  have heq (a b : Fin 3) : D.vertex a = D.vertex b ↔ a = b :=
    D.vertex_injective.eq_iff
  fin_cases i <;> simp [first, second, oppositePair, heq]

theorem oppositePrice_le_avoiding (i : Fin 3) :
    G.subtwoNormalizedSetPrice D.price {D.first i, D.second i} ≤
      D.avoidingPrice i := by
  have hs := G.subtwoNormalizedSetPrice_disjoint_avoiding D.price
    D.price_max_pos {D.first i, D.second i} ∅ (by simp)
    (D.vertex i) (D.vertex_not_opposite i) (by simp)
  have hz : 0 ≤ G.subtwoNormalizedSetPrice D.price ∅ :=
    (G.subtwoNormalizedSetPrice_bounds D.price D.price_nonneg
      D.price_max_pos ∅).1
  unfold avoidingPrice
  linarith

theorem bundlePrice_le_cost_mul_avoiding (i : Fin 3) :
    D.bundlePrice i ≤ D.bundleCost i * D.avoidingPrice i := by
  have hprice := G.subtwoPhysicalBundlePrice_le_cost_mul_price (n := n)
    D.price D.price_max_pos (D.first i) (D.second i)
    (D.first_ne_second i)
  have hcost : 0 ≤ D.bundleCost i := by
    unfold bundleCost subtwoPhysicalBundleCost
    exact div_nonneg (G.floorBundleCover _).cost_nonneg
      (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left (D.oppositePrice_le_avoiding i) hcost
  change D.bundlePrice i ≤ D.bundleCost i *
    G.subtwoNormalizedSetPrice D.price {D.first i, D.second i} at hprice
  linarith

theorem physical_reserved_price_bound (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 1)
    (hset : D.vertexSet =
      G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b) :
    (∑ i : Fin 3, D.bundlePrice i) +
      (∑ i : Fin 3, D.exteriorCharge i * (1 - D.avoidingPrice i)) <
      (1999/1000:ℝ) := by
  exact WeightedEdgeColoring.Subtwo.triangle_reserved_price_lt_kappa
    D.bundleCost D.exteriorCharge D.avoidingPrice D.bundlePrice
    (D.bundleCost_le_one hlocal)
    (fun i => (G.subtwoNormalizedAvoidingPrice_bounds D.price
      D.price_nonneg D.price_max_pos (D.vertex i)).2)
    (D.incident_budget hlocal)
    (D.bundleCost_sum_ge_kappa hlocal b hrank hset)
    (D.bundleCost_sum_le_two hlocal)
    (D.bundlePrice_sum_le_three_halves hlocal)
    (D.bundlePrice_le_cost_mul_avoiding)

end WeightedEdgeColoring.WeightedMultigraph.SubtwoThreePhysicalData
