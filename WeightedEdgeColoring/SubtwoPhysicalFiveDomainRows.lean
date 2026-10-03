import WeightedEdgeColoring.SubtwoPhysicalFiveCostKeys

/-!
# Density, star budgets, and triangle rows for an actual five-block

These rows use the original graph's star packings and the density of its
constructed block. No numerical domain inequality is postulated.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}
namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem indexed_star_budget (hlocal : G.LocallyPacksInto n) (v : Fin 5) :
    (∑ a : Fin 4, D.bundleCost (subtwoFivePairIndex v (v.succAbove a))) +
      D.exteriorCharge v ≤ subtwoM := by
  have hn : (0 : ℝ) < n := by exact_mod_cast D.n_pos
  have hs := D.incident_bundleCost_sum_le_fractional_incident v
  have hm := G.subtwo_exterior_add_fractionalIncident_le hlocal D.vertexSet (D.vertex v)
  have hmul := (le_div_iff₀ hn).mp hs
  have hext : D.exteriorCharge v * n = G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex v) := by
    exact div_mul_cancel₀ _ hn.ne'
  nlinarith

theorem indexed_triangle_cost_row (a b c : Fin 5)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    D.bundleCost (subtwoFivePairIndex a b) +
      D.bundleCost (subtwoFivePairIndex a c) +
      D.bundleCost (subtwoFivePairIndex b c) ≤ 2 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast D.n_pos
  rw [D.bundleCost_pairIndex a b hab, D.bundleCost_pairIndex a c hac,
    D.bundleCost_pairIndex b c hbc]
  unfold subtwoPhysicalBundleCost
  rw [← add_div, ← add_div]
  apply (div_le_iff₀ hn).mpr
  exact G.subtwo_three_floorBundleCosts_le_two_mul _ _ _ n
    (fun h => hab (D.vertex_injective h))
    (fun h => hac (D.vertex_injective h))
    (fun h => hbc (D.vertex_injective h))
    ⟨D.bin a, D.bin_load a⟩ ⟨D.bin b, D.bin_load b⟩ ⟨D.bin c, D.bin_load c⟩

theorem indexed_density_row_of_rank_two_block
    (hlocal : G.LocallyPacksInto n) (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (hset : D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q) :
    2 * subtwoKappa ≤ ∑ e : Fin 10, D.bundleCost e := by
  have hn : (0 : ℝ) < n := by exact_mod_cast D.n_pos
  rw [D.bundleCost_sum_eq_fractional_internal, hset]
  apply (le_div_iff₀ hn).mpr
  have h := G.subtwoFloorBlock_fractional_paid D.n_pos hlocal q
  rw [hrank] at h
  simpa only [Nat.cast_ofNat] using h

theorem indexed_bundle_price_cost_row (e : Fin 10) :
    D.demandPrice e ≤ D.pairPrice e * D.bundleCost e := by
  have h := G.subtwoPhysicalBundlePrice_le_cost_mul_price (n := n) D.price D.price_max_pos
    (D.vertex (subtwoFivePair e).1) (D.vertex (subtwoFivePair e).2)
    (fun he => subtwoFivePair_ne e (D.vertex_injective he))
  simpa only [demandPrice, pairPrice, bundleCost, mul_comm] using h

theorem indexed_star_price_le_one (v : Fin 5) :
    (∑ a : Fin 4, D.demandPrice (subtwoFivePairIndex v (v.succAbove a))) ≤ 1 := by
  simp only [D.demandPrice_incident]
  exact G.subtwoPhysicalBundlePrice_star_le_one _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) D.n_pos (D.bin v) (D.bin_load v) D.price D.price_max_pos

theorem indexed_singleton_cost_upper (v : Fin 5) (a : Fin 4) :
    D.bundleCost (subtwoFivePairIndex v (v.succAbove a)) +
      (∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j) *
        (if i = a then (-1 / 2 : ℝ) else if i.succAbove j = a then 0 else 1 / 4)) ≤ 1 / 2 := by
  rw [D.weighted_heavyMass_classIndex v
    (fun i k => if i = a then (-1 / 2 : ℝ) else if k = a then 0 else 1 / 4),
    D.bundleCost_incident]
  exact G.subtwo_physical_singleton_cost_upper _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) D.n_pos (D.bin v) (D.bin_load v) a

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
