import WeightedEdgeColoring.SubtwoPhysicalHeavyAverages
import WeightedEdgeColoring.SubtwoPhysicalAvoidingPriceRows

/-!
# Bounds on actual certificate observables

The integer certificate checker pays its signed residuals using finite
coordinate bounds. Here the heavy prices and all true product coordinates
are bounded by one using the same physical packings as the other rows.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoHeavyClassMass_le_one
    (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ} (hn : 0 < n)
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) :
    G.subtwoHeavyClassMass v neighbor bin i k ≤ 1 := by
  calc
    _ ≤ ∑ _j : Fin n, (1 / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · rfl
      · positivity
    _ = 1 := subtwo_uniform_bin_mass_sum hn

theorem subtwoHeavyBigSmallPrice_bounds
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (i k : Fin 4) :
    (0 ≤ G.subtwoHeavyBigPrice v neighbor bin price i k ∧
      G.subtwoHeavyBigPrice v neighbor bin price i k ≤ 1) ∧
    (0 ≤ G.subtwoHeavySmallPrice v neighbor bin price i k ∧
      G.subtwoHeavySmallPrice v neighbor bin price i k ≤ 1) := by
  obtain ⟨hb, hs⟩ := G.subtwoHeavyBigSmallPrice_nonneg v neighbor bin price hp hR i k
  have ha := G.subtwoHeavyBigSmallPrice_add_le_mass v neighbor hinj hne bin hbin price hp hR i k
  have hm := G.subtwoHeavyClassMass_le_one v neighbor hn bin i k
  exact ⟨⟨hb, by linarith⟩, ⟨hs, by linarith⟩⟩

/-- Every lift of an actual unit-bounded observable has the same unit bound. -/
theorem subtwoPhysicalPriceProduct_bounds
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (S : Finset G.V) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ G.subtwoNormalizedSetPrice price S * y ∧
      G.subtwoNormalizedSetPrice price S * y ≤ 1 := by
  obtain ⟨hm0, hm1⟩ := G.subtwoNormalizedSetPrice_bounds price hp hR S
  exact ⟨mul_nonneg hm0 hy0,
    (mul_le_mul_of_nonneg_right hm1 hy0).trans (by simpa using hy1)⟩

/-- Exterior loss in a rank-two block obeys the checker cap, using the
actual boundary charge of that block. -/
theorem subtwoFloorFive_avoiding_loss_bounds
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (v : G.V)
    (hv : v ∈ G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price) :
    let Qv := G.subtwoExteriorHarmonicCharge
      (G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q) v / n
    0 ≤ G.subtwoAvoidingPriceLoss Qv price v ∧
      G.subtwoAvoidingPriceLoss Qv price v ≤ (459155 / 1000000 : ℝ) := by
  dsimp only
  obtain ⟨hq0, hq1⟩ := G.subtwoFloorFive_exterior_normalized_bounds hn hlocal q hrank v hv
  obtain ⟨hb0, hb1⟩ := G.subtwoAvoidingPriceLoss_bounds _ hq0 price hp hR v
  exact ⟨hb0, hb1.trans hq1⟩

end
end WeightedEdgeColoring.WeightedMultigraph
