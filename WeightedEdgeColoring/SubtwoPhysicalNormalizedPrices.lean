import WeightedEdgeColoring.SubtwoPhysicalPriceRows
import WeightedEdgeColoring.SubtwoBundlePriceCost

/-!
# Normalized cost and demand-price variables from a graph

These are the actual `t` and `c` coordinates in the certificate: minimum
bundle cost divided by the common bin bound, and physical demand price
divided by that bound and the maximum feasible-color price.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

def subtwoPhysicalBundleCost (n : ℕ) (a b : G.V) : ℝ :=
  (G.floorBundleCover (G.floorPairKey a b)).cost / n

def subtwoPhysicalBundlePrice (n : ℕ) (price : G.E → ℝ) (a b : G.V) : ℝ :=
  (∑ e ∈ G.floorBundle (G.floorPairKey a b), price e) / ((n : ℝ) * G.subtwoColorPriceMax price)

theorem subtwoPhysicalBundleCost_bounds {n : ℕ} (hn : 0 < n)
    (a b : G.V) (hab : a ≠ b) (hpack : G.PacksStarInto a n) :
    0 ≤ G.subtwoPhysicalBundleCost n a b ∧ G.subtwoPhysicalBundleCost n a b ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (G.floorBundleCover _).cost_nonneg hnR.le
  · exact (div_le_one hnR).2 (G.subtwo_floorBundleCover_cost_le a b hab hpack)

theorem subtwoPhysicalBundlePrice_nonneg {n : ℕ}
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hR : 0 < G.subtwoColorPriceMax price) (a b : G.V) :
    0 ≤ G.subtwoPhysicalBundlePrice n price a b :=
  div_nonneg (Finset.sum_nonneg fun e he => hp e) (mul_nonneg (Nat.cast_nonneg _) hR.le)

theorem subtwoPhysicalBundlePrice_le_cost_mul_price {n : ℕ}
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (a b : G.V) (hab : a ≠ b) :
    G.subtwoPhysicalBundlePrice n price a b ≤
      G.subtwoPhysicalBundleCost n a b * G.subtwoNormalizedSetPrice price {a, b} := by
  have h := div_le_div_of_nonneg_right (G.subtwo_floorBundle_price_le_cost_mul a b hab price)
    (mul_nonneg (show (0 : ℝ) ≤ n by positivity) hR.le)
  simpa only [subtwoPhysicalBundlePrice, subtwoPhysicalBundleCost, subtwoNormalizedSetPrice,
    div_mul_div_comm] using h

theorem subtwoPhysicalBundlePrice_as_bin_average
    (a b : G.V) (hab : a ≠ b) {n : ℕ} (bin : G.StarEdge a → Fin n) (price : G.E → ℝ) :
    G.subtwoPhysicalBundlePrice n price a b =
      ∑ j : Fin n, (1 / (n : ℝ)) *
        (G.subtwoStarProjectionPrice (G.floorBundle (G.floorPairKey a b)) bin j price /
          G.subtwoColorPriceMax price) := by
  have hinc : ∀ e ∈ G.floorBundle (G.floorPairKey a b), G.Inc a e := by
    intro e he
    rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab] at he
    exact G.inc_left_of_mem_exactDemandEdgesBetween he
  have hs := G.sum_subtwoStarProjectionPrice (G.floorBundle (G.floorPairKey a b)) bin price
  have hs' : (∑ j : Fin n, G.subtwoStarProjectionPrice (G.floorBundle (G.floorPairKey a b)) bin j price) =
      ∑ e ∈ G.floorBundle (G.floorPairKey a b), price e := by
    rw [hs]
    apply Finset.sum_congr rfl
    intro e he
    simp [hinc e he]
  unfold subtwoPhysicalBundlePrice
  rw [← hs', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem subtwoPhysicalBundlePrice_star_le_one
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price) :
    (∑ i : Fin 4, G.subtwoPhysicalBundlePrice n price v (neighbor i)) ≤ 1 := by
  simp_rw [G.subtwoPhysicalBundlePrice_as_bin_average v _ (hne _) bin price]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _j : Fin n, (1 / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.mul_sum]
      have h := G.subtwoPhysicalFourPrices_sum_le_one v neighbor hinj hne bin hbin price hR j Finset.univ
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h (show 0 ≤ (1 / (n : ℝ)) by positivity)
    _ = 1 := subtwo_uniform_bin_mass_sum hn

theorem subtwoPhysicalBundlePrice_le_one {n : ℕ} (hn : 0 < n)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (a b : G.V) (hab : a ≠ b) (hpack : G.PacksStarInto a n) :
    G.subtwoPhysicalBundlePrice n price a b ≤ 1 := by
  have ht := G.subtwoPhysicalBundleCost_bounds hn a b hab hpack
  have hm := G.subtwoNormalizedSetPrice_bounds price hp hR {a, b}
  calc
    _ ≤ G.subtwoPhysicalBundleCost n a b * G.subtwoNormalizedSetPrice price {a, b} :=
      G.subtwoPhysicalBundlePrice_le_cost_mul_price price hR a b hab
    _ ≤ 1 := by nlinarith

end
end WeightedEdgeColoring.WeightedMultigraph
