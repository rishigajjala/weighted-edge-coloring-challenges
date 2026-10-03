import WeightedEdgeColoring.SubtwoPhysicalHeavyAverages

/-!
# The priced boundary-potential row for actual graph observables

The small-price contribution is paid by the harmonic charges of the two
smaller projections. The existing physical boundary inequality then proves
the exact priced row used in the archived certificate.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

theorem sum_subtwoHeavySmallPrice_eq
    (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) :
    (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavySmallPrice v neighbor bin price i k) =
      ∑ j : Fin n, if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) then
        (1 / (n : ℝ)) * (G.subtwoOrderedFourPrices v neighbor bin price j 2 +
          G.subtwoOrderedFourPrices v neighbor bin price j 3) else 0 :=
  G.sum_subtwoHeavyClassBin v neighbor bin _

theorem subtwo_ordered_small_price_le_charge
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (sm : ℝ) (hsm : ∀ a, G.subtwoNormalizedSetPrice price {v, neighbor a} ≤ sm) (j : Fin n) :
    G.subtwoOrderedFourPrices v neighbor bin price j 2 +
      G.subtwoOrderedFourPrices v neighbor bin price j 3 ≤
      sm * (harmonicCharge (G.subtwoOrderedFourLoads v neighbor bin j 2) +
        harmonicCharge (G.subtwoOrderedFourLoads v neighbor bin j 3)) := by
  let π := SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j)
  have h (i : Fin 4) : G.subtwoOrderedFourPrices v neighbor bin price j i ≤
      sm * harmonicCharge (G.subtwoOrderedFourLoads v neighbor bin j i) := by
    exact (G.subtwoPhysicalFourPrices_le_harmonic v neighbor hne bin hbin price hR j (π i)).trans
      (mul_le_mul_of_nonneg_right (hsm (π i)) (harmonicCharge_nonneg _))
  linarith [h 2, h 3]

theorem sum_subtwoHeavySmallPrice_le_charge
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (sm : ℝ) (hsm : ∀ a, G.subtwoNormalizedSetPrice price {v, neighbor a} ≤ sm) :
    (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavySmallPrice v neighbor bin price i k) ≤
      sm * ∑ j : Fin n, if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) then
        (1 / (n : ℝ)) * (harmonicCharge (G.subtwoOrderedFourLoads v neighbor bin j 2) +
          harmonicCharge (G.subtwoOrderedFourLoads v neighbor bin j 3)) else 0 := by
  rw [G.sum_subtwoHeavySmallPrice_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · have h := mul_le_mul_of_nonneg_left
      (G.subtwo_ordered_small_price_le_charge v neighbor hne bin hbin price hR sm hsm j)
      (show 0 ≤ (1 / (n : ℝ)) by positivity)
    nlinarith
  · simp

/-- The potential row with actual big/small profile variables, actual
minimum bundle costs, and the block's exterior harmonic charge. -/
theorem subtwo_physical_priced_boundary_row
    (S : Finset G.V) (v : G.V) (hv : v ∈ S)
    (neighbor : Fin 4 → G.V) (hinj : Function.Injective neighbor)
    (hne : ∀ i, v ≠ neighbor i) (hmem : ∀ i, neighbor i ∈ S)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (sm : ℝ) (hsm0 : 0 ≤ sm)
    (hsm : ∀ a, G.subtwoNormalizedSetPrice price {v, neighbor a} ≤ sm) :
    (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavySmallPrice v neighbor bin price i k) +
      (3 / 2 : ℝ) * sm * (∑ i : Fin 4, (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n) +
      (2 / 3 : ℝ) * sm * (G.subtwoExteriorHarmonicCharge S v / n) -
      (893 / 1430 : ℝ) * sm * (∑ i : Fin 4, ∑ k : Fin 4,
        G.subtwoHeavyClassMass v neighbor bin i k) ≤ (111 / 52 : ℝ) * sm := by
  have hp := G.subtwo_exterior_boundary_potential S v hv neighbor hinj hne hmem hn bin hbin
  dsimp only at hp
  have h := mul_le_mul_of_nonneg_left hp hsm0
  have hs := G.sum_subtwoHeavySmallPrice_le_charge v neighbor hne bin hbin price hR sm hsm
  rw [G.sum_subtwoHeavyClassMass]
  nlinarith

end
end WeightedEdgeColoring.WeightedMultigraph
