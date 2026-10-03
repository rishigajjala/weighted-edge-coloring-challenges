import WeightedEdgeColoring.SubtwoPhysicalPricedPotential
import WeightedEdgeColoring.SubtwoPhysicalNormalizedPrices
import WeightedEdgeColoring.SubtwoNormalPriceRank

/-!
# Full-star price rows from actual bins

The normal and heavy contributions use the same original star packing.
The identity between bin-price averages and physical demand prices makes
the resulting inequalities apply to the actual certificate coordinates.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

theorem sum_subtwoHeavyBigPrice_eq
    (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) :
    (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyBigPrice v neighbor bin price i k) =
      ∑ j : Fin n, if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) then
        (1 / (n : ℝ)) * (G.subtwoOrderedFourPrices v neighbor bin price j 0 +
          G.subtwoOrderedFourPrices v neighbor bin price j 1) else 0 :=
  G.sum_subtwoHeavyClassBin v neighbor bin _

theorem sum_subtwoPhysicalBundlePrice_as_bin_average
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) :
    (∑ i : Fin 4, G.subtwoPhysicalBundlePrice n price v (neighbor i)) =
      ∑ j : Fin n, (1 / (n : ℝ)) * ∑ i : Fin 4,
        G.subtwoPhysicalFourPrices v neighbor bin price j i := by
  simp_rw [G.subtwoPhysicalBundlePrice_as_bin_average v _ (hne _) bin price]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  rfl

theorem subtwo_normal_physical_price_le_half_sum
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (j : Fin n) (hnormal : ¬∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) :
    (∑ i : Fin 4, G.subtwoPhysicalFourPrices v neighbor bin price j i) ≤
      (1 / 2 : ℝ) * ∑ i : Fin 4, G.subtwoNormalizedSetPrice price {v, neighbor i} := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hw := SubtwoHarmonicRanks.charge_le_inv (r := 2) (by decide)
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin j i)
    (show G.subtwoPhysicalFourLoads v neighbor bin j i ≤ 1 / 2 from
      le_of_not_gt (fun h => hnormal ⟨i, h⟩))
  have h := (G.subtwoPhysicalFourPrices_le_harmonic v neighbor hne bin hbin price hR j i).trans
    (mul_le_mul_of_nonneg_left hw (G.subtwoNormalizedSetPrice_bounds price hp hR _).1)
  simpa only [Nat.cast_ofNat, mul_comm] using h

theorem subtwo_normal_physical_price_le_sorted_upper
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (π : Equiv.Perm (Fin 4)) (U : Fin 4 → ℝ)
    (hU : ∀ i, G.subtwoNormalizedSetPrice price {v, neighbor (π i)} ≤ U i)
    (h01 : U 1 ≤ U 0) (h12 : U 2 ≤ U 1) (h23 : U 3 ≤ U 2) (h3 : 0 ≤ U 3)
    (j : Fin n) (hnormal : ¬∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) :
    (∑ i : Fin 4, G.subtwoPhysicalFourPrices v neighbor bin price j i) ≤
      min 1 (U 0 / 2 + U 1 / 2 + U 2 / 3 + U 3 / 12) := by
  apply le_min
  · exact G.subtwoPhysicalFourPrices_sum_le_one v neighbor hinj hne bin hbin price hR j Finset.univ
  · rw [← Equiv.sum_comp π (G.subtwoPhysicalFourPrices v neighbor bin price j)]
    apply SubtwoHarmonicRanks.normal_sorted_price_bound
      (fun i => G.subtwoPhysicalFourLoads v neighbor bin j (π i)) U
      (fun i => G.subtwoPhysicalFourPrices v neighbor bin price j (π i))
      (fun i => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j (π i))
      (fun i => le_of_not_gt (fun h => hnormal ⟨π i, h⟩))
      (by rw [Equiv.sum_comp]; exact G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j)
      h01 h12 h23 h3
    intro i
    exact (G.subtwoPhysicalFourPrices_le_harmonic v neighbor hne bin hbin price hR j (π i)).trans
      (mul_le_mul_of_nonneg_right (hU i) (harmonicCharge_nonneg _))

/-- Average the normal cap and the actual heavy contributions. No class
variables or price-coverage equalities are assumed. -/
theorem subtwo_physical_star_price_row_of_normal_cap
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (nc : ℝ)
    (hnormal : ∀ j, (¬∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) →
      (∑ i : Fin 4, G.subtwoPhysicalFourPrices v neighbor bin price j i) ≤ nc) :
    (∑ i : Fin 4, G.subtwoPhysicalBundlePrice n price v (neighbor i)) ≤
      nc * (1 - ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyBigPrice v neighbor bin price i k) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavySmallPrice v neighbor bin price i k) := by
  have hpoint (j : Fin n) :
      (1 / (n : ℝ)) * (∑ i : Fin 4, G.subtwoPhysicalFourPrices v neighbor bin price j i) ≤
      nc * (1 / (n : ℝ)) - nc *
        (if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) then (1 / (n : ℝ)) else 0) +
      (if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) then
        (1 / (n : ℝ)) * (G.subtwoOrderedFourPrices v neighbor bin price j 0 +
          G.subtwoOrderedFourPrices v neighbor bin price j 1) else 0) +
      (if (∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a) then
        (1 / (n : ℝ)) * (G.subtwoOrderedFourPrices v neighbor bin price j 2 +
          G.subtwoOrderedFourPrices v neighbor bin price j 3) else 0) := by
    by_cases hh : ∃ a, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j a
    · simp only [hh, if_true, sub_self, zero_add]
      rw [← G.subtwoOrderedFourPrices_sum]
      simp only [Fin.sum_univ_succ]
      ring_nf
      rfl
    · simp only [hh, if_false, mul_zero, sub_zero, add_zero]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hnormal j hh)
        (show 0 ≤ (1 / (n : ℝ)) by positivity)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j hj => hpoint j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  simp only [← Finset.mul_sum, subtwo_uniform_bin_mass_sum hn, mul_one] at h
  rw [G.sum_subtwoPhysicalBundlePrice_as_bin_average v neighbor hne bin price,
    G.sum_subtwoHeavyClassMass, G.sum_subtwoHeavyBigPrice_eq, G.sum_subtwoHeavySmallPrice_eq]
  rw [← Finset.mul_sum]
  nlinarith

theorem subtwo_physical_star_half_price_row
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price) :
    (∑ i : Fin 4, G.subtwoPhysicalBundlePrice n price v (neighbor i)) ≤
      ((1 / 2 : ℝ) * ∑ i : Fin 4, G.subtwoNormalizedSetPrice price {v, neighbor i}) *
        (1 - ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyBigPrice v neighbor bin price i k) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavySmallPrice v neighbor bin price i k) := by
  apply G.subtwo_physical_star_price_row_of_normal_cap v neighbor hne hn bin price
  exact G.subtwo_normal_physical_price_le_half_sum v neighbor hne bin hbin price hp hR


/-- The sharper normal-bin cap can use any ordered set of upper bounds
on the actual pair prices. The heavy prices still use the original bins. -/
theorem subtwo_physical_star_sorted_price_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (π : Equiv.Perm (Fin 4)) (U : Fin 4 → ℝ)
    (hU : ∀ i, G.subtwoNormalizedSetPrice price {v, neighbor (π i)} ≤ U i)
    (h01 : U 1 ≤ U 0) (h12 : U 2 ≤ U 1) (h23 : U 3 ≤ U 2) (h3 : 0 ≤ U 3) :
    (∑ i : Fin 4, G.subtwoPhysicalBundlePrice n price v (neighbor i)) ≤
      min 1 (U 0 / 2 + U 1 / 2 + U 2 / 3 + U 3 / 12) *
        (1 - ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyBigPrice v neighbor bin price i k) +
      (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavySmallPrice v neighbor bin price i k) := by
  apply G.subtwo_physical_star_price_row_of_normal_cap v neighbor hne hn bin price
  exact G.subtwo_normal_physical_price_le_sorted_upper v neighbor hinj hne bin hbin
    price hR π U hU h01 h12 h23 h3

end
end WeightedEdgeColoring.WeightedMultigraph
