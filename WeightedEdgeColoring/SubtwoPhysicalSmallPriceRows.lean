import WeightedEdgeColoring.SubtwoPhysicalHeavyAverages

/-!
# Complementary-pair and small-price rows for actual heavy classes

The two indices outside a heavy class are a fixed unordered pair. Their
order may change between bins, but the maximum price of that pair and the
sum of its two incident price caps do not change.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem four_perm_remaining_pair (π : Equiv.Perm (Fin 4)) :
    ((Finset.univ.erase (π 0)).erase (π 1) : Finset (Fin 4)) = {π 2, π 3} := by
  classical
  ext i
  obtain ⟨a, rfl⟩ := π.surjective i
  fin_cases a <;> simp [π.injective.eq_iff]

end WeightedEdgeColoring.SubtwoHarmonicRanks

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

def subtwoOtherTwoIndices (i k : Fin 4) : Finset (Fin 4) :=
  (Finset.univ.erase i).erase k

theorem subtwoOtherTwoIndices_eq_of_class
    (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (j : Fin n)
    (hj : G.SubtwoHeavyClassBin v neighbor bin i k j) :
    subtwoOtherTwoIndices i k =
      {SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 2,
       SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 3} := by
  unfold subtwoOtherTwoIndices
  rw [← hj.2.1, ← hj.2.2]
  exact SubtwoHarmonicRanks.four_perm_remaining_pair _

theorem subtwoHeavyBigPrice_complement
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price) (i k : Fin 4) :
    G.subtwoHeavyBigPrice v neighbor bin price i k +
      G.subtwoHeavyClassMass v neighbor bin i k *
        G.subtwoNormalizedSetPrice price ((subtwoOtherTwoIndices i k).image neighbor) ≤
      G.subtwoHeavyClassMass v neighbor bin i k := by
  have h := G.subtwoHeavyClassAverage_le_const v neighbor bin i k
    (fun j => G.subtwoOrderedFourPrices v neighbor bin price j 0 +
      G.subtwoOrderedFourPrices v neighbor bin price j 1 +
      G.subtwoNormalizedSetPrice price ((subtwoOtherTwoIndices i k).image neighbor)) 1 (by
    intro j hj
    rw [G.subtwoOtherTwoIndices_eq_of_class v neighbor bin i k j hj]
    simp only [Finset.image_insert, Finset.image_singleton]
    exact (G.subtwo_ordered_heavy_complement_prices v neighbor hinj hne bin hbin price hR j hj.1).1)
  simpa only [G.subtwoHeavyClassAverage_add, G.subtwoHeavyClassAverage_const,
    mul_one, subtwoHeavyBigPrice] using h

theorem subtwoHeavySmallPrice_le_quarter_caps
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (i k : Fin 4) :
    G.subtwoHeavySmallPrice v neighbor bin price i k ≤
      G.subtwoHeavyClassMass v neighbor bin i k * ((1 / 4 : ℝ) *
        ∑ a ∈ subtwoOtherTwoIndices i k, G.subtwoNormalizedSetPrice price {v, neighbor a}) := by
  apply G.subtwoHeavyClassAverage_le_const
  intro j hj
  rw [G.subtwoOtherTwoIndices_eq_of_class v neighbor bin i k j hj]
  let π := SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j)
  have hn23 : π 2 ≠ π 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (π.injective h)
  have h := (G.subtwo_ordered_heavy_price_caps v neighbor hinj hne bin hbin price hp hR j hj.1).2.1
  change _ ≤ (1 / 4 : ℝ) * ∑ a ∈ ({π 2, π 3} : Finset (Fin 4)),
    G.subtwoNormalizedSetPrice price {v, neighbor a}
  rw [Finset.sum_pair hn23]
  exact h

theorem subtwoHeavySmallPrice_le_small_cap
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (i k : Fin 4) (sm : ℝ)
    (hsm : ∀ a ∈ subtwoOtherTwoIndices i k, G.subtwoNormalizedSetPrice price {v, neighbor a} ≤ sm) :
    G.subtwoHeavySmallPrice v neighbor bin price i k ≤
      G.subtwoHeavyClassMass v neighbor bin i k * ((11 / 30 : ℝ) * sm) := by
  apply G.subtwoHeavyClassAverage_le_const
  intro j hj
  have hs := hsm
  rw [G.subtwoOtherTwoIndices_eq_of_class v neighbor bin i k j hj] at hs
  have h2 := hs _ (Finset.mem_insert_self _ _)
  have h3 := hs _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hm := max_le h2 h3
  have h := (G.subtwo_ordered_heavy_price_caps v neighbor hinj hne bin hbin price hp hR j hj.1).2.2.1
  exact h.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

end
end WeightedEdgeColoring.WeightedMultigraph
