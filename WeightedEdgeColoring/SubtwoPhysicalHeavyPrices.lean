import WeightedEdgeColoring.SubtwoPhysicalPriceRows

/-!
# Price bounds inside an actual heavy bin

The two larger projections and the two smaller projections are sums of
physical edge prices. Their harmonic bounds and complementary-copy bounds
follow from genuine feasible patterns in the same original star bin.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_disjoint_indexed_neighbors (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (I J : Finset (Fin 4)) (hIJ : Disjoint I J) :
    Disjoint (insert v (I.image neighbor)) (J.image neighbor) := by
  apply Finset.disjoint_left.mpr
  intro x hx hj
  obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp hj
  rcases Finset.mem_insert.mp hx with he | he
  · exact hne j he.symm
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp he
    exact Finset.disjoint_left.mp hIJ hi ((hinj he).symm ▸ hjJ)

theorem subtwoPhysicalFourPrices_pair_complement
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (a b c d : Fin 4) (hab : a ≠ b) (hd : Disjoint ({a, b} : Finset (Fin 4)) {c, d})
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (j : Fin n) (k : ℕ)
    (hload : (k : ℝ) * (G.subtwoPhysicalFourLoads v neighbor bin j a +
      G.subtwoPhysicalFourLoads v neighbor bin j b) ≤ 1) :
    (k : ℝ) * (G.subtwoPhysicalFourPrices v neighbor bin price j a +
      G.subtwoPhysicalFourPrices v neighbor bin price j b) +
      G.subtwoNormalizedSetPrice price {neighbor c, neighbor d} ≤ 1 := by
  have hd' := G.subtwo_disjoint_indexed_neighbors v neighbor hinj hne {a, b} {c, d} hd
  simp only [Finset.image_insert, Finset.image_singleton] at hd'
  have h := G.subtwoPhysicalFourPrices_copies_complement v neighbor hinj hne {a, b}
    {neighbor c, neighbor d}
    (by simpa only [Finset.image_insert, Finset.image_singleton] using hd')
    bin hbin price hR j k (by simpa [hab] using hload)
  simpa [hab] using h

def subtwoOrderedFourPrices (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (j : Fin n) (i : Fin 4) : ℝ :=
  G.subtwoPhysicalFourPrices v neighbor bin price j
    (SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) i)

theorem subtwoOrderedFourPrices_sum (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (j : Fin n) :
    (∑ i : Fin 4, G.subtwoOrderedFourPrices v neighbor bin price j i) =
      ∑ i : Fin 4, G.subtwoPhysicalFourPrices v neighbor bin price j i :=
  Equiv.sum_comp _ _

theorem subtwo_ordered_heavy_price_caps
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) (hR : 0 < G.subtwoColorPriceMax price)
    (j : Fin n) (hh : ∃ i, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i) :
    let p := G.subtwoOrderedFourPrices v neighbor bin price j
    let π := SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j)
    let m := fun i => G.subtwoNormalizedSetPrice price {v, neighbor (π i)}
    p 0 + p 1 ≤ m 0 + (1 / 2 : ℝ) * m 1 ∧
      p 2 + p 3 ≤ (1 / 4 : ℝ) * (m 2 + m 3) ∧
      p 2 + p 3 ≤ (11 / 30 : ℝ) * max (m 2) (m 3) ∧
      p 0 + p 1 + p 2 + p 3 ≤ 1 := by
  classical
  dsimp only
  let w := G.subtwoOrderedFourLoads v neighbor bin j
  let p := G.subtwoOrderedFourPrices v neighbor bin price j
  let π := SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j)
  let m := fun i => G.subtwoNormalizedSetPrice price {v, neighbor (π i)}
  have hw (i) : 0 ≤ w i := G.subtwoPhysicalFourLoads_nonneg v neighbor bin j _
  have hm (i) : 0 ≤ m i := (G.subtwoNormalizedSetPrice_bounds price hp hR _).1
  have hl : w 0 + w 1 + w 2 + w 3 ≤ 1 := by
    have h := G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j
    rw [← G.subtwoOrderedFourLoads_sum] at h
    simpa [w, Fin.sum_univ_succ, add_assoc] using h
  have hh0 : 1 / 2 < w 0 := SubtwoHarmonicRanks.fourLoadOrder_heavy _ hh
  have hs : w 2 ≤ w 1 ∧ w 3 ≤ w 1 := SubtwoHarmonicRanks.fourLoadOrder_second
    (G.subtwoPhysicalFourLoads v neighbor bin j)
  have hr := SubtwoHarmonicRanks.heavy_subset_ranks (w 0) (w 1) (w 2) (w 3)
    hh0 (hw 1) (hw 2) (hw 3) hs.1 hs.2 hl
  have hpi (i) : p i ≤ m i * harmonicCharge (w i) :=
    G.subtwoPhysicalFourPrices_le_harmonic v neighbor hne bin hbin price hR j (π i)
  have hp0 : p 0 ≤ m 0 := by simpa [hr.heavy_eq] using hpi 0
  have hp1 : p 1 ≤ m 1 * (1 / 2) :=
    (hpi 1).trans (mul_le_mul_of_nonneg_left hr.second_le (hm 1))
  have hp2 : p 2 ≤ m 2 * (1 / 4) :=
    (hpi 2).trans (mul_le_mul_of_nonneg_left hr.small₁_le (hm 2))
  have hp3 : p 3 ≤ m 3 * (1 / 4) :=
    (hpi 3).trans (mul_le_mul_of_nonneg_left hr.small₂_le (hm 3))
  have hsmall : p 2 + p 3 ≤ max (m 2) (m 3) * (11 / 30) := by
    calc
      _ ≤ max (m 2) (m 3) * (harmonicCharge (w 2) + harmonicCharge (w 3)) := by
        have h2 := mul_le_mul_of_nonneg_right (le_max_left (m 2) (m 3))
          (harmonicCharge_nonneg (w 2))
        have h3 := mul_le_mul_of_nonneg_right (le_max_right (m 2) (m 3))
          (harmonicCharge_nonneg (w 3))
        nlinarith [hpi 2, hpi 3]
      _ ≤ _ := mul_le_mul_of_nonneg_left hr.small_pair ((hm 2).trans (le_max_left _ _))
  have hfull : p 0 + p 1 + p 2 + p 3 ≤ 1 := by
    have h := G.subtwoPhysicalFourPrices_sum_le_one v neighbor hinj hne bin hbin price hR j Finset.univ
    rw [← G.subtwoOrderedFourPrices_sum] at h
    simpa [p, Fin.sum_univ_succ, add_assoc] using h
  change p 0 + p 1 ≤ m 0 + (1 / 2 : ℝ) * m 1 ∧
    p 2 + p 3 ≤ (1 / 4 : ℝ) * (m 2 + m 3) ∧
    p 2 + p 3 ≤ (11 / 30 : ℝ) * max (m 2) (m 3) ∧
    p 0 + p 1 + p 2 + p 3 ≤ 1
  exact ⟨by linarith, by linarith, by nlinarith, hfull⟩

theorem subtwo_ordered_heavy_complement_prices
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (j : Fin n) (hh : ∃ i, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i) :
    let p := G.subtwoOrderedFourPrices v neighbor bin price j
    let π := SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j)
    p 0 + p 1 + G.subtwoNormalizedSetPrice price {neighbor (π 2), neighbor (π 3)} ≤ 1 ∧
      3 * (p 2 + p 3) + G.subtwoNormalizedSetPrice price {neighbor (π 0), neighbor (π 1)} ≤ 1 := by
  classical
  dsimp only
  let w := G.subtwoOrderedFourLoads v neighbor bin j
  let π := SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j)
  have hw (i) : 0 ≤ w i := G.subtwoPhysicalFourLoads_nonneg v neighbor bin j _
  have hl : w 0 + w 1 + w 2 + w 3 ≤ 1 := by
    have h := G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j
    rw [← G.subtwoOrderedFourLoads_sum] at h
    simpa [w, Fin.sum_univ_succ, add_assoc] using h
  have hh0 : 1 / 2 < w 0 := SubtwoHarmonicRanks.fourLoadOrder_heavy _ hh
  have hs : w 2 ≤ w 1 ∧ w 3 ≤ w 1 := SubtwoHarmonicRanks.fourLoadOrder_second
    (G.subtwoPhysicalFourLoads v neighbor bin j)
  have hd : Disjoint ({π 0, π 1} : Finset (Fin 4)) {π 2, π 3} := by
    simp [Finset.disjoint_left, π.injective.eq_iff]
  have h01 : π 0 ≠ π 1 := fun h => (by decide : (0 : Fin 4) ≠ 1) (π.injective h)
  have h23 : π 2 ≠ π 3 := fun h => (by decide : (2 : Fin 4) ≠ 3) (π.injective h)
  have hb := G.subtwoPhysicalFourPrices_pair_complement v neighbor hinj hne
    (π 0) (π 1) (π 2) (π 3) h01 hd bin hbin price hR j 1
    (by simpa only [Nat.cast_one, one_mul] using
      (show w 0 + w 1 ≤ 1 by linarith [hw 2, hw 3]))
  have hs3 := SubtwoBinProfileRows.three_smaller_pairs_fit
    (w 0) (w 1) (w 2) (w 3) hh0 (hw 2) (hw 3) hs.1 hs.2 hl
  have ht := G.subtwoPhysicalFourPrices_pair_complement v neighbor hinj hne
    (π 2) (π 3) (π 0) (π 1) h23 hd.symm bin hbin price hR j 3
    (by simpa only [Nat.cast_ofNat] using hs3.le)
  exact ⟨by simpa [subtwoOrderedFourPrices, π] using hb,
    by simpa [subtwoOrderedFourPrices, π] using ht⟩

end
end WeightedEdgeColoring.WeightedMultigraph
