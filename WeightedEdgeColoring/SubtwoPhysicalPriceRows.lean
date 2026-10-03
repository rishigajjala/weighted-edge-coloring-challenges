import WeightedEdgeColoring.SubtwoPhysicalBinPatterns

/-!
# Actual projected prices and copy inequalities

The normalized prices below are physical edge-price sums in a chosen bin,
divided by the maximum price of a feasible weighted color. Disjoint bundle
projections can be added, and repeated copies can be combined with a color
on complementary vertices.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

def subtwoIncidentBundleUnion (v : G.V) (neighbor : Fin 4 → G.V) (I : Finset (Fin 4)) :
    Finset G.E := I.biUnion fun i => G.floorBundle (G.floorPairKey v (neighbor i))

theorem subtwoIncidentBundleUnion_support (v : G.V) (neighbor : Fin 4 → G.V)
    (hne : ∀ i, v ≠ neighbor i) (I : Finset (Fin 4)) :
    ∀ e ∈ G.subtwoIncidentBundleUnion v neighbor I,
      G.fst e ∈ insert v (I.image neighbor) ∧ G.snd e ∈ insert v (I.image neighbor) := by
  intro e he
  obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
  rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween v (neighbor i) (hne i)] at he
  have hm : neighbor i ∈ I.image neighbor := Finset.mem_image.mpr ⟨i, hi, rfl⟩
  rcases (Finset.mem_filter.mp he).2 with h | h <;> simp [h.1, h.2, hm]

theorem subtwoIncidentBundleUnion_load (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (I : Finset (Fin 4)) {n : ℕ} (bin : G.StarEdge v → Fin n) (j : Fin n) :
    G.subtwoStarProjectionLoad (G.subtwoIncidentBundleUnion v neighbor I) bin j =
      ∑ i ∈ I, G.subtwoPhysicalFourLoads v neighbor bin j i := by
  have hd : (↑I : Set (Fin 4)).PairwiseDisjoint
      (fun i => G.floorBundle (G.floorPairKey v (neighbor i))) := by
    intro i hi k hk hik
    exact G.subtwo_incident_floorBundles_disjoint v neighbor hinj hne hik
  exact Finset.sum_biUnion hd

def subtwoPhysicalFourPrices (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (j : Fin n) (i : Fin 4) : ℝ :=
  G.subtwoStarProjectionPrice (G.floorBundle (G.floorPairKey v (neighbor i))) bin j price /
    G.subtwoColorPriceMax price

theorem subtwoIncidentBundleUnion_price (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (I : Finset (Fin 4)) {n : ℕ} (bin : G.StarEdge v → Fin n)
    (j : Fin n) (price : G.E → ℝ) :
    G.subtwoStarProjectionPrice (G.subtwoIncidentBundleUnion v neighbor I) bin j price /
      G.subtwoColorPriceMax price = ∑ i ∈ I, G.subtwoPhysicalFourPrices v neighbor bin price j i := by
  have hd : (↑I : Set (Fin 4)).PairwiseDisjoint
      (fun i => G.floorBundle (G.floorPairKey v (neighbor i))) := by
    intro i hi k hk hik
    exact G.subtwo_incident_floorBundles_disjoint v neighbor hinj hne hik
  unfold subtwoPhysicalFourPrices
  simp_rw [G.subtwoStarProjectionPrice_eq]
  rw [← Finset.sum_div]
  congr 1
  exact Finset.sum_biUnion hd

theorem subtwoPhysicalFourPrices_nonneg (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e)
    (hR : 0 < G.subtwoColorPriceMax price) (j : Fin n) (i : Fin 4) :
    0 ≤ G.subtwoPhysicalFourPrices v neighbor bin price j i :=
  div_nonneg (G.subtwoStarProjectionPrice_nonneg _ bin j price hp) hR.le

theorem subtwoPhysicalFourPrices_le_harmonic
    (v : G.V) (neighbor : Fin 4 → G.V) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price) (j : Fin n) (i : Fin 4) :
    G.subtwoPhysicalFourPrices v neighbor bin price j i ≤
      G.subtwoNormalizedSetPrice price {v, neighbor i} *
        harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j i) := by
  have hs : ∀ e ∈ G.floorBundle (G.floorPairKey v (neighbor i)),
      G.fst e ∈ ({v, neighbor i} : Finset G.V) ∧ G.snd e ∈ ({v, neighbor i} : Finset G.V) := by
    intro e he
    rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween v (neighbor i) (hne i)] at he
    rcases (Finset.mem_filter.mp he).2 with h | h <;> simp [h.1, h.2]
  have h := div_le_div_of_nonneg_right
    (G.subtwoStarProjectionPrice_le_harmonic _ {v, neighbor i} hs bin hbin j price) hR.le
  simpa only [subtwoPhysicalFourPrices, subtwoNormalizedSetPrice, subtwoPhysicalFourLoads,
    div_mul_eq_mul_div] using h

theorem subtwoPhysicalFourPrices_sum_le_one
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price) (j : Fin n)
    (I : Finset (Fin 4)) :
    (∑ i ∈ I, G.subtwoPhysicalFourPrices v neighbor bin price j i) ≤ 1 := by
  rw [← G.subtwoIncidentBundleUnion_price v neighbor hinj hne I bin j price]
  apply (div_le_one hR).2
  exact G.subtwoStarProjectionPrice_le_max _ bin hbin j price

/-- Repeating an actual group of projected bundles and adjoining a color
on disjoint vertices gives the one-, two-, and three-copy price rows. -/
theorem subtwoPhysicalFourPrices_copies_complement
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (I : Finset (Fin 4)) (T : Finset G.V) (hdisj : Disjoint (insert v (I.image neighbor)) T)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (price : G.E → ℝ) (hR : 0 < G.subtwoColorPriceMax price)
    (j : Fin n) (k : ℕ)
    (hload : (k : ℝ) * (∑ i ∈ I, G.subtwoPhysicalFourLoads v neighbor bin j i) ≤ 1) :
    (k : ℝ) * (∑ i ∈ I, G.subtwoPhysicalFourPrices v neighbor bin price j i) +
      G.subtwoNormalizedSetPrice price T ≤ 1 := by
  let F := G.subtwoIncidentBundleUnion v neighbor I
  have hl : (k : ℝ) * (∑ e : G.E,
      ((G.subtwoStarBinPattern F bin hbin j).val e : ℝ) * G.weight e) ≤ 1 := by
    change (k : ℝ) * (∑ e, (G.subtwoStarBinMultiplicity F bin j e : ℝ) * G.weight e) ≤ 1
    rw [G.subtwoStarBinMultiplicity_load, G.subtwoIncidentBundleUnion_load v neighbor hinj hne]
    exact hload
  have h := G.subtwo_normalized_copies_complement_price
    (G.subtwoStarBinPattern F bin hbin j) k (insert v (I.image neighbor)) T hdisj
    (G.subtwoStarBinPattern_support F _ (G.subtwoIncidentBundleUnion_support v neighbor hne I)
      bin hbin j) hl price hR
  change (k : ℝ) * (G.subtwoStarProjectionPrice F bin j price / G.subtwoColorPriceMax price) +
    G.subtwoNormalizedSetPrice price T ≤ 1 at h
  rwa [G.subtwoIncidentBundleUnion_price v neighbor hinj hne] at h

end
end WeightedEdgeColoring.WeightedMultigraph
