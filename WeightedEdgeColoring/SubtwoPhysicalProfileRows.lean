import WeightedEdgeColoring.SubtwoPhysicalProjectedBins
import WeightedEdgeColoring.SubtwoProfileRankTable
import WeightedEdgeColoring.SubtwoProfileCrossCost

/-!
# Profile inequalities for the actual four incident bundles

All four projections use one common packing of the original star. Their
physical loads add to at most one, and their minimum normalized bundle
costs are paid by the uniform distribution over those local bins.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoStarProjectionLoad_sum_le {I : Type*} [Fintype I]
    (F : I → Finset G.E) (hdisj : Pairwise (fun i k => Disjoint (F i) (F k)))
    {v : G.V} {n : ℕ} (bin : G.StarEdge v → Fin n) (j : Fin n) :
    (∑ i, G.subtwoStarProjectionLoad (F i) bin j) ≤ G.starBinLoad bin j := by
  classical
  have hp : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint F := by
    intro i hi k hk hik
    exact hdisj hik
  calc
    _ = G.subtwoStarProjectionLoad (Finset.univ.biUnion F) bin j := by
      unfold subtwoStarProjectionLoad
      exact (Finset.sum_biUnion hp).symm
    _ ≤ _ := G.subtwoStarProjectionLoad_le_star _ bin j

theorem subtwo_incident_floorBundles_disjoint {I : Type*}
    (v : G.V) (neighbor : I → G.V) (hinj : Function.Injective neighbor)
    (hne : ∀ i, v ≠ neighbor i) :
    Pairwise (fun i k => Disjoint (G.floorBundle (G.floorPairKey v (neighbor i)))
      (G.floorBundle (G.floorPairKey v (neighbor k)))) := by
  intro i k hik
  rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween v (neighbor i) (hne i),
    G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween v (neighbor k) (hne k)]
  exact (G.exactDemandEdgesBetween_pairwise_disjoint Finset.univ (hne i) (hne k)
    (fun h => hik (hinj h))).1

def subtwoPhysicalFourLoads (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (i : Fin 4) : ℝ :=
  G.subtwoStarProjectionLoad (G.floorBundle (G.floorPairKey v (neighbor i))) bin j

theorem subtwoPhysicalFourLoads_nonneg (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (i : Fin 4) :
    0 ≤ G.subtwoPhysicalFourLoads v neighbor bin j i :=
  G.subtwoStarProjectionLoad_nonneg _ bin j

theorem subtwoPhysicalFourLoads_sum_le_one (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (j : Fin n) :
    (∑ i, G.subtwoPhysicalFourLoads v neighbor bin j i) ≤ 1 :=
  (G.subtwoStarProjectionLoad_sum_le _ (G.subtwo_incident_floorBundles_disjoint v neighbor hinj hne)
    bin j).trans (hbin j)

theorem subtwo_uniform_bin_mass_sum {n : ℕ} (hn : 0 < n) :
    (∑ _j : Fin n, (1 / (n : ℝ))) = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [hnR]

/-- The exact full-star LP row for the four true minimum bundle costs,
derived from a chosen physical packing of their common star. -/
theorem subtwo_physical_full_star_rank_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) :
    (∑ i : Fin 4, (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n) ≤
      (17 / 12 : ℝ) + (23 / 84 : ℝ) *
        ∑ j : Fin n, if (∃ i, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i)
          then (1 / (n : ℝ)) else 0 := by
  classical
  apply SubtwoHarmonicRanks.full_star_rank_row_of_loads (fun _ : Fin n => 1 / (n : ℝ))
    (G.subtwoPhysicalFourLoads v neighbor bin)
    (fun i => (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n)
    (fun _ => by positivity) (le_of_eq (subtwo_uniform_bin_mass_sum hn))
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin)
    (G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin)
  intro i
  exact G.subtwo_floorBundle_normalized_cost_le_local_charge v (neighbor i) (hne i) hn bin hbin

/-- The directed cross-cost row also uses the actual common star packing
and the actual cost of the selected neighboring bundle. -/
theorem subtwo_physical_cross_cost_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (selected : Fin n → Prop) [DecidablePred selected]
    (hselected : ∀ j, selected j → 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j 0) :
    let w := G.subtwoPhysicalFourLoads v neighbor bin
    (∑ j : Fin n, if selected j then (1 / (n : ℝ)) *
      (harmonicCharge (w j 2) + harmonicCharge (w j 3)) else 0) +
      (G.floorBundleCover (G.floorPairKey v (neighbor 1))).cost / n ≤
      1 / 2 + (1 / 2 : ℝ) * (∑ j : Fin n, if 1 / 2 < w j 1 then (1 / (n : ℝ)) else 0) +
        (4 / 21 : ℝ) * ∑ j : Fin n, if selected j then (1 / (n : ℝ)) else 0 := by
  classical
  apply SubtwoHarmonicRanks.profile_cross_cost_of_loads (fun _ : Fin n => 1 / (n : ℝ))
    (G.subtwoPhysicalFourLoads v neighbor bin) selected
    ((G.floorBundleCover (G.floorPairKey v (neighbor 1))).cost / n)
    (fun _ => by positivity) (le_of_eq (subtwo_uniform_bin_mass_sum hn))
    (G.subtwoPhysicalFourLoads_nonneg v neighbor bin)
    (G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin) hselected
  exact G.subtwo_floorBundle_normalized_cost_le_local_charge v (neighbor 1) (hne 1) hn bin hbin

end
end WeightedEdgeColoring.WeightedMultigraph
