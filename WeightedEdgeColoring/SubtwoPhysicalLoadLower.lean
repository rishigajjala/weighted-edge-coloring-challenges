import WeightedEdgeColoring.SubtwoPhysicalProfileRows

/-!
# The heavy-bin lower bound for actual minimum bundle costs

An exact cover pays at least the total physical weight. In particular,
every local bin whose projection onto a bundle exceeds one half pays one
half towards that bundle's cost. This is the singleton lower row in the
five-vertex profile system.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.BinPackingInstance.ExactDemandPatternCover

theorem subtwo_total_demand_load_le_cost
    {B : BinPackingInstance} {demand : B.Item → ℕ}
    (C : B.ExactDemandPatternCover demand) :
    (∑ i : B.Item, (demand i : ℝ) * B.weight i) ≤ C.cost := by
  calc
    _ = ∑ i : B.Item, (∑ p : B.Pattern, C.coeff p * (p.multiplicity i : ℝ)) * B.weight i := by
      simp_rw [C.sum_coeff_mul_multiplicity_eq]
    _ = ∑ p : B.Pattern, C.coeff p * (∑ i : B.Item, (p.multiplicity i : ℝ) * B.weight i) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ p : B.Pattern, C.coeff p := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [mul_one] using mul_le_mul_of_nonneg_left p.capacity (C.coeff_nonneg p)
    _ = _ := C.sum_coeff_eq_cost

end WeightedEdgeColoring.BinPackingInstance.ExactDemandPatternCover

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_edgeSet_weight_le_cover_cost (F : Finset G.E) (C : G.EdgeSetExactDemandCover F) :
    (∑ e ∈ F, G.weight e) ≤ C.cost := by
  rw [← G.subtwo_edgeSetWeightDemand_charge F (fun x => x)]
  exact C.subtwo_total_demand_load_le_cost

theorem sum_subtwoStarProjectionLoad (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) :
    (∑ j : Fin n, G.subtwoStarProjectionLoad F bin j) =
      ∑ e ∈ F, if G.Inc v e then G.weight e else 0 := by
  classical
  unfold subtwoStarProjectionLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hi : G.Inc v e <;> simp [subtwoStarBinEdgeWeight, hi]

theorem subtwo_floorBundle_cost_ge_sum_load
    (a b : G.V) (hab : a ≠ b) {n : ℕ} (bin : G.StarEdge a → Fin n) :
    (∑ j : Fin n,
      G.subtwoStarProjectionLoad (G.floorBundle (G.floorPairKey a b)) bin j) ≤
      (G.floorBundleCover (G.floorPairKey a b)).cost := by
  rw [G.sum_subtwoStarProjectionLoad]
  have hinc : ∀ e ∈ G.floorBundle (G.floorPairKey a b), G.Inc a e := by
    intro e he
    rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab] at he
    exact G.inc_left_of_mem_exactDemandEdgesBetween he
  calc
    _ = ∑ e ∈ G.floorBundle (G.floorPairKey a b), G.weight e := by
      apply Finset.sum_congr rfl
      intro e he
      simp [hinc e he]
    _ ≤ _ := G.subtwo_edgeSet_weight_le_cover_cost _ _

theorem subtwo_floorBundle_heavy_mass_lower
    (a b : G.V) (hab : a ≠ b) {n : ℕ} (bin : G.StarEdge a → Fin n) :
    (1 / 2 : ℝ) * (∑ j : Fin n,
      if 1 / 2 < G.subtwoStarProjectionLoad (G.floorBundle (G.floorPairKey a b)) bin j
      then (1 / (n : ℝ)) else 0) ≤
      (G.floorBundleCover (G.floorPairKey a b)).cost / n := by
  classical
  have hl : (1 / 2 : ℝ) * (∑ j : Fin n,
      if 1 / 2 < G.subtwoStarProjectionLoad (G.floorBundle (G.floorPairKey a b)) bin j
      then (1 : ℝ) else 0) ≤ (G.floorBundleCover (G.floorPairKey a b)).cost := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum ?_) (G.subtwo_floorBundle_cost_ge_sum_load a b hab bin)
    intro j hj
    split_ifs with h
    · simpa using h.le
    · simpa using G.subtwoStarProjectionLoad_nonneg (G.floorBundle (G.floorPairKey a b)) bin j
  have h := div_le_div_of_nonneg_right hl (show (0 : ℝ) ≤ n by positivity)
  convert h using 1
  rw [mul_div_assoc, Finset.sum_div]
  simp only [ite_div, one_div, zero_div]

end
end WeightedEdgeColoring.WeightedMultigraph
