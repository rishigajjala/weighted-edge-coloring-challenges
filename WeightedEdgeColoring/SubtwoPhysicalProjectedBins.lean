import WeightedEdgeColoring.SubtwoProjectedCoverCost
import WeightedEdgeColoring.SubtwoBundleCharge

/-!
# Projecting actual local star bins onto bundles

The projection loads below are formed from the original physical edge
assignment.  Their harmonic charges pay for the chosen minimum bundle
cover, so the profile rank rows apply to the actual costs in the block
construction.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

def subtwoStarBinEdgeWeight {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (e : G.E) : ℝ :=
  if he : G.Inc v e then if bin ⟨e, he⟩ = j then G.weight e else 0 else 0

def subtwoStarProjectionLoad (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) : ℝ :=
  ∑ e ∈ F, G.subtwoStarBinEdgeWeight bin j e

theorem subtwoStarBinEdgeWeight_nonneg {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (e : G.E) :
    0 ≤ G.subtwoStarBinEdgeWeight bin j e := by
  unfold subtwoStarBinEdgeWeight
  split_ifs <;> first | exact (G.weight_pos e).le | rfl

theorem subtwoStarProjectionLoad_nonneg (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) : 0 ≤ G.subtwoStarProjectionLoad F bin j :=
  Finset.sum_nonneg fun e _ => G.subtwoStarBinEdgeWeight_nonneg bin j e

theorem subtwoStarProjectionLoad_univ {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) :
    G.subtwoStarProjectionLoad Finset.univ bin j = G.starBinLoad bin j := by
  classical
  unfold subtwoStarProjectionLoad
  have hfilter : (∑ e : G.E, G.subtwoStarBinEdgeWeight bin j e) =
      ∑ e ∈ Finset.univ.filter (G.Inc v), G.subtwoStarBinEdgeWeight bin j e := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hi : G.Inc v e <;> simp [subtwoStarBinEdgeWeight, hi]
  rw [hfilter, Finset.sum_subtype (p := G.Inc v)
    (Finset.univ.filter (G.Inc v)) (by intro e; simp)]
  unfold starBinLoad
  apply Finset.sum_congr rfl
  intro e he
  simp [subtwoStarBinEdgeWeight, e.property]

theorem subtwoStarProjectionLoad_le_star (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) :
    G.subtwoStarProjectionLoad F bin j ≤ G.starBinLoad bin j := by
  rw [← G.subtwoStarProjectionLoad_univ bin j]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun e _ _ => G.subtwoStarBinEdgeWeight_nonneg bin j e)

def subtwoStarProjectionBin (F : Finset G.E) (v : G.V)
    (hinc : ∀ e ∈ F, G.Inc v e) {n : ℕ} (bin : G.StarEdge v → Fin n) :
    {e : G.E // e ∈ F} → Fin n :=
  fun e => bin ⟨e.val, hinc e.val e.property⟩

theorem subtwoStarProjectionBin_load_eq (F : Finset G.E) (v : G.V)
    (hinc : ∀ e ∈ F, G.Inc v e) {n : ℕ} (bin : G.StarEdge v → Fin n) (j : Fin n) :
    (∑ e : {e : G.E // e ∈ F},
      if G.subtwoStarProjectionBin F v hinc bin e = j then G.weight e.val else 0) =
      G.subtwoStarProjectionLoad F bin j := by
  classical
  rw [subtwoStarProjectionLoad, Finset.sum_subtype (p := fun e => e ∈ F) F (by intro e; simp)]
  apply Finset.sum_congr rfl
  intro e he
  simp [subtwoStarProjectionBin, subtwoStarBinEdgeWeight, hinc e.val e.property]

theorem subtwoStarProjectionBin_capacity (F : Finset G.E) (v : G.V)
    (hinc : ∀ e ∈ F, G.Inc v e) {n : ℕ} (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (j : Fin n) :
    (∑ e : {e : G.E // e ∈ F},
      if G.subtwoStarProjectionBin F v hinc bin e = j then G.weight e.val else 0) ≤ 1 := by
  rw [G.subtwoStarProjectionBin_load_eq F v hinc bin j]
  exact (G.subtwoStarProjectionLoad_le_star F bin j).trans (hbin j)

/-- The harmonic cost domination for any incident physical edge set, with
the actual minimum exact-demand cover and the original star bin map. -/
theorem subtwo_edgeSetCover_cost_le_projection_charge
    (F : Finset G.E) (v : G.V) (hinc : ∀ e ∈ F, G.Inc v e)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (C : (G.edgeSetWeightBinPackingInstance F).ExactDemandPatternCover (G.edgeSetWeightDemand F))
    (hmin : C.IsMinimumCost) :
    C.cost ≤ ∑ j : Fin n, harmonicCharge (G.subtwoStarProjectionLoad F bin j) := by
  classical
  let binF := G.subtwoStarProjectionBin F v hinc bin
  have hload := G.subtwoStarProjectionBin_capacity F v hinc bin hbin
  let P : BinPackingInstance.ExactDemandPatternCover.PackingCertificate
      (B := G.edgeSetWeightBinPackingInstance F) (G.edgeSetWeightDemand F) n :=
    { pattern := G.edgeSetWeightPatternOfBin F binF hload
      covers_exact := by intro i; exact G.sum_edgeSetWeightPatternOfBin_multiplicity F binF hload i }
  have hc := C.subtwo_cost_le_packing_projection_charge hmin P
  calc
    _ ≤ ∑ j : Fin n, harmonicCharge (P.pattern j).subtwoProjectionLoad := hc
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      change (∑ x, ((G.edgeSetWeightPatternOfBin F binF hload j).multiplicity x : ℝ) *
        (G.edgeSetWeightBinPackingInstance F).weight x) = _
      exact (G.edgeSetWeightPatternOfBin_load_eq F binF hload j).trans
        (G.subtwoStarProjectionBin_load_eq F v hinc bin j)

theorem subtwo_floorBundle_cost_le_local_projected_charge
    (a b : G.V) (hab : a ≠ b) {n : ℕ}
    (bin : G.StarEdge a → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1) :
    (G.floorBundleCover (G.floorPairKey a b)).cost ≤
      ∑ j : Fin n, harmonicCharge
        (G.subtwoStarProjectionLoad (G.floorBundle (G.floorPairKey a b)) bin j) := by
  have hinc : ∀ e ∈ G.floorBundle (G.floorPairKey a b), G.Inc a e := by
    intro e he
    rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab] at he
    exact G.inc_left_of_mem_exactDemandEdgesBetween he
  exact G.subtwo_edgeSetCover_cost_le_projection_charge _ a hinc bin hbin
    (G.floorBundleCover (G.floorPairKey a b)) (G.floorBundleCover_minimum _)

/-- The normalized cost premise of the profile rows now follows from an
actual local packing, with uniform bin mass `1/n`. -/
theorem subtwo_floorBundle_normalized_cost_le_local_charge
    (a b : G.V) (hab : a ≠ b) {n : ℕ} (hn : 0 < n)
    (bin : G.StarEdge a → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1) :
    (G.floorBundleCover (G.floorPairKey a b)).cost / n ≤
      ∑ j : Fin n, (1 / (n : ℝ)) * harmonicCharge
        (G.subtwoStarProjectionLoad (G.floorBundle (G.floorPairKey a b)) bin j) := by
  have h := div_le_div_of_nonneg_right
    (G.subtwo_floorBundle_cost_le_local_projected_charge a b hab bin hbin)
    (show (0 : ℝ) ≤ n by positivity)
  rw [← Finset.mul_sum]
  simpa [div_eq_mul_inv, mul_comm] using h

end
end WeightedEdgeColoring.WeightedMultigraph
