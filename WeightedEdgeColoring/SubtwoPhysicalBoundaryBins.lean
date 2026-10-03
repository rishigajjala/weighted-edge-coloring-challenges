import WeightedEdgeColoring.SubtwoPhysicalProfileRows

/-! Exterior harmonic charge and remaining capacity in actual star bins. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

def subtwoStarProjectionCharge (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) : ℝ :=
  ∑ e ∈ F, harmonicCharge (G.subtwoStarBinEdgeWeight bin j e)

theorem subtwoStarProjectionCharge_nonneg (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) : 0 ≤ G.subtwoStarProjectionCharge F bin j :=
  Finset.sum_nonneg fun _ _ => harmonicCharge_nonneg _

theorem subtwoStarProjectionCharge_le_linear (F : Finset G.E) {v : G.V} {n r : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (hr : 0 < r)
    (hload : G.subtwoStarProjectionLoad F bin j ≤ 1 / (r : ℝ)) :
    G.subtwoStarProjectionCharge F bin j ≤ ((r + 1 : ℕ) : ℝ) / r *
      G.subtwoStarProjectionLoad F bin j := by
  unfold subtwoStarProjectionCharge subtwoStarProjectionLoad
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  apply SubtwoHarmonicRanks.charge_le_linear hr (G.subtwoStarBinEdgeWeight_nonneg bin j e)
  exact (Finset.single_le_sum (fun f _ => G.subtwoStarBinEdgeWeight_nonneg bin j f) he).trans hload

theorem sum_subtwoStarProjectionCharge (F : Finset G.E) {v : G.V} {n : ℕ}
    (bin : G.StarEdge v → Fin n) :
    (∑ j : Fin n, G.subtwoStarProjectionCharge F bin j) =
      ∑ e ∈ F, if G.Inc v e then harmonicCharge (G.weight e) else 0 := by
  classical
  unfold subtwoStarProjectionCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hi : G.Inc v e
  · have hpoint (j : Fin n) : harmonicCharge (G.subtwoStarBinEdgeWeight bin j e) =
        if bin ⟨e, hi⟩ = j then harmonicCharge (G.weight e) else 0 := by
      by_cases hj : bin ⟨e, hi⟩ = j <;>
        simp [subtwoStarBinEdgeWeight, hi, hj, SubtwoHarmonicRanks.harmonicCharge_zero]
    simp_rw [hpoint]
    simp [hi]
  · simp [subtwoStarBinEdgeWeight, hi, SubtwoHarmonicRanks.harmonicCharge_zero]

theorem subtwoStarProjectionLoad_add_le (F H : Finset G.E) (hdisj : Disjoint F H)
    {v : G.V} {n : ℕ} (bin : G.StarEdge v → Fin n) (j : Fin n) :
    G.subtwoStarProjectionLoad F bin j + G.subtwoStarProjectionLoad H bin j ≤ G.starBinLoad bin j := by
  have heq : G.subtwoStarProjectionLoad F bin j + G.subtwoStarProjectionLoad H bin j =
      G.subtwoStarProjectionLoad (F ∪ H) bin j := by
    unfold subtwoStarProjectionLoad
    exact (Finset.sum_union hdisj).symm
  rw [heq]
  exact G.subtwoStarProjectionLoad_le_star _ bin j

theorem subtwoPhysicalFourLoads_add_external_le
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (external : Finset G.E)
    (hdisj : ∀ i, Disjoint (G.floorBundle (G.floorPairKey v (neighbor i))) external)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (j : Fin n) :
    (∑ i, G.subtwoPhysicalFourLoads v neighbor bin j i) +
      G.subtwoStarProjectionLoad external bin j ≤ G.starBinLoad bin j := by
  classical
  let F : Fin 4 → Finset G.E := fun i => G.floorBundle (G.floorPairKey v (neighbor i))
  have hp : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint F := by
    intro i hi k hk hik
    exact G.subtwo_incident_floorBundles_disjoint v neighbor hinj hne hik
  have heq : (∑ i, G.subtwoPhysicalFourLoads v neighbor bin j i) =
      G.subtwoStarProjectionLoad (Finset.univ.biUnion F) bin j := by
    unfold subtwoPhysicalFourLoads subtwoStarProjectionLoad
    exact (Finset.sum_biUnion hp).symm
  have hd : Disjoint (Finset.univ.biUnion F) external := by
    apply Finset.disjoint_left.mpr
    intro e he hx
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
    exact (Finset.disjoint_left.mp (hdisj i)) hei hx
  rw [heq]
  exact G.subtwoStarProjectionLoad_add_le _ external hd bin j

/-- The boundary capacity premise of the potential row follows from the
original local packing, with the better coefficient in heavy bins. -/
theorem subtwoPhysicalFourLoads_boundary_capacity
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (external : Finset G.E)
    (hdisj : ∀ i, Disjoint (G.floorBundle (G.floorPairKey v (neighbor i))) external)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1) (j : Fin n) :
    (∑ i, G.subtwoPhysicalFourLoads v neighbor bin j i) +
      (if (∃ i, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i)
       then (2 / 3 : ℝ) * G.subtwoStarProjectionCharge external bin j
       else G.subtwoStarProjectionCharge external bin j / 2) ≤ 1 := by
  classical
  have htotal := (G.subtwoPhysicalFourLoads_add_external_le v neighbor hinj hne external hdisj bin j).trans
    (hbin j)
  have hload0 := G.subtwoStarProjectionLoad_nonneg external bin j
  have hint0 : 0 ≤ ∑ i, G.subtwoPhysicalFourLoads v neighbor bin j i :=
    Finset.sum_nonneg (fun i _ => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j i)
  split_ifs with hh
  · obtain ⟨i, hi⟩ := hh
    have hsingle := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin 4)))
      (fun i _ => G.subtwoPhysicalFourLoads_nonneg v neighbor bin j i) (Finset.mem_univ i)
    have hload : G.subtwoStarProjectionLoad external bin j ≤ 1 / 2 := by linarith
    have hc := G.subtwoStarProjectionCharge_le_linear external bin j (r := 2) (by decide) hload
    norm_num at hc
    linarith
  · have hload : G.subtwoStarProjectionLoad external bin j ≤ 1 := by linarith
    have hc := G.subtwoStarProjectionCharge_le_linear external bin j (r := 1) (by decide) (by simpa using hload)
    norm_num at hc
    linarith

end
end WeightedEdgeColoring.WeightedMultigraph
