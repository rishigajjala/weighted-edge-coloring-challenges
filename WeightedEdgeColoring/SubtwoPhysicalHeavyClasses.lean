import WeightedEdgeColoring.SubtwoPhysicalExteriorPotential
import WeightedEdgeColoring.SubtwoPhysicalLoadLower

/-!
# The twelve heavy classes at an actual graph vertex

Each heavy star bin has a chosen largest and second-largest projection.
Their distinct indices define one of twelve classes. The class masses are
computed from the original bin assignment, rather than supplied as free
variables. Ties among the lighter projections cause no difficulty.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.SubtwoHarmonicRanks

theorem fourLoadOrder_first_eq_of_heavy (w : Fin 4 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : (∑ i, w i) ≤ 1)
    {i : Fin 4} (hi : 1 / 2 < w i) : fourLoadOrder w 0 = i := by
  classical
  by_contra hne
  have hpair : w (fourLoadOrder w 0) + w i ≤ 1 := by
    calc
      _ = ∑ j ∈ ({fourLoadOrder w 0, i} : Finset (Fin 4)), w j := by simp [hne]
      _ ≤ ∑ j : Fin 4, w j := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun j _ _ => hw j)
      _ ≤ 1 := hsum
  have hm := fourLoadOrder_first w i
  linarith

end WeightedEdgeColoring.SubtwoHarmonicRanks

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
attribute [local instance] Classical.propDecidable
universe u
variable (G : WeightedMultigraph.{u})

def SubtwoHeavyClassBin (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) (j : Fin n) : Prop :=
  (∃ h, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j h) ∧
  SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 0 = i ∧
  SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) 1 = k

def subtwoHeavyClassMass (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) : ℝ :=
  ∑ j : Fin n, if G.SubtwoHeavyClassBin v neighbor bin i k j then (1 / (n : ℝ)) else 0

theorem subtwoHeavyClassMass_nonneg (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i k : Fin 4) :
    0 ≤ G.subtwoHeavyClassMass v neighbor bin i k := by
  apply Finset.sum_nonneg
  intro j hj
  split <;> positivity

theorem subtwoHeavyClassMass_self (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (i : Fin 4) :
    G.subtwoHeavyClassMass v neighbor bin i i = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  have hn : ¬G.SubtwoHeavyClassBin v neighbor bin i i j := by
    intro h
    have he := (SubtwoHarmonicRanks.fourLoadOrder
      (G.subtwoPhysicalFourLoads v neighbor bin j)).injective (h.2.1.trans h.2.2.symm)
    norm_num at he
  simp [hn]

theorem sum_subtwoHeavyClassBin (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (f : Fin n → ℝ) :
    (∑ i : Fin 4, ∑ k : Fin 4, ∑ j : Fin n,
      if G.SubtwoHeavyClassBin v neighbor bin i k j then f j else 0) =
      ∑ j : Fin n, if (∃ h, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j h)
        then f j else 0 := by
  classical
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin n, ∑ k : Fin 4,
        if G.SubtwoHeavyClassBin v neighbor bin i k j then f j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ∑ i : Fin 4, ∑ k : Fin 4,
        if G.SubtwoHeavyClassBin v neighbor bin i k j then f j else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hh : ∃ h, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j h
      · simp only [SubtwoHeavyClassBin, hh, true_and, if_true]
        simp [ite_and]
      · simp only [SubtwoHeavyClassBin, hh, false_and, if_false, Finset.sum_const_zero]

theorem sum_subtwoHeavyClassMass (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) :
    (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k) =
      ∑ j : Fin n, if (∃ h, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j h)
        then (1 / (n : ℝ)) else 0 :=
  G.sum_subtwoHeavyClassBin v neighbor bin (fun _ => 1 / (n : ℝ))

theorem sum_subtwoHeavyClassMass_le_one (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (hn : 0 < n) (bin : G.StarEdge v → Fin n) :
    (∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k) ≤ 1 := by
  rw [G.sum_subtwoHeavyClassMass]
  calc
    _ ≤ ∑ _j : Fin n, (1 / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      split
      · rfl
      · positivity
    _ = 1 := subtwo_uniform_bin_mass_sum hn

theorem subtwoHeavyClassMass_first_eq
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (i : Fin 4) :
    (∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k) =
      ∑ j : Fin n, if 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i
        then (1 / (n : ℝ)) else 0 := by
  classical
  unfold subtwoHeavyClassMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  let w := G.subtwoPhysicalFourLoads v neighbor bin j
  have hc (k : Fin 4) : G.SubtwoHeavyClassBin v neighbor bin i k j ↔
      1 / 2 < w i ∧ SubtwoHarmonicRanks.fourLoadOrder w 1 = k := by
    constructor
    · intro h
      have hh := SubtwoHarmonicRanks.fourLoadOrder_heavy w h.1
      rw [h.2.1] at hh
      exact ⟨hh, h.2.2⟩
    · intro h
      exact ⟨⟨i, h.1⟩, SubtwoHarmonicRanks.fourLoadOrder_first_eq_of_heavy w
        (G.subtwoPhysicalFourLoads_nonneg v neighbor bin j)
        (G.subtwoPhysicalFourLoads_sum_le_one v neighbor hinj hne bin hbin j) h.1, h.2⟩
  dsimp only [w] at hc
  simp_rw [hc]
  by_cases hh : 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i
  · simp only [hh, true_and, if_true]
    simp
  · simp only [hh, false_and, if_false, Finset.sum_const_zero]

/-- The actual singleton lower row, indexed by its twelve heavy classes. -/
theorem subtwo_heavy_class_singleton_lower
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (bin : G.StarEdge v → Fin n) (hbin : ∀ j, G.starBinLoad bin j ≤ 1)
    (i : Fin 4) :
    (1 / 2 : ℝ) * (∑ k : Fin 4, G.subtwoHeavyClassMass v neighbor bin i k) ≤
      (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n := by
  rw [G.subtwoHeavyClassMass_first_eq v neighbor hinj hne bin hbin i]
  exact G.subtwo_floorBundle_heavy_mass_lower v (neighbor i) (hne i) bin

/-- The full-star row uses the same actual class masses as the singleton
rows and the boundary-potential inequality. -/
theorem subtwo_heavy_class_full_star_row
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) :
    (∑ i : Fin 4, (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n) -
      (23 / 84 : ℝ) * (∑ i : Fin 4, ∑ k : Fin 4,
        G.subtwoHeavyClassMass v neighbor bin i k) ≤ (17 / 12 : ℝ) := by
  rw [G.sum_subtwoHeavyClassMass]
  have h := G.subtwo_physical_full_star_rank_row v neighbor hinj hne hn bin hbin
  linarith

end
end WeightedEdgeColoring.WeightedMultigraph
