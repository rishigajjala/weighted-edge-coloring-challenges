import WeightedEdgeColoring.SubtwoPhysicalFiveIndices

/-!
# Local physical rows in the archive's pair and triple coordinates

Diagonal heavy classes have zero mass and zero price. Removing them gives
the twelve coordinates at a vertex in the frozen generator's order.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}

namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem heavyMass_first_sum (v : Fin 5) (i : Fin 4) :
    (∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j)) =
      ∑ k : Fin 4, G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k := by
  simp only [D.heavyMass_classIndex]
  rw [Fin.sum_univ_succAbove
    (fun k => G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k) i]
  rw [G.subtwoHeavyClassMass_self, zero_add]

theorem heavyMass_total_sum (v : Fin 5) :
    (∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j)) =
      ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k := by
  simp only [D.heavyMass_first_sum]

theorem indexed_heavy_mass_sum_le_one (v : Fin 5) :
    (∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j)) ≤ 1 := by
  rw [D.heavyMass_total_sum]
  exact G.sum_subtwoHeavyClassMass_le_one _ _ D.n_pos _

theorem indexed_singleton_cost_lower (v : Fin 5) (i : Fin 4) :
    (1 / 2 : ℝ) * (∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j)) ≤
      D.bundleCost (subtwoFivePairIndex v (v.succAbove i)) := by
  rw [D.heavyMass_first_sum, D.bundleCost_incident]
  exact G.subtwo_heavy_class_singleton_lower _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) (D.bin v) (D.bin_load v) i

theorem indexed_full_star_cost_row (v : Fin 5) :
    (∑ a : Fin 4, D.bundleCost (subtwoFivePairIndex v (v.succAbove a))) -
      (23 / 84 : ℝ) * (∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j)) ≤ 17 / 12 := by
  simp only [D.bundleCost_incident]
  rw [D.heavyMass_total_sum]
  exact G.subtwo_heavy_class_full_star_row _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) D.n_pos (D.bin v) (D.bin_load v)

theorem demandPrice_incident (v : Fin 5) (a : Fin 4) :
    D.demandPrice (subtwoFivePairIndex v (v.succAbove a)) =
      G.subtwoPhysicalBundlePrice n D.price (D.vertex v) (D.neighbor v a) :=
  D.demandPrice_pairIndex v (v.succAbove a) (subtwoFiveNeighbor_ne v a)

theorem bigSmallPrice_diagonal (v : Fin 5) (i : Fin 4) :
    G.subtwoHeavyBigPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i i = 0 ∧
      G.subtwoHeavySmallPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i i = 0 := by
  obtain ⟨hb, hs⟩ := G.subtwoHeavyBigSmallPrice_nonneg _ _ _ D.price D.price_nonneg D.price_max_pos i i
  have h := G.subtwoHeavyBigSmallPrice_add_le_mass _ _ (D.neighbor_injective v) (D.neighbor_ne v)
    (D.bin v) (D.bin_load v) D.price D.price_nonneg D.price_max_pos i i
  rw [G.subtwoHeavyClassMass_self] at h
  constructor <;> linarith

theorem bigPrice_total_sum (v : Fin 5) :
    (∑ i : Fin 4, ∑ j : Fin 3, D.bigPrice (subtwoFiveClassIndex v i j)) =
      ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavyBigPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i k := by
  simp only [D.bigPrice_classIndex]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.sum_univ_succAbove
    (fun k => G.subtwoHeavyBigPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i k) i,
    (D.bigSmallPrice_diagonal v i).1, zero_add]

theorem smallPrice_total_sum (v : Fin 5) :
    (∑ i : Fin 4, ∑ j : Fin 3, D.smallPrice (subtwoFiveClassIndex v i j)) =
      ∑ i : Fin 4, ∑ k : Fin 4, G.subtwoHeavySmallPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i k := by
  simp only [D.smallPrice_classIndex]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.sum_univ_succAbove
    (fun k => G.subtwoHeavySmallPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i k) i,
    (D.bigSmallPrice_diagonal v i).2, zero_add]

theorem indexed_star_half_price_row (v : Fin 5) :
    (∑ a : Fin 4, D.demandPrice (subtwoFivePairIndex v (v.succAbove a))) ≤
      ((1 / 2 : ℝ) * ∑ a : Fin 4, D.pairPrice (subtwoFivePairIndex v (v.succAbove a))) *
        (1 - ∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j)) +
      (∑ i : Fin 4, ∑ j : Fin 3, D.bigPrice (subtwoFiveClassIndex v i j)) +
      (∑ i : Fin 4, ∑ j : Fin 3, D.smallPrice (subtwoFiveClassIndex v i j)) := by
  simp only [D.demandPrice_incident, D.pairPrice_incident]
  rw [D.heavyMass_total_sum, D.bigPrice_total_sum, D.smallPrice_total_sum]
  exact G.subtwo_physical_star_half_price_row _ _ (D.neighbor_ne v) D.n_pos
    (D.bin v) (D.bin_load v) D.price D.price_nonneg D.price_max_pos

theorem indexed_heavy_big_pair_caps (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.bigPrice (subtwoFiveClassIndex v i j) ≤ D.heavyMass (subtwoFiveClassIndex v i j) *
      (D.pairPrice (subtwoFivePairIndex v (v.succAbove i)) +
        (1 / 2 : ℝ) * D.pairPrice (subtwoFivePairIndex v (v.succAbove (i.succAbove j)))) := by
  rw [D.bigPrice_classIndex, D.heavyMass_classIndex, D.pairPrice_incident, D.pairPrice_incident]
  exact G.subtwoHeavyBigPrice_le_pair_caps _ _ (D.neighbor_injective v) (D.neighbor_ne v)
    (D.bin v) (D.bin_load v) D.price D.price_nonneg D.price_max_pos _ _

theorem indexed_heavy_big_small_le_mass (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.bigPrice (subtwoFiveClassIndex v i j) + D.smallPrice (subtwoFiveClassIndex v i j) ≤
      D.heavyMass (subtwoFiveClassIndex v i j) := by
  rw [D.bigPrice_classIndex, D.smallPrice_classIndex, D.heavyMass_classIndex]
  exact G.subtwoHeavyBigSmallPrice_add_le_mass _ _ (D.neighbor_injective v) (D.neighbor_ne v)
    (D.bin v) (D.bin_load v) D.price D.price_nonneg D.price_max_pos _ _

theorem indexed_heavy_small_complement (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    3 * D.smallPrice (subtwoFiveClassIndex v i j) +
      D.heavyMass (subtwoFiveClassIndex v i j) *
        D.pairPrice (subtwoFivePairIndex (v.succAbove i) (v.succAbove (i.succAbove j))) ≤
      D.heavyMass (subtwoFiveClassIndex v i j) := by
  have hi : i ≠ i.succAbove j := (Fin.succAbove_ne i j).symm
  have hne : v.succAbove i ≠ v.succAbove (i.succAbove j) := fun he =>
    hi ((subtwoFiveNeighbor_injective v) he)
  rw [D.smallPrice_classIndex, D.heavyMass_classIndex,
    D.pairPrice_pairIndex _ _ hne]
  exact G.subtwoHeavySmallPrice_three_copies_complement _ _ (D.neighbor_injective v) (D.neighbor_ne v)
    (D.bin v) (D.bin_load v) D.price D.price_max_pos _ _

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
