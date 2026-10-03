import WeightedEdgeColoring.SubtwoPhysicalFiveDomainRows

/-!
# Physical price rows with the certificate's exact indices

The complement, small-price, sorted-star, and boundary-potential rows
refer to one common packing at each original vertex.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}
namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem indexed_heavy_big_complement (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.bigPrice (subtwoFiveClassIndex v i j) +
      D.heavyMass (subtwoFiveClassIndex v i j) *
        G.subtwoNormalizedSetPrice D.price
          ((subtwoOtherTwoIndices i (i.succAbove j)).image (D.neighbor v)) ≤
      D.heavyMass (subtwoFiveClassIndex v i j) := by
  rw [D.bigPrice_classIndex, D.heavyMass_classIndex]
  exact G.subtwoHeavyBigPrice_complement _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) (D.bin v) (D.bin_load v) D.price D.price_max_pos _ _

theorem indexed_heavy_small_quarter (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.smallPrice (subtwoFiveClassIndex v i j) ≤
      D.heavyMass (subtwoFiveClassIndex v i j) * ((1 / 4 : ℝ) *
        ∑ a ∈ subtwoOtherTwoIndices i (i.succAbove j),
          D.pairPrice (subtwoFivePairIndex v (v.succAbove a))) := by
  rw [D.smallPrice_classIndex, D.heavyMass_classIndex]
  simp only [D.pairPrice_incident]
  exact G.subtwoHeavySmallPrice_le_quarter_caps _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) (D.bin v) (D.bin_load v) D.price D.price_nonneg D.price_max_pos _ _

theorem indexed_heavy_small_box_cap (v : Fin 5) (i : Fin 4) (j : Fin 3)
    (sm : ℝ)
    (hsm : ∀ a ∈ subtwoOtherTwoIndices i (i.succAbove j),
      D.pairPrice (subtwoFivePairIndex v (v.succAbove a)) ≤ sm) :
    D.smallPrice (subtwoFiveClassIndex v i j) ≤
      (11 / 30 : ℝ) * sm * D.heavyMass (subtwoFiveClassIndex v i j) := by
  rw [D.smallPrice_classIndex, D.heavyMass_classIndex]
  have h := G.subtwoHeavySmallPrice_le_small_cap _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) (D.bin v) (D.bin_load v) D.price D.price_nonneg D.price_max_pos
    i (i.succAbove j) sm (by simpa only [D.pairPrice_incident] using hsm)
  nlinarith

theorem indexed_cross_price_cost_row (v : Fin 5) (i : Fin 4) (j : Fin 3)
    (sm : ℝ) (hsm0 : 0 ≤ sm)
    (hsm : ∀ a ∈ subtwoOtherTwoIndices i (i.succAbove j),
      D.pairPrice (subtwoFivePairIndex v (v.succAbove a)) ≤ sm) :
    D.smallPrice (subtwoFiveClassIndex v i j) +
      sm * D.bundleCost (subtwoFivePairIndex v (v.succAbove (i.succAbove j))) -
      (sm / 2) * (∑ a : Fin 3, D.heavyMass (subtwoFiveClassIndex v (i.succAbove j) a)) -
      (4 * sm / 21) * D.heavyMass (subtwoFiveClassIndex v i j) ≤ sm / 2 := by
  rw [D.smallPrice_classIndex, D.bundleCost_incident, D.heavyMass_first_sum,
    D.heavyMass_classIndex]
  exact G.subtwo_physical_cross_price_cost_row _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) D.n_pos (D.bin v) (D.bin_load v) D.price D.price_max_pos
    i (i.succAbove j) (Fin.succAbove_ne i j).symm sm hsm0
    (by simpa only [D.pairPrice_incident] using hsm)

theorem indexed_sorted_star_price_row (v : Fin 5) (π : Equiv.Perm (Fin 4))
    (U : Fin 4 → ℝ)
    (hU : ∀ a, D.pairPrice (subtwoFivePairIndex v (v.succAbove (π a))) ≤ U a)
    (h01 : U 1 ≤ U 0) (h12 : U 2 ≤ U 1) (h23 : U 3 ≤ U 2) (h3 : 0 ≤ U 3) :
    (∑ a : Fin 4, D.demandPrice (subtwoFivePairIndex v (v.succAbove a))) +
      min 1 (U 0 / 2 + U 1 / 2 + U 2 / 3 + U 3 / 12) *
        (∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j)) -
      (∑ i : Fin 4, ∑ j : Fin 3, D.bigPrice (subtwoFiveClassIndex v i j)) -
      (∑ i : Fin 4, ∑ j : Fin 3, D.smallPrice (subtwoFiveClassIndex v i j)) ≤
      min 1 (U 0 / 2 + U 1 / 2 + U 2 / 3 + U 3 / 12) := by
  simp only [D.demandPrice_incident]
  rw [D.heavyMass_total_sum, D.bigPrice_total_sum, D.smallPrice_total_sum]
  have h := G.subtwo_physical_star_sorted_price_row _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) D.n_pos (D.bin v) (D.bin_load v) D.price D.price_max_pos π U
    (by simpa only [D.pairPrice_incident] using hU) h01 h12 h23 h3
  nlinarith

theorem indexed_priced_boundary_potential (v : Fin 5) (sm : ℝ) (hsm0 : 0 ≤ sm)
    (hsm : ∀ a : Fin 4, D.pairPrice (subtwoFivePairIndex v (v.succAbove a)) ≤ sm) :
    (∑ i : Fin 4, ∑ j : Fin 3, D.smallPrice (subtwoFiveClassIndex v i j)) +
      (3 / 2 : ℝ) * sm * (∑ a : Fin 4, D.bundleCost (subtwoFivePairIndex v (v.succAbove a))) +
      (2 / 3 : ℝ) * sm * D.exteriorCharge v -
      (893 / 1430 : ℝ) * sm * (∑ i : Fin 4, ∑ j : Fin 3,
        D.heavyMass (subtwoFiveClassIndex v i j)) ≤ (111 / 52 : ℝ) * sm := by
  rw [D.smallPrice_total_sum, D.heavyMass_total_sum]
  simp only [D.bundleCost_incident, subtwoPhysicalBundleCost, exteriorCharge]
  exact G.subtwo_physical_priced_boundary_row D.vertexSet (D.vertex v)
    (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
    (D.neighbor v) (D.neighbor_injective v) (D.neighbor_ne v)
    (fun a => Finset.mem_image.mpr ⟨v.succAbove a, Finset.mem_univ _, rfl⟩)
    D.n_pos (D.bin v) (D.bin_load v) D.price D.price_max_pos sm hsm0
    (by simpa only [D.pairPrice_incident] using hsm)

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
