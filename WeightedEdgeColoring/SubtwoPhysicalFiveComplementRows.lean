import WeightedEdgeColoring.SubtwoPhysicalFivePriceRows

/-!
# The fixed complementary pair and avoiding rows in a five-block

The two remaining neighbor indices are explicit, so the price in each
complement row is exactly one of the ten archived pair coordinates.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}

def subtwoFourOtherFirst (i : Fin 4) (j : Fin 3) : Fin 4 := i.succAbove (j.succAbove 0)
def subtwoFourOtherSecond (i : Fin 4) (j : Fin 3) : Fin 4 := i.succAbove (j.succAbove 1)

theorem subtwoFourOther_ne (i : Fin 4) (j : Fin 3) :
    subtwoFourOtherFirst i j ≠ subtwoFourOtherSecond i j := by
  have h : ∀ i : Fin 4, ∀ j : Fin 3,
      subtwoFourOtherFirst i j ≠ subtwoFourOtherSecond i j := by decide
  exact h i j

theorem subtwoOtherTwoIndices_eq_fixed_pair (i : Fin 4) (j : Fin 3) :
    subtwoOtherTwoIndices i (i.succAbove j) =
      {subtwoFourOtherFirst i j, subtwoFourOtherSecond i j} := by
  have h : ∀ i : Fin 4, ∀ j : Fin 3,
      subtwoOtherTwoIndices i (i.succAbove j) =
        {subtwoFourOtherFirst i j, subtwoFourOtherSecond i j} := by decide
  exact h i j

namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

def complementaryPairIndex (v : Fin 5) (i : Fin 4) (j : Fin 3) : Fin 10 :=
  subtwoFivePairIndex (v.succAbove (subtwoFourOtherFirst i j))
    (v.succAbove (subtwoFourOtherSecond i j))

theorem pairPrice_complementaryPairIndex (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.pairPrice (complementaryPairIndex v i j) =
      G.subtwoNormalizedSetPrice D.price
        ((subtwoOtherTwoIndices i (i.succAbove j)).image (D.neighbor v)) := by
  unfold complementaryPairIndex
  rw [D.pairPrice_pairIndex _ _ (fun he => subtwoFourOther_ne i j
    ((subtwoFiveNeighbor_injective v) he)), subtwoOtherTwoIndices_eq_fixed_pair]
  simp only [Finset.image_insert, Finset.image_singleton, neighbor]

theorem indexed_heavy_big_complement_pair (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.bigPrice (subtwoFiveClassIndex v i j) +
      D.pairPrice (complementaryPairIndex v i j) *
        D.heavyMass (subtwoFiveClassIndex v i j) ≤ D.heavyMass (subtwoFiveClassIndex v i j) := by
  rw [D.pairPrice_complementaryPairIndex, mul_comm]
  exact D.indexed_heavy_big_complement v i j

theorem indexed_heavy_small_quarter_pair (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.smallPrice (subtwoFiveClassIndex v i j) ≤
      (1 / 4 : ℝ) * (D.pairPrice (subtwoFivePairIndex v (v.succAbove (subtwoFourOtherFirst i j))) +
        D.pairPrice (subtwoFivePairIndex v (v.succAbove (subtwoFourOtherSecond i j)))) *
          D.heavyMass (subtwoFiveClassIndex v i j) := by
  have h := D.indexed_heavy_small_quarter v i j
  rw [subtwoOtherTwoIndices_eq_fixed_pair, Finset.sum_pair (subtwoFourOther_ne i j)] at h
  nlinarith

theorem indexed_small_box_cap_of_pair_box (U : Fin 10 → ℝ)
    (hU : ∀ e, D.pairPrice e ≤ U e) (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.smallPrice (subtwoFiveClassIndex v i j) ≤ (11 / 30 : ℝ) *
      max (U (subtwoFivePairIndex v (v.succAbove (subtwoFourOtherFirst i j))))
        (U (subtwoFivePairIndex v (v.succAbove (subtwoFourOtherSecond i j)))) *
      D.heavyMass (subtwoFiveClassIndex v i j) := by
  apply D.indexed_heavy_small_box_cap
  intro a ha
  rw [subtwoOtherTwoIndices_eq_fixed_pair] at ha
  have hp := ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  obtain rfl | rfl := hp
  · exact (hU _).trans (le_max_left _ _)
  · exact (hU _).trans (le_max_right _ _)

theorem indexed_avoiding_pair_row (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.avoidingLoss v - D.exteriorCharge v +
      D.pairPrice (subtwoFivePairIndex (v.succAbove i) (v.succAbove (i.succAbove j))) *
        D.exteriorCharge v +
      D.pairPrice (complementaryPairIndex v i j) * D.exteriorCharge v ≤ 0 := by
  have hne : v.succAbove i ≠ v.succAbove (i.succAbove j) := fun he =>
    (Fin.succAbove_ne i j).symm ((subtwoFiveNeighbor_injective v) he)
  rw [D.pairPrice_pairIndex _ _ hne, D.pairPrice_complementaryPairIndex,
    subtwoOtherTwoIndices_eq_fixed_pair]
  simp only [Finset.image_insert, Finset.image_singleton]
  have hd : Disjoint ({i, i.succAbove j} : Finset (Fin 4))
      {subtwoFourOtherFirst i j, subtwoFourOtherSecond i j} := by
    rw [← subtwoOtherTwoIndices_eq_fixed_pair]
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hp := ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    obtain rfl | rfl := hp
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1 rfl
    · exact (Finset.mem_erase.mp hb).1 rfl
  have hdn : Disjoint (({i, i.succAbove j} : Finset (Fin 4)).image (D.neighbor v))
      (({subtwoFourOtherFirst i j, subtwoFourOtherSecond i j} : Finset (Fin 4)).image (D.neighbor v)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hw
    exact Finset.disjoint_left.mp hd ha ((D.neighbor_injective v he) ▸ hb)
  have hdv : D.vertex v ∉ ({D.neighbor v i, D.neighbor v (i.succAbove j)} : Finset G.V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨D.neighbor_ne v i, D.neighbor_ne v _⟩
  have hdw : D.vertex v ∉ ({D.neighbor v (subtwoFourOtherFirst i j),
      D.neighbor v (subtwoFourOtherSecond i j)} : Finset G.V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨D.neighbor_ne v _, D.neighbor_ne v _⟩
  simpa only [Finset.image_insert, Finset.image_singleton, avoidingLoss, neighbor] using
    G.subtwo_physical_avoiding_matching_row (D.exteriorCharge v) (D.exteriorCharge_nonneg v)
      D.price D.price_max_pos
      (({i, i.succAbove j} : Finset (Fin 4)).image (D.neighbor v))
      (({subtwoFourOtherFirst i j, subtwoFourOtherSecond i j} : Finset (Fin 4)).image (D.neighbor v))
      hdn (D.vertex v)
      (by simpa only [Finset.image_insert, Finset.image_singleton] using hdv)
      (by simpa only [Finset.image_insert, Finset.image_singleton] using hdw)

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
