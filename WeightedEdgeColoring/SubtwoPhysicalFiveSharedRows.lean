import WeightedEdgeColoring.SubtwoPhysicalFiveComplementRows

/-!
# Shared incident-pair rows in the twelve heavy-class coordinates

The same fixed complementary price multiplies the mass of each heavy
class. The reindexing below also removes the zero diagonal classes.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}

def subtwoSharedPairFactor (I : Finset (Fin 4)) (i k : Fin 4) : ℝ :=
  (if i ∉ I then 1 / 2 else 0) + (if i ∉ I ∧ k ∉ I then 1 / 6 else 0)

theorem subtwoFour_complement_pair (i : Fin 4) (j : Fin 3) :
    (Finset.univ \ ({i, i.succAbove j} : Finset (Fin 4))) =
      subtwoOtherTwoIndices i (i.succAbove j) := by
  have h : ∀ i : Fin 4, ∀ j : Fin 3,
      (Finset.univ \ ({i, i.succAbove j} : Finset (Fin 4))) =
        subtwoOtherTwoIndices i (i.succAbove j) := by decide
  exact h i j

namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem indexed_shared_price_row (v : Fin 5) (I : Finset (Fin 4)) :
    let m := G.subtwoNormalizedSetPrice D.price ((Finset.univ \ I).image (D.neighbor v))
    (∑ a ∈ I, D.demandPrice (subtwoFivePairIndex v (v.succAbove a))) + m +
      (∑ i : Fin 4, ∑ j : Fin 3,
        (subtwoSharedPairFactor I i (i.succAbove j) * D.heavyMass (subtwoFiveClassIndex v i j) -
          subtwoSharedPairFactor I i (i.succAbove j) * (m * D.heavyMass (subtwoFiveClassIndex v i j)))) ≤ 1 := by
  dsimp only
  let m := G.subtwoNormalizedSetPrice D.price ((Finset.univ \ I).image (D.neighbor v))
  have hs :
      (∑ i : Fin 4, ∑ j : Fin 3,
        (subtwoSharedPairFactor I i (i.succAbove j) * D.heavyMass (subtwoFiveClassIndex v i j) -
          subtwoSharedPairFactor I i (i.succAbove j) * (m * D.heavyMass (subtwoFiveClassIndex v i j)))) =
      ∑ i : Fin 4, ∑ k : Fin 4,
        (subtwoSharedPairFactor I i k * G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k -
          subtwoSharedPairFactor I i k * (m * G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k)) := by
    calc
      _ = ∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j) *
          (subtwoSharedPairFactor I i (i.succAbove j) * (1 - m)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i : Fin 4, ∑ k : Fin 4,
          G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k *
            (subtwoSharedPairFactor I i k * (1 - m)) :=
        D.weighted_heavyMass_classIndex v (fun i k => subtwoSharedPairFactor I i k * (1 - m))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        ring
  change _ + m + _ ≤ 1
  rw [hs]
  simp only [D.demandPrice_incident, subtwoSharedPairFactor]
  exact G.subtwo_physical_shared_pair_certificate_row _ _ (D.neighbor_injective v)
    (D.neighbor_ne v) D.n_pos (D.bin v) (D.bin_load v) D.price D.price_nonneg D.price_max_pos I

theorem indexed_shared_incident_pair_row (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.demandPrice (subtwoFivePairIndex v (v.succAbove i)) +
      D.demandPrice (subtwoFivePairIndex v (v.succAbove (i.succAbove j))) +
      D.pairPrice (complementaryPairIndex v i j) +
      (∑ a : Fin 4, ∑ b : Fin 3,
        (subtwoSharedPairFactor {i, i.succAbove j} a (a.succAbove b) *
            D.heavyMass (subtwoFiveClassIndex v a b) -
          subtwoSharedPairFactor {i, i.succAbove j} a (a.succAbove b) *
            (D.pairPrice (complementaryPairIndex v i j) * D.heavyMass (subtwoFiveClassIndex v a b)))) ≤ 1 := by
  rw [D.pairPrice_complementaryPairIndex]
  have h := D.indexed_shared_price_row v {i, i.succAbove j}
  dsimp only at h
  rw [Finset.sum_pair (Fin.succAbove_ne i j).symm, subtwoFour_complement_pair] at h
  exact h

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
