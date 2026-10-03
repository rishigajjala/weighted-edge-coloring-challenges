import WeightedEdgeColoring.SubtwoPhysicalFiveLiftedRows

/-!
# Pair and heavy-class indices in the physical certificate vector

The two index maps enumerate pairs and heavy classes in lexicographic order.
The proofs below identify their observables with
the actual incident bundles and the chosen heavy classes.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}

def subtwoFivePairIndex (a b : Fin 5) : Fin 10 :=
  let l := min a.val b.val
  let r := max a.val b.val
  ⟨(5 * l - l * (l + 1) / 2 + (r - l - 1)) % 10, by omega⟩

theorem subtwoFivePairIndex_endpoints (a b : Fin 5) (hab : a ≠ b) :
    ((subtwoFivePair (subtwoFivePairIndex a b)).1 = a ∧
      (subtwoFivePair (subtwoFivePairIndex a b)).2 = b) ∨
    ((subtwoFivePair (subtwoFivePairIndex a b)).1 = b ∧
      (subtwoFivePair (subtwoFivePairIndex a b)).2 = a) := by
  have h : ∀ a b : Fin 5, a ≠ b →
      ((subtwoFivePair (subtwoFivePairIndex a b)).1 = a ∧
        (subtwoFivePair (subtwoFivePairIndex a b)).2 = b) ∨
      ((subtwoFivePair (subtwoFivePairIndex a b)).1 = b ∧
        (subtwoFivePair (subtwoFivePairIndex a b)).2 = a) := by decide
  exact h a b hab

def subtwoFiveClassIndex (v : Fin 5) (i : Fin 4) (j : Fin 3) : Fin 60 :=
  ⟨12 * v.val + 3 * i.val + j.val, by omega⟩

theorem subtwoFiveClassVertex_index (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    subtwoFiveClassVertex (subtwoFiveClassIndex v i j) = v := by
  apply Fin.ext
  change (12 * v.val + 3 * i.val + j.val) / 12 = v.val
  omega

theorem subtwoFiveClassFirst_index (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    subtwoFiveClassFirst (subtwoFiveClassIndex v i j) = i := by
  apply Fin.ext
  change ((12 * v.val + 3 * i.val + j.val) % 12) / 3 = i.val
  omega

theorem subtwoFiveClassSecond_index (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    subtwoFiveClassSecond (subtwoFiveClassIndex v i j) = i.succAbove j := by
  unfold subtwoFiveClassSecond
  rw [subtwoFiveClassFirst_index]
  apply congrArg i.succAbove
  apply Fin.ext
  change (12 * v.val + 3 * i.val + j.val) % 3 = j.val
  omega

theorem subtwo_floorPairKey_comm (a b : G.V) : G.floorPairKey a b = G.floorPairKey b a := by
  unfold floorPairKey
  by_cases h : G.floorVertexCode a < G.floorVertexCode b
  · have hn : ¬G.floorVertexCode b < G.floorVertexCode a := by omega
    simp [h, hn]
  · by_cases heq : a = b
    · subst b
      rfl
    · have hcode : G.floorVertexCode a ≠ G.floorVertexCode b := fun hc =>
        heq (G.floorVertexCode.injective hc)
      have hr : G.floorVertexCode b < G.floorVertexCode a := by omega
      simp [h, hr]

namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem pairPrice_pairIndex (a b : Fin 5) (hab : a ≠ b) :
    D.pairPrice (subtwoFivePairIndex a b) =
      G.subtwoNormalizedSetPrice D.price {D.vertex a, D.vertex b} := by
  unfold pairPrice
  obtain h | h := subtwoFivePairIndex_endpoints a b hab
  · rw [h.1, h.2]
  · rw [h.1, h.2, Finset.pair_comm]

theorem bundleCost_pairIndex (a b : Fin 5) (hab : a ≠ b) :
    D.bundleCost (subtwoFivePairIndex a b) = G.subtwoPhysicalBundleCost n (D.vertex a) (D.vertex b) := by
  unfold bundleCost subtwoPhysicalBundleCost
  obtain h | h := subtwoFivePairIndex_endpoints a b hab
  · rw [h.1, h.2]
  · rw [h.1, h.2, subtwo_floorPairKey_comm (D.vertex b) (D.vertex a)]

theorem demandPrice_pairIndex (a b : Fin 5) (hab : a ≠ b) :
    D.demandPrice (subtwoFivePairIndex a b) =
      G.subtwoPhysicalBundlePrice n D.price (D.vertex a) (D.vertex b) := by
  unfold demandPrice subtwoPhysicalBundlePrice
  obtain h | h := subtwoFivePairIndex_endpoints a b hab
  · rw [h.1, h.2]
  · rw [h.1, h.2, subtwo_floorPairKey_comm (D.vertex b) (D.vertex a)]

theorem bundleCost_incident (v : Fin 5) (a : Fin 4) :
    D.bundleCost (subtwoFivePairIndex v (v.succAbove a)) =
      G.subtwoPhysicalBundleCost n (D.vertex v) (D.neighbor v a) :=
  D.bundleCost_pairIndex v (v.succAbove a) (subtwoFiveNeighbor_ne v a)

theorem pairPrice_incident (v : Fin 5) (a : Fin 4) :
    D.pairPrice (subtwoFivePairIndex v (v.succAbove a)) =
      G.subtwoNormalizedSetPrice D.price {D.vertex v, D.neighbor v a} :=
  D.pairPrice_pairIndex v (v.succAbove a) (subtwoFiveNeighbor_ne v a)

theorem heavyMass_classIndex (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.heavyMass (subtwoFiveClassIndex v i j) =
      G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i (i.succAbove j) := by
  unfold heavyMass
  rw [subtwoFiveClassVertex_index, subtwoFiveClassFirst_index, subtwoFiveClassSecond_index]

theorem bigPrice_classIndex (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.bigPrice (subtwoFiveClassIndex v i j) =
      G.subtwoHeavyBigPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i (i.succAbove j) := by
  unfold bigPrice
  rw [subtwoFiveClassVertex_index, subtwoFiveClassFirst_index, subtwoFiveClassSecond_index]

theorem smallPrice_classIndex (v : Fin 5) (i : Fin 4) (j : Fin 3) :
    D.smallPrice (subtwoFiveClassIndex v i j) =
      G.subtwoHeavySmallPrice (D.vertex v) (D.neighbor v) (D.bin v) D.price i (i.succAbove j) := by
  unfold smallPrice
  rw [subtwoFiveClassVertex_index, subtwoFiveClassFirst_index, subtwoFiveClassSecond_index]

/-- Weighted class sums in the twelve encoded coordinates have exactly
the same meaning as the physical sixteen-index sum with zero diagonal. -/
theorem weighted_heavyMass_classIndex (v : Fin 5) (f : Fin 4 → Fin 4 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j) * f i (i.succAbove j)) =
      ∑ i : Fin 4, ∑ k : Fin 4,
        G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k * f i k := by
  simp only [D.heavyMass_classIndex]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.sum_univ_succAbove
    (fun k => G.subtwoHeavyClassMass (D.vertex v) (D.neighbor v) (D.bin v) i k * f i k) i]
  rw [G.subtwoHeavyClassMass_self, zero_mul, zero_add]

/-- The physical subset cost row now refers to the exact pair and
heavy-class indices of the actual five-block vector. -/
theorem indexed_subset_cost_row (v : Fin 5) (I : Finset (Fin 4)) :
    (∑ a ∈ I, D.bundleCost (subtwoFivePairIndex v (v.succAbove a))) +
      (∑ i : Fin 4, ∑ j : Fin 3, D.heavyMass (subtwoFiveClassIndex v i j) *
        (SubtwoHarmonicRanks.normalRank I.card - SubtwoHarmonicRanks.heavySubsetRank I i (i.succAbove j))) ≤
      SubtwoHarmonicRanks.normalRank I.card := by
  simp only [D.bundleCost_incident]
  rw [D.weighted_heavyMass_classIndex v
    (fun i k => SubtwoHarmonicRanks.normalRank I.card - SubtwoHarmonicRanks.heavySubsetRank I i k)]
  exact G.subtwo_physical_subset_cost_certificate_row (D.vertex v) (D.neighbor v)
    (D.neighbor_injective v) (D.neighbor_ne v) D.n_pos (D.bin v) (D.bin_load v) I

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
