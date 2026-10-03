import WeightedEdgeColoring.BPGeneralPhysicalBundleCover
import WeightedEdgeColoring.BipartiteDegreeCriterion

/-!
# Ordinary degree at a reciprocal weight floor

For the finite core every physical edge has weight at least `1/S`.  An
`n`-bin local packing therefore contains at most `S n` incident physical
edges.  This estimate absorbs the fixed remainder paid once for each large
endpoint bundle.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- A bundle can always be packed by putting every physical edge in its own
bin.  Hence the minimum physical exact-cover cost is at most the bundle
cardinality. -/
theorem physicalBundleCover_cost_le_card (k : G.V × G.V) :
    (G.physicalBundleCover k).cost ≤ (G.floorBundle k).card := by
  obtain ⟨C, hCcost⟩ :=
    BinPackingInstance.exists_unitDemandExactPatternCover_cost_eq_of_packsInto
      (B := G.edgeSetBinPackingInstance (G.floorBundle k))
      (G.edgeSetBinPackingInstance (G.floorBundle k)).packsInto_card
  calc
    (G.physicalBundleCover k).cost ≤ C.cost :=
      G.physicalBundleCover_minimum k C
    _ = (G.floorBundle k).card := by
      rw [hCcost]
      simp [WeightedMultigraph.edgeSetBinPackingInstance]

theorem degreeOn_univ_le_mul_of_reciprocal_weight_floor
    {n S : ℕ} (hS : 0 < S)
    (hweight : ∀ e : G.E, (1 : ℝ) / S ≤ G.weight e)
    (hlocal : G.LocallyPacksInto n) (v : G.V) :
    G.degreeOn Finset.univ v ≤ n * S := by
  have hweighted := G.degreeOn_mul_le_restrictedWeight
    Finset.univ ((1 : ℝ) / S) (fun e _he ↦ hweight e) v
  have hstar := G.starWeight_le_of_packsStarInto (hlocal v)
  have htotal :
      (G.degreeOn Finset.univ v : ℝ) * ((1 : ℝ) / S) ≤ n := by
    calc
      _ ≤ ∑ e ∈ (Finset.univ : Finset G.E),
          if G.Inc v e then G.weight e else 0 := hweighted
      _ = G.starWeight v := by
        rw [G.starWeight_eq_inc_sum]
      _ ≤ n := hstar
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hreal : (G.degreeOn Finset.univ v : ℝ) ≤ (n : ℝ) * S := by
    calc
      (G.degreeOn Finset.univ v : ℝ) =
          ((G.degreeOn Finset.univ v : ℝ) * ((1 : ℝ) / S)) * S := by
        field_simp
      _ ≤ (n : ℝ) * S :=
        mul_le_mul_of_nonneg_right htotal hSR.le
  exact_mod_cast hreal

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.WeightedMultigraph.degreeOn_univ_le_mul_of_reciprocal_weight_floor
