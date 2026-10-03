import WeightedEdgeColoring.SubtwoPhysicalPotential

/-!
# The potential inequality for the actual exterior of a block

The exterior set and its disjointness from the four internal bundles are
constructed from the graph endpoints. Thus the boundary variable here is
the same exterior harmonic charge used in block selection and restoration.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

def subtwoExteriorEdgeSet (S : Finset G.V) : Finset G.E :=
  Finset.univ.filter fun e => ¬(G.fst e ∈ S ∧ G.snd e ∈ S)

theorem subtwoExteriorEdgeSet_charge (S : Finset G.V) (v : G.V) :
    (∑ e ∈ G.subtwoExteriorEdgeSet S,
      if G.Inc v e then harmonicCharge (G.weight e) else 0) =
      G.subtwoExteriorHarmonicCharge S v := by
  classical
  unfold subtwoExteriorEdgeSet subtwoExteriorHarmonicCharge
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hi : G.Inc v e <;>
    by_cases hs : G.fst e ∈ S ∧ G.snd e ∈ S <;> simp [hi, hs]

theorem subtwo_floorBundle_disjoint_exterior
    (S : Finset G.V) {a b : G.V} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    Disjoint (G.floorBundle (G.floorPairKey a b)) (G.subtwoExteriorEdgeSet S) := by
  classical
  rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab]
  apply Finset.disjoint_left.mpr
  intro e he hx
  have hn := (Finset.mem_filter.mp hx).2
  rcases (Finset.mem_filter.mp he).2 with h | h
  · exact hn ⟨h.1 ▸ ha, h.2 ▸ hb⟩
  · exact hn ⟨h.1 ▸ hb, h.2 ▸ ha⟩

/-- Actual block version of the exact `111/52`, `893/1430` row. -/
theorem subtwo_exterior_boundary_potential
    (S : Finset G.V) (v : G.V) (hv : v ∈ S)
    (neighbor : Fin 4 → G.V) (hinj : Function.Injective neighbor)
    (hne : ∀ i, v ≠ neighbor i) (hmem : ∀ i, neighbor i ∈ S)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) :
    let heavy := fun j => ∃ i, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i
    let w := G.subtwoOrderedFourLoads v neighbor bin
    (∑ j : Fin n, if heavy j then (1 / (n : ℝ)) *
      (harmonicCharge (w j 2) + harmonicCharge (w j 3)) else 0) +
      (3 / 2 : ℝ) * (∑ i : Fin 4, (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n) +
      (2 / 3 : ℝ) * (G.subtwoExteriorHarmonicCharge S v / n) ≤
      (111 / 52 : ℝ) + (893 / 1430 : ℝ) *
        ∑ j : Fin n, if heavy j then (1 / (n : ℝ)) else 0 := by
  simpa only [G.subtwoExteriorEdgeSet_charge] using
    G.subtwo_physical_boundary_potential v neighbor hinj hne
      (G.subtwoExteriorEdgeSet S)
      (fun i => G.subtwo_floorBundle_disjoint_exterior S hv (hmem i) (hne i)) hn bin hbin

end
end WeightedEdgeColoring.WeightedMultigraph
