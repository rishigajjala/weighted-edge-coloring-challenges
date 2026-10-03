import WeightedEdgeColoring.SubtwoPhysicalBoundaryBins
import WeightedEdgeColoring.SubtwoAveragedPotential
import WeightedEdgeColoring.SubtwoLoadOrder

/-!
# The boundary-potential row for actual graph packings

The costs are the chosen minimum bundle costs, the boundary charge is
the charge of physical exterior edges, and every profile comes from the
same original star packing.  Each bin's first two coordinates are chosen
by the proved finite ordering construction.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

noncomputable section
universe u
variable (G : WeightedMultigraph.{u})

def subtwoOrderedFourLoads (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) (i : Fin 4) : ℝ :=
  G.subtwoPhysicalFourLoads v neighbor bin j
    (SubtwoHarmonicRanks.fourLoadOrder (G.subtwoPhysicalFourLoads v neighbor bin j) i)

theorem subtwoOrderedFourLoads_sum (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) :
    (∑ i, G.subtwoOrderedFourLoads v neighbor bin j i) =
      ∑ i, G.subtwoPhysicalFourLoads v neighbor bin j i :=
  Equiv.sum_comp _ _

theorem subtwoOrderedFourLoads_charge_sum (v : G.V) (neighbor : Fin 4 → G.V) {n : ℕ}
    (bin : G.StarEdge v → Fin n) (j : Fin n) :
    (∑ i, harmonicCharge (G.subtwoOrderedFourLoads v neighbor bin j i)) =
      ∑ i, harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j i) :=
  Equiv.sum_comp (SubtwoHarmonicRanks.fourLoadOrder
    (G.subtwoPhysicalFourLoads v neighbor bin j))
    (fun i => harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j i))

/-- The unpriced potential row, completely instantiated with actual local
star bins, minimum bundle costs, and physical exterior harmonic charge. -/
theorem subtwo_physical_boundary_potential
    (v : G.V) (neighbor : Fin 4 → G.V)
    (hinj : Function.Injective neighbor) (hne : ∀ i, v ≠ neighbor i)
    (external : Finset G.E)
    (hdisj : ∀ i, Disjoint (G.floorBundle (G.floorPairKey v (neighbor i))) external)
    {n : ℕ} (hn : 0 < n) (bin : G.StarEdge v → Fin n)
    (hbin : ∀ j, G.starBinLoad bin j ≤ 1) :
    let heavy := fun j => ∃ i, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i
    let w := G.subtwoOrderedFourLoads v neighbor bin
    (∑ j : Fin n, if heavy j then (1 / (n : ℝ)) *
      (harmonicCharge (w j 2) + harmonicCharge (w j 3)) else 0) +
      (3 / 2 : ℝ) * (∑ i : Fin 4, (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n) +
      (2 / 3 : ℝ) * ((∑ e ∈ external, if G.Inc v e then harmonicCharge (G.weight e) else 0) / n) ≤
      (111 / 52 : ℝ) + (893 / 1430 : ℝ) *
        ∑ j : Fin n, if heavy j then (1 / (n : ℝ)) else 0 := by
  classical
  apply SubtwoHarmonicRanks.averaged_boundary_potential
    (fun _ : Fin n => 1 / (n : ℝ)) (G.subtwoOrderedFourLoads v neighbor bin)
    (G.subtwoStarProjectionCharge external bin)
    (fun j => ∃ i, 1 / 2 < G.subtwoPhysicalFourLoads v neighbor bin j i)
    (∑ i : Fin 4, (G.floorBundleCover (G.floorPairKey v (neighbor i))).cost / n)
    ((∑ e ∈ external, if G.Inc v e then harmonicCharge (G.weight e) else 0) / n)
    (fun _ => by positivity) (le_of_eq (subtwo_uniform_bin_mass_sum hn))
  · intro j i
    exact G.subtwoPhysicalFourLoads_nonneg v neighbor bin j _
  · exact G.subtwoStarProjectionCharge_nonneg external bin
  · intro j hj i
    exact le_of_not_gt (fun h => hj ⟨_, h⟩)
  · intro j hj
    exact SubtwoHarmonicRanks.fourLoadOrder_heavy _ hj
  · intro j hj
    exact SubtwoHarmonicRanks.fourLoadOrder_second _
  · intro j
    rw [G.subtwoOrderedFourLoads_sum]
    exact G.subtwoPhysicalFourLoads_boundary_capacity v neighbor hinj hne external hdisj bin hbin j
  · have hc := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
      (fun i _ => G.subtwo_floorBundle_normalized_cost_le_local_charge v (neighbor i) (hne i) hn bin hbin)
    rw [Finset.sum_comm] at hc
    calc
      _ ≤ ∑ j : Fin n, ∑ i : Fin 4, (1 / (n : ℝ)) *
          harmonicCharge (G.subtwoPhysicalFourLoads v neighbor bin j i) := hc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum, G.subtwoOrderedFourLoads_charge_sum]
  · apply le_of_eq
    rw [← Finset.mul_sum, G.sum_subtwoStarProjectionCharge]
    ring

end
end WeightedEdgeColoring.WeightedMultigraph
