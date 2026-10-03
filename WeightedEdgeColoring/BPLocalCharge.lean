import WeightedEdgeColoring.HarmonicBinCharge
import WeightedEdgeColoring.WeightedMultigraph

/-!
# Lifting a one-bin charge bound to all vertex stars

The bin-packing arguments first prove that every unit bin has charge at most
`Q`.  This file records the exact finite step which applies that estimate to
the `n` bins in a local packing of a vertex star.  The result is stated for an
arbitrary charge function and then specialized to harmonic charge.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- Total charge incident with one vertex. -/
noncomputable def starCharge (charge : ℝ → ℝ) (v : G.V) : ℝ :=
  ∑ e : G.StarEdge v, charge (G.weight e.1)

/-- A charge bound for one unit bin lifts to a charge bound for every
explicit local packing. -/
theorem starCharge_le_mul_of_packsStarInto
    (charge : ℝ → ℝ) (Q : ℝ) {v : G.V} {n : ℕ}
    (hpack : G.PacksStarInto v n)
    (hone : ∀ S : Finset (G.StarEdge v),
      (∑ e ∈ S, G.weight e.1) ≤ 1 →
      (∑ e ∈ S, charge (G.weight e.1)) ≤ Q) :
    G.starCharge charge v ≤ (n : ℝ) * Q := by
  classical
  rcases hpack with ⟨bin, hbin⟩
  have hcolor (i : Fin n) :
      (∑ e : G.StarEdge v,
          if bin e = i then charge (G.weight e.1) else 0) ≤ Q := by
    let S : Finset (G.StarEdge v) :=
      Finset.univ.filter fun e ↦ bin e = i
    have hload : (∑ e ∈ S, G.weight e.1) ≤ 1 := by
      simpa [S, starBinLoad, ← Finset.sum_filter] using hbin i
    have hcharge := hone S hload
    simpa [S, ← Finset.sum_filter] using hcharge
  calc
    G.starCharge charge v =
        ∑ i : Fin n, ∑ e : G.StarEdge v,
          if bin e = i then charge (G.weight e.1) else 0 := by
      simp only [starCharge]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      simp
    _ ≤ ∑ _i : Fin n, Q :=
      Finset.sum_le_sum fun i _hi ↦ hcolor i
    _ = (n : ℝ) * Q := by simp

/-- Harmonic charge at a vertex is at most `h∞` times the number of bins
in any explicit packing of that star. -/
theorem harmonicStarCharge_le_of_packsStarInto {v : G.V} {n : ℕ}
    (hpack : G.PacksStarInto v n) :
    G.starCharge harmonicCharge v ≤
      (n : ℝ) * harmonicBinPackingConstant := by
  apply G.starCharge_le_mul_of_packsStarInto harmonicCharge
    harmonicBinPackingConstant hpack
  intro S hload
  exact harmonicCharge_sum_le_harmonicBinPackingConstant S
    (fun e ↦ G.weight e.1)
    (fun e _he ↦ G.weight_pos e.1) hload

/-- In particular, the harmonic charge at every vertex is at most
`h∞ * bp(G)`. -/
theorem harmonicStarCharge_le_bp (v : G.V) :
    G.starCharge harmonicCharge v ≤
      (G.bp : ℝ) * harmonicBinPackingConstant :=
  G.harmonicStarCharge_le_of_packsStarInto (G.locallyPacksInto_bp v)

end WeightedMultigraph
end WeightedEdgeColoring
