import WeightedEdgeColoring.BPLocalCharge
import WeightedEdgeColoring.BPEdgeRestriction

/-!
# Interface for coloring from harmonic charge

The packet argument must turn a vertexwise harmonic-charge bound into a
global coloring, with an error controlled by an external scale `n`.  Keeping
that scale explicit is essential: an edge restriction may have small own
`bp`, even when it came from a large original graph.
-/

namespace WeightedEdgeColoring

universe u

/-- Uniform harmonic-charge coloring statement used by the sharp bipartite
bin-packing proof. -/
def BipartiteHarmonicChargeColoring : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ,
    ∀ (G : WeightedMultigraph.{u}) (n : ℕ) (A : ℝ),
      G.IsBipartite → N ≤ n → 0 ≤ A →
      (∀ v, G.starWeight v ≤ n) →
      (∀ v, G.starCharge harmonicCharge v ≤ A) →
      (G.chiW : ℝ) ≤ A + η * n

/-- The harmonic-charge interface immediately gives the first bipartite
`h∞ bp(G)` bound.  This theorem discharges the local-bin bookkeeping and all
coefficient algebra. -/
theorem bipartiteHarmonicBPAsymptotic_of_chargeColoring
    (hcolor : BipartiteHarmonicChargeColoring.{u}) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
      G.IsBipartite → N ≤ G.bp →
      (G.chiW : ℝ) ≤
        (harmonicBinPackingConstant + ε) * (G.bp : ℝ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hcolor ε hε
  refine ⟨N, ?_⟩
  intro G hbip hlarge
  have hstar : ∀ v, G.starWeight v ≤ (G.bp : ℝ) := by
    intro v
    exact G.starWeight_le_of_packsStarInto (G.locallyPacksInto_bp v)
  have hcharge : ∀ v,
      G.starCharge harmonicCharge v ≤
        (G.bp : ℝ) * harmonicBinPackingConstant :=
    G.harmonicStarCharge_le_bp
  have hA : 0 ≤ (G.bp : ℝ) * harmonicBinPackingConstant :=
    mul_nonneg (Nat.cast_nonneg _) harmonicBinPackingConstant_nonneg
  have h := hN G G.bp
    ((G.bp : ℝ) * harmonicBinPackingConstant)
    hbip hlarge hA hstar hcharge
  calc
    (G.chiW : ℝ) ≤
        (G.bp : ℝ) * harmonicBinPackingConstant + ε * G.bp := h
    _ = (harmonicBinPackingConstant + ε) * (G.bp : ℝ) := by ring

end WeightedEdgeColoring
