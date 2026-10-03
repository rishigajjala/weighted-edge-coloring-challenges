import WeightedEdgeColoring.BPHarmonicColoringInterface
import WeightedEdgeColoring.BPGeneralPacketSlack
import WeightedEdgeColoring.MainTheorems

/-!
# Bipartite coloring from total incident weight

Harmonic charge of an edge is at most twice its weight. The uniform
harmonic-charge coloring theorem therefore yields the coefficient-two
weighted-degree bound, with only the ceiling of the external scale to absorb.
-/

namespace WeightedEdgeColoring

universe u

/-- Uniform bipartite weighted-degree coloring follows from harmonic-charge
coloring. -/
theorem bipartiteMultigraphDeltaAsymptotic_of_harmonicChargeColoring
    (hcolor : BipartiteHarmonicChargeColoring.{u}) :
    BipartiteMultigraphDeltaAsymptotic.{u} := by
  intro ε hε
  obtain ⟨Ncharge, hchargeColor⟩ := hcolor (ε / 2) (half_pos hε)
  let N := max Ncharge 1
  refine ⟨N, ?_⟩
  intro G hbip hlarge
  let n := Nat.ceil G.deltaW
  have hn : Ncharge ≤ n := by
    have h : (Ncharge : ℝ) ≤ (n : ℝ) := by
      calc
        (Ncharge : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_left Ncharge 1
        _ ≤ G.deltaW := hlarge
        _ ≤ (n : ℝ) := Nat.le_ceil _
    exact_mod_cast h
  have hdelta : (1 : ℝ) ≤ G.deltaW := by
    calc
      (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_max_right Ncharge 1
      _ ≤ G.deltaW := hlarge
  have hstar (v : G.V) : G.starWeight v ≤ (n : ℝ) := by
    exact (G.starWeight_le_deltaW v).trans (Nat.le_ceil _)
  have hcharge (v : G.V) :
      G.starCharge harmonicCharge v ≤ 2 * G.deltaW := by
    calc
      G.starCharge harmonicCharge v ≤ 2 * G.starWeight v :=
        G.harmonicStarCharge_le_two_starWeight v
      _ ≤ 2 * G.deltaW :=
        mul_le_mul_of_nonneg_left (G.starWeight_le_deltaW v) (by norm_num)
  have hbase : (G.chiW : ℝ) ≤ 2 * G.deltaW + ε / 2 * (n : ℝ) :=
    hchargeColor G n (2 * G.deltaW) hbip hn
      (mul_nonneg (by norm_num) G.deltaW_nonneg) hstar hcharge
  have hceil : (n : ℝ) ≤ G.deltaW + 1 :=
    (Nat.ceil_lt_add_one G.deltaW_nonneg).le
  have hmul := mul_le_mul_of_nonneg_left hceil (by positivity : 0 ≤ ε / 2)
  have hmul' := mul_le_mul_of_nonneg_left hdelta (by positivity : 0 ≤ ε / 2)
  nlinarith

end WeightedEdgeColoring
