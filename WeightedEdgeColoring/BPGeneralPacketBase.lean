import WeightedEdgeColoring.BPGeneralPacketSlack

/-!
# The colored packet base for the general multigraph proof

This file composes the elementary odd-set bound with the standard
near-fractional ordinary edge-coloring input.  It colors a chosen set of
packets, expands their colors to the physical edges, and proves that every
vertex keeps the exact `2/5 n` missing-palette reserve needed for the short
residual.

The packet construction and the final support-preserving residual rounding
remain separate inputs.  No part of either is hidden here.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

/-- Assuming the standard near-fractional ordinary multigraph theorem, a
packet family with the charge identity and the triangle bound has a proper
packet coloring at the desired target.  Expanding it is feasible on all
physical full-packet edges and leaves the precise residual reserve. -/
theorem exists_chargeSensitivePacketBase
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    {G : WeightedMultigraph.{u}} (P : G.Packetization)
    (S : Finset P.Packet) (residualCharge : G.V → ℝ)
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (n : ℕ) (Q : ℝ),
      N ≤ n →
      0 ≤ Q → Q ≤ 2 * (n : ℝ) →
      (∀ v, 0 ≤ residualCharge v) →
      (∀ v, (P.groupedGraph.degreeOn S v : ℝ) + residualCharge v ≤ Q) →
      P.groupedGraph.TriangleEdgeCountAtMost S (2 * (n : ℝ)) →
      ∃ (K : ℕ) (base : P.Packet → Fin K),
        0 < K ∧
        max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) ≤ (K : ℝ) ∧
        (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 ∧
        P.groupedGraph.IsProperOn S base ∧
        G.IsFeasibleOn (P.originalEdgesOfPackets S) (P.expandColor base) ∧
        ∀ v, residualCharge v + (2 / 5 : ℝ) * n ≤
          ((G.missingColorsAt (P.originalEdgesOfPackets S)
            (P.expandColor base) v).card : ℝ) := by
  obtain ⟨N, hN⟩ := hordinary (5 / 2 : ℝ) η (by norm_num) hη
  refine ⟨N, ?_⟩
  intro n Q hn hQ0 hQ2 hres0 haccount htriangle
  let L : ℝ := max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact le_max_of_le_left (mul_nonneg (by norm_num) hn0)
  have hLupper : L ≤ (5 / 2 : ℝ) * n := by
    dsimp [L]
    apply max_le
    · nlinarith
    · nlinarith
  have hdegreeQ : ∀ v, (P.groupedGraph.degreeOn S v : ℝ) ≤ Q := by
    intro v
    have := haccount v
    have := hres0 v
    linarith
  have hdegreeL : ∀ v, (P.groupedGraph.degreeOn S v : ℝ) ≤ L := by
    intro v
    calc
      (P.groupedGraph.degreeOn S v : ℝ) ≤ Q := hdegreeQ v
      _ ≤ (5 / 4 : ℝ) * Q := by nlinarith
      _ ≤ L := le_max_right _ _
  have hodd : P.groupedGraph.OddSetDensityAtMost S L := by
    dsimp [L]
    exact P.groupedGraph.oddSetDensityAtMost_max_two_fiveFourth
      S (n : ℝ) Q hn0 hQ0 hdegreeQ htriangle
  obtain ⟨q, hq, hqBound, color, hproper⟩ :=
    hN P.groupedGraph S n L hn hL0 hLupper hdegreeL hodd
  obtain ⟨K, base, hK, hLK, hKupper, hbaseProper⟩ :=
    P.groupedGraph.exists_padded_properColoring
      S n q L η hL0 hη.le hq hqBound color hproper
  refine ⟨K, base, hK, hLK, hKupper, hbaseProper, ?_, ?_⟩
  · apply P.isFeasibleOn_originalEdgesOfPackets S base
    exact P.groupedGraph.isFeasibleOn_of_isProperOn S base hbaseProper
  · intro v
    apply Packetization.residualCharge_add_two_fifths_le_expandedMissingColors
      G P S base hbaseProper (n : ℝ) Q (residualCharge v)
      hn0 hQ0 hQ2 (hres0 v) (haccount v)
    simpa [L] using hLK

/-- Uniform form of `exists_chargeSensitivePacketBase`: the threshold is
chosen before the graph and packetization. -/
theorem exists_uniform_chargeSensitivePacketBase
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ,
      ∀ (G : WeightedMultigraph.{u}) (P : G.Packetization)
        (S : Finset P.Packet) (residualCharge : G.V → ℝ)
        (n : ℕ) (Q : ℝ),
      N ≤ n →
      0 ≤ Q → Q ≤ 2 * (n : ℝ) →
      (∀ v, 0 ≤ residualCharge v) →
      (∀ v, (P.groupedGraph.degreeOn S v : ℝ) + residualCharge v ≤ Q) →
      P.groupedGraph.TriangleEdgeCountAtMost S (2 * (n : ℝ)) →
      ∃ (K : ℕ) (base : P.Packet → Fin K),
        0 < K ∧
        max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) ≤ (K : ℝ) ∧
        (K : ℝ) ≤
          max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q) + η * n + 1 ∧
        P.groupedGraph.IsProperOn S base ∧
        G.IsFeasibleOn (P.originalEdgesOfPackets S) (P.expandColor base) ∧
        ∀ v, residualCharge v + (2 / 5 : ℝ) * n ≤
          ((G.missingColorsAt (P.originalEdgesOfPackets S)
            (P.expandColor base) v).card : ℝ) := by
  obtain ⟨N, hN⟩ := hordinary (5 / 2 : ℝ) η (by norm_num) hη
  refine ⟨N, ?_⟩
  intro G P S residualCharge n Q hn hQ0 hQ2 hres0 haccount htriangle
  let L : ℝ := max (2 * (n : ℝ)) ((5 / 4 : ℝ) * Q)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL0 : 0 ≤ L := by
    dsimp [L]
    exact le_max_of_le_left (mul_nonneg (by norm_num) hn0)
  have hLupper : L ≤ (5 / 2 : ℝ) * n := by
    dsimp [L]
    apply max_le
    · nlinarith
    · nlinarith
  have hdegreeQ : ∀ v, (P.groupedGraph.degreeOn S v : ℝ) ≤ Q := by
    intro v
    have := haccount v
    have := hres0 v
    linarith
  have hdegreeL : ∀ v, (P.groupedGraph.degreeOn S v : ℝ) ≤ L := by
    intro v
    calc
      (P.groupedGraph.degreeOn S v : ℝ) ≤ Q := hdegreeQ v
      _ ≤ (5 / 4 : ℝ) * Q := by nlinarith
      _ ≤ L := le_max_right _ _
  have hodd : P.groupedGraph.OddSetDensityAtMost S L := by
    dsimp [L]
    exact P.groupedGraph.oddSetDensityAtMost_max_two_fiveFourth
      S (n : ℝ) Q hn0 hQ0 hdegreeQ htriangle
  obtain ⟨q, hq, hqBound, color, hproper⟩ :=
    hN P.groupedGraph S n L hn hL0 hLupper hdegreeL hodd
  obtain ⟨K, base, hK, hLK, hKupper, hbaseProper⟩ :=
    P.groupedGraph.exists_padded_properColoring
      S n q L η hL0 hη.le hq hqBound color hproper
  refine ⟨K, base, hK, hLK, hKupper, hbaseProper, ?_, ?_⟩
  · apply P.isFeasibleOn_originalEdgesOfPackets S base
    exact P.groupedGraph.isFeasibleOn_of_isProperOn S base hbaseProper
  · intro v
    apply Packetization.residualCharge_add_two_fifths_le_expandedMissingColors
      G P S base hbaseProper (n : ℝ) Q (residualCharge v)
      hn0 hQ0 hQ2 (hres0 v) (haccount v)
    simpa [L] using hLK

end WeightedMultigraph
end WeightedEdgeColoring
