import WeightedEdgeColoring.GeneralTinyThresholdPacketization
import WeightedEdgeColoring.SmallItemGreedyPacking

/-!
# Local repacking of general tiny packets

The scalar least-loaded-bin estimate is instantiated at packet size
`delta = 2*tau`.  When `tau ≤ 1/4`, a local `n`-bin budget for the original
tiny edges becomes a local

`n + ceil (4*tau*n) + 1`

bin budget for the aggregated packet graph.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

/-- The concrete scalar theorem filling `SmallItemRepackingBound`. -/
theorem smallItemRepackingBound_nat_add_ceil_two_mul
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdeltahalf : delta ≤ 1 / 2)
    (n : ℕ) :
    SmallItemRepackingBound.{u} delta n
      (n + Nat.ceil (2 * delta * n) + 1) := by
  intro B htotal hsmall
  exact B.packsInto_nat_add_ceil_two_mul
    delta hdelta0 hdeltahalf n htotal hsmall

/-- Scalar packet-size specialization: items of size at most `2*tau` and
total weight at most `n` fit in `n + ceil (4*tau*n) + 1` bins. -/
theorem smallItemRepackingBound_two_mul_tau
    (tau : ℝ) (htau0 : 0 ≤ tau) (htauquarter : tau ≤ 1 / 4)
    (n : ℕ) :
    SmallItemRepackingBound.{u} (2 * tau) n
      (n + Nat.ceil (4 * tau * n) + 1) := by
  have hdelta0 : 0 ≤ 2 * tau := by positivity
  have hdeltahalf : 2 * tau ≤ (1 : ℝ) / 2 := by linarith
  have h := smallItemRepackingBound_nat_add_ceil_two_mul
    (2 * tau) hdelta0 hdeltahalf n
  have harith : 2 * (2 * tau) * (n : ℝ) = 4 * tau * n := by ring
  simpa [harith] using h

namespace GeneralTinyThresholdPacketization

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

/-- The aggregated tiny-packet graph remains locally packable with only
`ceil (4*tau*n) + 1` extra bins. -/
theorem groupedGraph_locallyPacksInto_nat_add_ceil_four_mul
    {n : ℕ} (htau0 : 0 ≤ tau) (htauquarter : tau ≤ 1 / 4)
    (hlocal : (G.belowRestriction tau).LocallyPacksInto n) :
    P.packetization.groupedGraph.LocallyPacksInto
      (n + Nat.ceil (4 * tau * n) + 1) := by
  apply P.groupedGraph_locallyPacksInto_of_smallItemRepacking hlocal
  exact smallItemRepackingBound_two_mul_tau
    tau htau0 htauquarter n

/-- Convenient source-graph form: restrict an existing local packing to the
tiny edges, then repack the aggregated objects. -/
theorem groupedGraph_locallyPacksInto_nat_add_ceil_four_mul_of_original
    {n : ℕ} (htau0 : 0 ≤ tau) (htauquarter : tau ≤ 1 / 4)
    (hlocal : G.LocallyPacksInto n) :
    P.packetization.groupedGraph.LocallyPacksInto
      (n + Nat.ceil (4 * tau * n) + 1) := by
  apply P.groupedGraph_locallyPacksInto_nat_add_ceil_four_mul
    htau0 htauquarter
  exact G.edgeRestriction_locallyPacksInto (G.edgesBelow tau) hlocal

end GeneralTinyThresholdPacketization

/-- One-call construction of the general tiny packetization together with
its explicit local repacking bound. -/
theorem exists_generalTinyThresholdPacketization_locallyPacksInto
    (G : WeightedMultigraph.{u}) (tau : ℝ)
    (htau : 0 < tau) (htauquarter : tau ≤ 1 / 4)
    {n : ℕ} (hlocal : G.LocallyPacksInto n) :
    ∃ P : G.GeneralTinyThresholdPacketization tau,
      P.packetization.groupedGraph.LocallyPacksInto
        (n + Nat.ceil (4 * tau * n) + 1) := by
  have htauhalf : tau ≤ 1 / 2 := by linarith
  obtain ⟨P⟩ := G.exists_generalTinyThresholdPacketization
    tau htau htauhalf
  refine ⟨P, ?_⟩
  exact P.groupedGraph_locallyPacksInto_nat_add_ceil_four_mul_of_original
    htau.le htauquarter hlocal

end

end WeightedMultigraph
end WeightedEdgeColoring
