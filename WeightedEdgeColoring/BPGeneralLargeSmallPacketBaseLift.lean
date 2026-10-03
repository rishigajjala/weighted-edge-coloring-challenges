import WeightedEdgeColoring.BPGeneralFloorPacketBase
import WeightedEdgeColoring.BPGeneralMinimumCostSmallBundles

/-!
# Lifting a large/small packet split to a colored base

This file supplies the graph-level end of the large/small bundle argument.
It is deliberately independent of the construction of the packets inside a
large bundle.

The first lemma separates selected packets into paid packets, each carrying
at least one unit of harmonic charge, and unpaid packets.  Only the ordinary
degree of the unpaid packets is lost.  The second theorem absorbs additive
degree and triangle losses by replacing `n` with `n + d` in the existing
charge-sensitive packet theorem.  It also transports a fixed multiplicity
bound on the complementary physical edge set to the resulting
`GeneralColoredPacketBase`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

namespace Packetization

variable {G : WeightedMultigraph.{u}} (P : G.Packetization)

/-- Selected packets that carry one unit of harmonic charge pay for their
own grouped degree.  Any other selected packets are charged only through
their ordinary degree. -/
theorem degree_add_complementHarmonicCharge_le_starCharge_add_unpaidDegree
    (selected paid : Finset P.Packet) (hpaid : paid ⊆ selected)
    (hunit : ∀ p ∈ paid, 1 ≤ P.packetCharge harmonicCharge p)
    (v : G.V) :
    (P.groupedGraph.degreeOn selected v : ℝ) +
        G.chargeOn harmonicCharge
          (Finset.univ \ P.originalEdgesOfPackets selected) v ≤
      G.starCharge harmonicCharge v +
        (P.groupedGraph.degreeOn (selected \ paid) v : ℝ) := by
  let unpaid := selected \ paid
  have hdisjPackets : Disjoint paid unpaid := by
    rw [Finset.disjoint_left]
    intro p hp hpu
    exact (Finset.mem_sdiff.mp hpu).2 hp
  have hunionPackets : paid ∪ unpaid = selected := by
    exact Finset.union_sdiff_of_subset hpaid
  have hdegree : P.groupedGraph.degreeOn selected v =
      P.groupedGraph.degreeOn paid v + P.groupedGraph.degreeOn unpaid v := by
    rw [← hunionPackets,
      P.groupedGraph.degreeOn_union_of_disjoint hdisjPackets v]
  have hpaidDegree : (P.groupedGraph.degreeOn paid v : ℝ) ≤
      G.chargeOn harmonicCharge (P.originalEdgesOfPackets paid) v := by
    rw [P.chargeOn_originalEdgesOfPackets harmonicCharge paid v]
    unfold WeightedMultigraph.degreeOn
    calc
      (((paid.filter (P.groupedGraph.Inc v)).card : ℕ) : ℝ) =
          ∑ _p ∈ paid.filter (P.groupedGraph.Inc v), (1 : ℝ) := by
        simp
      _ ≤ ∑ p ∈ paid.filter (P.groupedGraph.Inc v),
          P.packetCharge harmonicCharge p := by
        exact Finset.sum_le_sum fun p hp ↦
          hunit p (Finset.mem_filter.mp hp).1
      _ = ∑ p ∈ paid,
          if P.groupedGraph.Inc v p
            then P.packetCharge harmonicCharge p else 0 := by
        rw [Finset.sum_filter]
        rfl
  have horiginalSub : P.originalEdgesOfPackets paid ⊆
      P.originalEdgesOfPackets selected := by
    intro e he
    have he' := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨he'.1, hpaid he'.2⟩
  have hdisjPhysical : Disjoint (P.originalEdgesOfPackets paid)
      (Finset.univ \ P.originalEdgesOfPackets selected) := by
    rw [Finset.disjoint_left]
    intro e hePaid heResidual
    exact (Finset.mem_sdiff.mp heResidual).2 (horiginalSub hePaid)
  have hunionSub :
      P.originalEdgesOfPackets paid ∪
          (Finset.univ \ P.originalEdgesOfPackets selected) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hchargeMono :
      G.chargeOn harmonicCharge
          (P.originalEdgesOfPackets paid ∪
            (Finset.univ \ P.originalEdgesOfPackets selected)) v ≤
        G.chargeOn harmonicCharge Finset.univ v := by
    unfold WeightedMultigraph.chargeOn
    exact Finset.sum_le_sum_of_subset_of_nonneg hunionSub (by
      intro e _heUniv _heUnion
      by_cases hinc : G.Inc v e
      · simp [hinc, harmonicCharge_nonneg]
      · simp [hinc])
  have hpaidResidual :
      G.chargeOn harmonicCharge (P.originalEdgesOfPackets paid) v +
          G.chargeOn harmonicCharge
            (Finset.univ \ P.originalEdgesOfPackets selected) v ≤
        G.starCharge harmonicCharge v := by
    rw [← G.chargeOn_union hdisjPhysical v,
      G.starCharge_eq_chargeOn_univ harmonicCharge v]
    exact hchargeMono
  rw [hdegree]
  push_cast
  dsimp [unpaid]
  linarith

end Packetization

/-- A packet family with additive degree and triangle loss gives a colored
packet base at the enlarged scale `n + d`.  The physical complement is
definitionally the residual edge set of the returned base, so its fixed
pair-multiplicity bound is preserved exactly. -/
theorem exists_uniform_largeSmallGeneralColoredPacketBase
    (hordinary : OrdinaryMultigraphNearFractionalColoring.{u})
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ,
      ∀ (G : WeightedMultigraph.{u}) (P : G.Packetization)
        (selected paid : Finset P.Packet) (n d L : ℕ) (Q : ℝ),
      N ≤ n →
      paid ⊆ selected →
      (∀ p ∈ paid, 1 ≤ P.packetCharge harmonicCharge p) →
      (∀ v, G.starCharge harmonicCharge v +
          (P.groupedGraph.degreeOn (selected \ paid) v : ℝ) ≤ Q) →
      0 ≤ Q → Q ≤ 2 * ((n + d : ℕ) : ℝ) →
      P.groupedGraph.TriangleEdgeCountAtMost selected
        (2 * ((n + d : ℕ) : ℝ)) →
      (G.edgeRestriction
        (Finset.univ \ P.originalEdgesOfPackets selected)).PairMultiplicityAtMost L →
      ∃ (K : ℕ) (C : G.GeneralColoredPacketBase K),
        max (2 * ((n + d : ℕ) : ℝ)) ((5 / 4 : ℝ) * Q) ≤ (K : ℝ) ∧
        (K : ℝ) ≤
          max (2 * ((n + d : ℕ) : ℝ)) ((5 / 4 : ℝ) * Q) +
            eta * (n + d : ℕ) + 1 ∧
        (∀ v,
          G.chargeOn harmonicCharge C.residualEdges v +
              (2 / 5 : ℝ) * (n + d : ℕ) ≤
            ((G.missingColorsAt C.fullEdges C.baseColor v).card : ℝ)) ∧
        C.residualGraph.PairMultiplicityAtMost L ∧
        C.residualEdges =
          Finset.univ \ P.originalEdgesOfPackets selected := by
  obtain ⟨N, hN⟩ :=
    exists_uniform_chargeSensitivePacketBase hordinary eta heta
  refine ⟨N, ?_⟩
  intro G P selected paid n d L Q hn hpaid hunit haccount hQ0 hQupper
    htriangle hmult
  have hn' : N ≤ n + d := hn.trans (Nat.le_add_right n d)
  let residualCharge : G.V → ℝ := fun v ↦
    G.chargeOn harmonicCharge
      (Finset.univ \ P.originalEdgesOfPackets selected) v
  have hres0 : ∀ v, 0 ≤ residualCharge v := by
    intro v
    unfold residualCharge WeightedMultigraph.chargeOn
    exact Finset.sum_nonneg fun e _he ↦ by
      by_cases hinc : G.Inc v e
      · simp [hinc, harmonicCharge_nonneg]
      · simp [hinc]
  have hpacketAccount : ∀ v,
      (P.groupedGraph.degreeOn selected v : ℝ) + residualCharge v ≤ Q := by
    intro v
    exact (P.degree_add_complementHarmonicCharge_le_starCharge_add_unpaidDegree
      selected paid hpaid hunit v).trans (haccount v)
  obtain ⟨K, base, hK, hlower, hupper, hproper, _hfeasible, hmissing⟩ :=
    hN G P selected residualCharge (n + d) Q hn' hQ0 hQupper hres0
      hpacketAccount htriangle
  let C : G.GeneralColoredPacketBase K := {
    packetization := P
    fullPackets := selected
    palette_pos := hK
    packetColor := base
    packetProper := hproper }
  refine ⟨K, C, hlower, hupper, ?_, ?_, ?_⟩
  · intro v
    simpa [C, GeneralColoredPacketBase.residualEdges,
      GeneralColoredPacketBase.fullEdges, GeneralColoredPacketBase.baseColor,
      residualCharge] using hmissing v
  · simpa [C, GeneralColoredPacketBase.residualGraph,
      GeneralColoredPacketBase.residualEdges,
      GeneralColoredPacketBase.fullEdges] using hmult
  · rfl

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.WeightedMultigraph.Packetization.degree_add_complementHarmonicCharge_le_starCharge_add_unpaidDegree
#print axioms WeightedEdgeColoring.WeightedMultigraph.exists_uniform_largeSmallGeneralColoredPacketBase
