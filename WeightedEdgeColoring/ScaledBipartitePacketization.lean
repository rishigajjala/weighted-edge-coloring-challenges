import WeightedEdgeColoring.WeightedMultigraphScaling

/-!
# Returning a packetization from scaled weights

Packetizing a graph after multiplying all weights by `s ≥ 1` gives packets
whose original total weight is at most `1 / s`.  Moreover, light packets in
the scaled graph are precisely packets whose original weight is at most
`1 / (2s)`.  These facts are the adapter needed for fixed-threshold grouping
of arbitrarily tiny parallel edges.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}}
variable {s : ℝ} {hs : 0 < s} {hupper : ∀ e, s * G.weight e ≤ 1}
variable {b : G.Bipartition}

namespace BipartitePacketization

variable
  (P : (G.scaleWeights s hs hupper).BipartitePacketization
    (Bipartition.scaleWeights (G := G) b s hs hupper))

/-- Forget the scaling while retaining the same packets.  The assumption
`1 ≤ s` ensures that every packet still has original weight at most one. -/
def unscale (hsone : 1 ≤ s) : G.BipartitePacketization b where
  Packet := P.Packet
  instFintypePacket := inferInstance
  instDecidableEqPacket := inferInstance
  packetOf := P.packetOf
  tail := P.tail
  head := P.head
  endpoints := P.endpoints
  onto := P.onto
  weight_le_one := by
    intro p
    have hnonneg :
        0 ≤ ∑ e : G.E, if P.packetOf e = p then G.weight e else 0 := by
      apply Finset.sum_nonneg
      intro e _he
      split
      · exact G.weight_nonneg e
      · exact le_rfl
    have hscaled :
        s * (∑ e : G.E, if P.packetOf e = p then G.weight e else 0) ≤ 1 := by
      calc
        s * (∑ e : G.E, if P.packetOf e = p then G.weight e else 0) =
            ∑ e : G.E,
              if P.packetOf e = p then
                (G.scaleWeights s hs hupper).weight e else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _he
          by_cases hep : P.packetOf e = p <;> simp [hep]
        _ ≤ 1 := P.weight_le_one p
    calc
      (∑ e : G.E, if P.packetOf e = p then G.weight e else 0) ≤
          s * (∑ e : G.E, if P.packetOf e = p then G.weight e else 0) := by
        nlinarith
      _ ≤ 1 := hscaled

/-- Exact relation between the scaled and original packet weights. -/
theorem packetWeight_eq_scale_mul_unscale (hsone : 1 ≤ s) (p : P.Packet) :
    P.packetWeight p = s * (P.unscale hsone).packetWeight p := by
  unfold packetWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hep : P.packetOf e = p <;> simp [unscale, hep]

/-- Every packet has original total weight at most `1 / s`. -/
theorem unscale_packetWeight_le_inv (hsone : 1 ≤ s) (p : P.Packet) :
    (P.unscale hsone).packetWeight p ≤ 1 / s := by
  have hpacket := P.weight_le_one p
  change P.packetWeight p ≤ 1 at hpacket
  rw [P.packetWeight_eq_scale_mul_unscale hsone p] at hpacket
  exact (le_div_iff₀ hs).2 (by simpa [mul_comm] using hpacket)

/-- An original packet of weight at most `1/(2s)` is light in the scaled
packetization. -/
theorem mem_lightPackets_of_unscale_packetWeight_le
    (hsone : 1 ≤ s) (p : P.Packet)
    (hp : (P.unscale hsone).packetWeight p ≤ 1 / (2 * s)) :
    p ∈ P.lightPackets := by
  have hscaled : P.packetWeight p ≤ (1 / 2 : ℝ) := by
    rw [P.packetWeight_eq_scale_mul_unscale hsone p]
    have hsnonneg : 0 ≤ s := hs.le
    calc
      s * (P.unscale hsone).packetWeight p ≤ s * (1 / (2 * s)) :=
        mul_le_mul_of_nonneg_left hp hsnonneg
      _ = 1 / 2 := by field_simp
  unfold lightPackets WeightedMultigraph.heavyEdges
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_filter]
  exact not_lt_of_ge hscaled

/-- Thus packets whose original weight is at most `1/(2s)` are simple over
endpoint pairs whenever the scaled light packets are simple. -/
theorem small_unscaled_packets_endpoint_injective
    (hsone : 1 ≤ s) (hsimple : P.LightIsSimple)
    {p q : P.Packet}
    (hp : (P.unscale hsone).packetWeight p ≤ 1 / (2 * s))
    (hq : (P.unscale hsone).packetWeight q ≤ 1 / (2 * s))
    (hends : s(P.tail p, P.head p) = s(P.tail q, P.head q)) :
    p = q := by
  let p' : {r : P.Packet // r ∈ P.lightPackets} :=
    ⟨p, P.mem_lightPackets_of_unscale_packetWeight_le hsone p hp⟩
  let q' : {r : P.Packet // r ∈ P.lightPackets} :=
    ⟨q, P.mem_lightPackets_of_unscale_packetWeight_le hsone q hq⟩
  have hpq : p' = q' := hsimple (by simpa [p', q'] using hends)
  exact congrArg Subtype.val hpq

end BipartitePacketization

end

end WeightedMultigraph
end WeightedEdgeColoring
