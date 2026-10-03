import WeightedEdgeColoring.ScaledBipartitePacketization
import WeightedEdgeColoring.BPEdgeRestriction

/-!
# Fixed-threshold packets for tiny parallel edges

For a threshold `tau ≤ 1/2`, restrict to edges of weight below `tau`, scale
their weights by `1/(2*tau)`, and use the existing minimal packetization.
After undoing the scale, every packet has weight at most `2*tau`, while the
packets of weight at most `tau` are endpoint-simple.  Hence each endpoint
pair has at most one tiny remainder.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

def edgesBelow (tau : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦ G.weight e < tau

@[simp] theorem mem_edgesBelow_iff (tau : ℝ) (e : G.E) :
    e ∈ G.edgesBelow tau ↔ G.weight e < tau := by
  simp [edgesBelow]

abbrev belowRestriction (tau : ℝ) : WeightedMultigraph.{u} :=
  G.edgeRestriction (G.edgesBelow tau)

def Bipartition.belowRestriction (b : G.Bipartition) (tau : ℝ) :
    (G.belowRestriction tau).Bipartition :=
  Bipartition.edgeRestriction G b (G.edgesBelow tau)

/-- The result of grouping every edge below `tau` along each endpoint pair. -/
structure TinyThresholdPacketization (b : G.Bipartition) (tau : ℝ) where
  packetization :
    (G.belowRestriction tau).BipartitePacketization
      (Bipartition.belowRestriction (G := G) b tau)
  packetWeight_le_two :
    ∀ p, packetization.packetWeight p ≤ 2 * tau
  small_endpoint_injective :
    Function.Injective
      (fun p : {p : packetization.Packet //
          packetization.packetWeight p ≤ tau} ↦
        s(packetization.tail p.1, packetization.head p.1))

namespace TinyThresholdPacketization

variable {G : WeightedMultigraph.{u}} {b : G.Bipartition} {tau : ℝ}
  (P : G.TinyThresholdPacketization b tau)

abbrev Packet := P.packetization.Packet

instance : Fintype P.Packet := inferInstance
instance : DecidableEq P.Packet := inferInstance

/-- At most one packet of weight at most `tau` joins a fixed unordered
endpoint pair. -/
theorem eq_of_small_of_same_endpoints {p q : P.Packet}
    (hp : P.packetization.packetWeight p ≤ tau)
    (hq : P.packetization.packetWeight q ≤ tau)
    (hends : s(P.packetization.tail p, P.packetization.head p) =
      s(P.packetization.tail q, P.packetization.head q)) :
    p = q := by
  let p' : {r : P.Packet // P.packetization.packetWeight r ≤ tau} := ⟨p, hp⟩
  let q' : {r : P.Packet // P.packetization.packetWeight r ≤ tau} := ⟨q, hq⟩
  have hpq : p' = q' := P.small_endpoint_injective (by
    simpa [p', q'] using hends)
  exact congrArg Subtype.val hpq

end TinyThresholdPacketization

/-- Fixed-threshold tiny packetization, obtained from the minimal scaled
packetization. -/
theorem exists_tinyThresholdPacketization
    (b : G.Bipartition) (tau : ℝ) (htau : 0 < tau)
    (htauhalf : tau ≤ 1 / 2) :
    Nonempty (G.TinyThresholdPacketization b tau) := by
  let H : WeightedMultigraph.{u} := G.belowRestriction tau
  let bH : H.Bipartition :=
    Bipartition.belowRestriction (G := G) b tau
  let s : ℝ := 1 / (2 * tau)
  have h2tau : 0 < 2 * tau := mul_pos (by norm_num) htau
  have hs : 0 < s := one_div_pos.mpr h2tau
  have hupper : ∀ e, s * H.weight e ≤ 1 := by
    intro e
    have he : G.weight e.1 < tau := G.mem_edgesBelow_iff tau e.1 |>.mp e.2
    change (1 / (2 * tau)) * G.weight e.1 ≤ 1
    calc
      (1 / (2 * tau)) * G.weight e.1 = G.weight e.1 / (2 * tau) := by ring
      _ ≤ 1 := (div_le_one h2tau).2 (by linarith)
  have hsone : 1 ≤ s := by
    apply (le_div_iff₀ h2tau).2
    linarith
  let bScaled : (H.scaleWeights s hs hupper).Bipartition :=
    Bipartition.scaleWeights (G := H) bH s hs hupper
  obtain ⟨Pscaled, hsimple⟩ :=
    (H.scaleWeights s hs hupper).exists_bipartitePacketization bScaled
  let P : H.BipartitePacketization bH := Pscaled.unscale hsone
  have hinv : 1 / s = 2 * tau := by
    dsimp [s]
    field_simp
  have hhalfInv : 1 / (2 * s) = tau := by
    dsimp [s]
    field_simp
  refine ⟨{
    packetization := P
    packetWeight_le_two := ?_
    small_endpoint_injective := ?_ }⟩
  · intro p
    calc
      P.packetWeight p ≤ 1 / s := Pscaled.unscale_packetWeight_le_inv hsone p
      _ = 2 * tau := hinv
  · intro p q hpq
    apply Subtype.ext
    apply Pscaled.small_unscaled_packets_endpoint_injective hsone hsimple
    · simpa [P, hhalfInv] using p.2
    · simpa [P, hhalfInv] using q.2
    · simpa [P] using hpq

end

end WeightedMultigraph
end WeightedEdgeColoring
