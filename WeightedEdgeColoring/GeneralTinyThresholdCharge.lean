import WeightedEdgeColoring.GeneralTinyThresholdPacketization
import WeightedEdgeColoring.HarmonicBinCharge
import WeightedEdgeColoring.BPLocalCharge

/-!
# Harmonic charge of general tiny packets

Canonical tiny packetization works without a bipartition.  This file proves
that it also preserves harmonic charge up to the same vanishing error as in
the bipartite construction: at a reciprocal threshold, aggregation adds at
most `4*tau` times the original tiny star weight.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}} {tau : ℝ}

namespace GeneralTinyThresholdPacketization

variable (P : G.GeneralTinyThresholdPacketization tau)

/-- Every genuine edge weight is at most its harmonic charge. -/
theorem physicalWeight_le_harmonicCharge
    (H : WeightedMultigraph.{u}) (e : H.E) :
    H.weight e ≤ harmonicCharge (H.weight e) := by
  let r : ℕ := Nat.floor ((1 : ℝ) / H.weight e)
  have hw : 0 < H.weight e := H.weight_pos e
  have hnonneg : 0 ≤ (1 : ℝ) / H.weight e :=
    div_nonneg zero_le_one hw.le
  have hrpos : 0 < r := by
    have h1 : (1 : ℝ) ≤ 1 / H.weight e := by
      rw [le_div_iff₀ hw]
      simpa using H.weight_le_one e
    have h1n : (1 : ℕ) ≤ r :=
      (Nat.le_floor_iff hnonneg).2 (by simpa using h1)
    omega
  have hrfloor : (r : ℝ) ≤ 1 / H.weight e := by
    simpa [r] using Nat.floor_le hnonneg
  unfold harmonicCharge
  change H.weight e ≤ (1 : ℝ) / r
  rw [le_div_iff₀ (by exact_mod_cast hrpos : (0 : ℝ) < r)]
  simpa [mul_comm] using (le_div_iff₀ hw).1 hrfloor

/-- Replacing tiny physical edges by canonical endpoint-pair packets adds
at most `4*tau` times their physical star weight to harmonic charge. -/
theorem groupedGraph_starCharge_le_add_four_mul
    (t : ℕ) (ht : 0 < t)
    (hupper : 2 * tau ≤ (1 : ℝ) / t)
    (hlower : (1 : ℝ) / t ≤ 4 * tau)
    (v : G.V) :
    P.packetization.groupedGraph.starCharge harmonicCharge v ≤
      (G.belowRestriction tau).starCharge harmonicCharge v +
        4 * tau * (G.belowRestriction tau).starWeight v := by
  have hpcharge : ∀ p : P.Packet,
      harmonicCharge (P.packetization.packetWeight p) ≤
        (1 + 4 * tau) * P.packetization.packetWeight p := by
    intro p
    have hpupper : P.packetization.packetWeight p ≤ (1 : ℝ) / t :=
      (P.packetWeight_le_two p).trans hupper
    calc
      harmonicCharge (P.packetization.packetWeight p) ≤
          (((t + 1 : ℕ) : ℝ) / t) *
            P.packetization.packetWeight p :=
        harmonicCharge_le_mul_weight ht
          (P.packetization.packetWeight_pos p) hpupper
      _ = (1 + (1 : ℝ) / t) *
          P.packetization.packetWeight p := by
        have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
        rw [Nat.cast_add, Nat.cast_one]
        field_simp [htR]
      _ ≤ (1 + 4 * tau) * P.packetization.packetWeight p := by
        gcongr
        exact P.packetization.packetWeight_pos p |>.le
  have hgroup :
      P.packetization.groupedGraph.starCharge harmonicCharge v ≤
        (1 + 4 * tau) *
          P.packetization.groupedGraph.starWeight v := by
    unfold starCharge starWeight
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _hp ↦ by
      simpa [Packetization.groupedGraph] using hpcharge p.1)
  have hweightCharge :
      (G.belowRestriction tau).starWeight v ≤
        (G.belowRestriction tau).starCharge harmonicCharge v := by
    unfold starWeight starCharge
    exact Finset.sum_le_sum (fun e _he ↦
      physicalWeight_le_harmonicCharge (G.belowRestriction tau) e.1)
  rw [P.groupedGraph_starWeight v] at hgroup
  calc
    P.packetization.groupedGraph.starCharge harmonicCharge v ≤
        (1 + 4 * tau) *
          (G.belowRestriction tau).starWeight v := hgroup
    _ = (G.belowRestriction tau).starWeight v +
        4 * tau * (G.belowRestriction tau).starWeight v := by ring
    _ ≤ (G.belowRestriction tau).starCharge harmonicCharge v +
        4 * tau * (G.belowRestriction tau).starWeight v := by gcongr

/-- Uniform local-packing form of the charge-inflation estimate. -/
theorem groupedGraph_starCharge_le_add_four_mul_n
    {n : ℕ} (htau : 0 ≤ tau)
    (hlocal : (G.belowRestriction tau).LocallyPacksInto n)
    (t : ℕ) (ht : 0 < t)
    (hupper : 2 * tau ≤ (1 : ℝ) / t)
    (hlower : (1 : ℝ) / t ≤ 4 * tau)
    (v : G.V) :
    P.packetization.groupedGraph.starCharge harmonicCharge v ≤
      (G.belowRestriction tau).starCharge harmonicCharge v +
        4 * tau * n := by
  have hcharge := P.groupedGraph_starCharge_le_add_four_mul
    t ht hupper hlower v
  have hstar : (G.belowRestriction tau).starWeight v ≤ (n : ℝ) :=
    (G.belowRestriction tau).starWeight_le_of_packsStarInto (hlocal v)
  calc
    P.packetization.groupedGraph.starCharge harmonicCharge v ≤
        (G.belowRestriction tau).starCharge harmonicCharge v +
          4 * tau * (G.belowRestriction tau).starWeight v := hcharge
    _ ≤ (G.belowRestriction tau).starCharge harmonicCharge v +
          4 * tau * n := by
      gcongr

end GeneralTinyThresholdPacketization

end

end WeightedMultigraph
end WeightedEdgeColoring
