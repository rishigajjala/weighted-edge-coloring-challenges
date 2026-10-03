import WeightedEdgeColoring.GeneralTinyThresholdMixedObjects
import WeightedEdgeColoring.SeededSmallItemGreedyPacking
import WeightedEdgeColoring.BPEdgeRestriction

/-!
# Local repacking of mixed tiny-threshold objects

Keep every non-tiny singleton in its original local bin.  Starting from
those fixed loads, insert the tiny packet objects one at a time into a
least-loaded bin.  Since every inserted packet has weight at most `2*tau`
and the total mixed star weight is unchanged, the mixed graph needs only
`ceil (4*tau*n) + 1` bins beyond the original `n`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

namespace GeneralTinyThresholdPacketization

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

/-- Non-tiny singleton objects incident with one fixed vertex. -/
abbrev NonTinyStar
    (P : G.GeneralTinyThresholdPacketization tau) (v : G.V) :=
  {e : {e : G.E // e ∈ nonTinyEdges G tau} // G.Inc v e.1}

/-- Aggregated tiny packets incident with one fixed vertex. -/
abbrev TinyPacketStar (v : G.V) :=
  {p : P.Packet // P.packetization.groupedGraph.Inc v p}

/-- A mixed star is the disjoint sum of its non-tiny singleton part and its
tiny-packet part. -/
def mixedStarEquiv (v : G.V) :
    P.mixedObjectGraph.StarEdge v ≃ P.NonTinyStar v ⊕ P.TinyPacketStar v where
  toFun o := by
    rcases o with ⟨o, ho⟩
    rcases o with e | p
    · exact Sum.inl ⟨e, by
        simpa [mixedObjectGraph, mixedPacketization,
          Packetization.groupedGraph, Inc] using ho⟩
    · exact Sum.inr ⟨p, by
        simpa [mixedObjectGraph, mixedPacketization,
          Packetization.groupedGraph, Inc] using ho⟩
  invFun x := by
    rcases x with e | p
    · exact ⟨Sum.inl e.1, by
        simpa [mixedObjectGraph, mixedPacketization,
          Packetization.groupedGraph, Inc] using e.2⟩
    · exact ⟨Sum.inr p.1, by
        simpa [mixedObjectGraph, mixedPacketization,
          Packetization.groupedGraph, Inc] using p.2⟩
  left_inv o := by
    rcases o with ⟨o, ho⟩
    rcases o with e | p <;> rfl
  right_inv x := by
    rcases x with e | p
    · rcases e with ⟨e, he⟩
      rfl
    · rcases p with ⟨p, hp⟩
      rfl

/-- On the singleton half of a mixed star, mixed-object weight is the
original physical-edge weight. -/
theorem mixedWeight_nonTinyStar (v : G.V) (e : P.NonTinyStar v) :
    P.mixedObjectGraph.weight (Sum.inl e.1) = G.weight e.1.1 := by
  simpa [mixedObjectGraph, Packetization.groupedGraph] using
    P.mixedPacketWeight_inl e.1

/-- On the packet half of a mixed star, mixed-object weight is packet
weight. -/
theorem mixedWeight_tinyPacketStar (v : G.V) (p : P.TinyPacketStar v) :
    P.mixedObjectGraph.weight (Sum.inr p.1) =
      P.packetization.packetWeight p.1 := by
  simpa [mixedObjectGraph, Packetization.groupedGraph] using
    P.mixedPacketWeight_inr p.1

/-- The mixed object graph inherits an explicit local packing from the
original graph.  Non-tiny singletons stay in their old bins; only tiny
packets are greedily reinserted. -/
theorem mixedObjectGraph_locallyPacksInto_nat_add_ceil_four_mul
    {n : ℕ} (htau0 : 0 ≤ tau) (htauquarter : tau ≤ 1 / 4)
    (hlocal : G.LocallyPacksInto n) :
    P.mixedObjectGraph.LocallyPacksInto
      (n + Nat.ceil (4 * tau * n) + 1) := by
  classical
  intro v
  let m : ℕ := n + Nat.ceil (4 * tau * n) + 1
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hnm : n ≤ m := by
    dsimp [m]
    omega
  obtain ⟨originalBin, horiginalBin⟩ := hlocal v
  let leftWeight : P.NonTinyStar v → ℝ := fun e ↦ G.weight e.1.1
  let rightWeight : P.TinyPacketStar v → ℝ := fun p ↦
    P.packetization.packetWeight p.1
  let leftToOriginal : P.NonTinyStar v ↪ G.StarEdge v :=
    ⟨fun e ↦ ⟨e.1.1, e.2⟩, by
      intro e f hef
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : G.StarEdge v ↦ z.1) hef⟩
  let leftBin : P.NonTinyStar v → Fin n := fun e ↦
    originalBin (leftToOriginal e)
  have hleftBin : ∀ i,
      (∑ e : P.NonTinyStar v,
        if leftBin e = i then leftWeight e else 0) ≤ 1 := by
    intro i
    let term : G.StarEdge v → ℝ := fun e ↦
      if originalBin e = i then G.weight e.1 else 0
    have hterm0 : ∀ e : G.StarEdge v, 0 ≤ term e := by
      intro e
      dsimp [term]
      split
      · exact G.weight_nonneg e.1
      · exact le_rfl
    calc
      (∑ e : P.NonTinyStar v,
          if leftBin e = i then leftWeight e else 0) =
          ∑ e ∈ (Finset.univ.map leftToOriginal), term e := by
            rw [Finset.sum_map]
            rfl
      _ ≤ ∑ e ∈ (Finset.univ : Finset (G.StarEdge v)), term e := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _) (fun e _he _hne ↦ hterm0 e)
      _ = G.starBinLoad originalBin i := by
            simp only [term, starBinLoad]
      _ ≤ 1 := horiginalBin i
  have hrightSmall : ∀ p : P.TinyPacketStar v,
      rightWeight p ≤ 2 * tau := by
    intro p
    exact P.packetWeight_le_two p.1
  have hequivWeight (o : P.mixedObjectGraph.StarEdge v) :
      Sum.elim leftWeight rightWeight (P.mixedStarEquiv v o) =
        P.mixedObjectGraph.weight o.1 := by
    rcases o with ⟨o, ho⟩
    rcases o with e | p
    · change G.weight e.1 = P.mixedObjectGraph.weight (Sum.inl e)
      simpa [mixedObjectGraph, Packetization.groupedGraph] using
        (P.mixedPacketWeight_inl e).symm
    · change P.packetization.packetWeight p =
        P.mixedObjectGraph.weight (Sum.inr p)
      simpa [mixedObjectGraph, Packetization.groupedGraph] using
        (P.mixedPacketWeight_inr p).symm
  have htotal :
      (∑ e : P.NonTinyStar v, leftWeight e) +
          ∑ p : P.TinyPacketStar v, rightWeight p ≤ n := by
    have hsplit :
        (∑ e : P.NonTinyStar v, leftWeight e) +
            ∑ p : P.TinyPacketStar v, rightWeight p =
          P.mixedObjectGraph.starWeight v := by
      have hsumSum :
          (∑ x : P.NonTinyStar v ⊕ P.TinyPacketStar v,
              Sum.elim leftWeight rightWeight x) =
            (∑ e : P.NonTinyStar v, leftWeight e) +
              ∑ p : P.TinyPacketStar v, rightWeight p := by
        simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
      have hsumEquiv :
          P.mixedObjectGraph.starWeight v =
            ∑ x : P.NonTinyStar v ⊕ P.TinyPacketStar v,
              Sum.elim leftWeight rightWeight x := by
        unfold starWeight
        exact Fintype.sum_equiv (P.mixedStarEquiv v) _ _
          (fun o ↦ (hequivWeight o).symm)
      exact hsumSum.symm.trans hsumEquiv.symm
    rw [hsplit, P.mixedObjectGraph_starWeight]
    exact G.starWeight_le_of_packsStarInto (hlocal v)
  have hcapacity :
      (n : ℝ) / (m : ℝ) + 2 * tau ≤ 1 := by
    have hdelta0 : 0 ≤ 2 * tau := by positivity
    have hdeltahalf : 2 * tau ≤ (1 : ℝ) / 2 := by linarith
    have h := BinPackingInstance.nat_div_nat_add_ceil_two_mul_add_le_one
      (2 * tau) hdelta0 hdeltahalf n
    have harith : 2 * (2 * tau) * (n : ℝ) = 4 * tau * n := by ring
    simpa [m, harith] using h
  obtain ⟨sumBin, hsumBin⟩ :=
    BinPackingInstance.exists_sum_assignment_of_left_packing_and_small_right
      leftWeight rightWeight
      (fun e ↦ G.weight_nonneg e.1.1)
      (fun p ↦ P.packetization.packetWeight_pos p.1 |>.le)
      (2 * tau) hrightSmall hnm hm leftBin hleftBin htotal hcapacity
  let mixedBin : P.mixedObjectGraph.StarEdge v → Fin m := fun o ↦
    sumBin (P.mixedStarEquiv v o)
  refine ⟨mixedBin, ?_⟩
  intro j
  calc
    P.mixedObjectGraph.starBinLoad mixedBin j =
        ∑ x : P.NonTinyStar v ⊕ P.TinyPacketStar v,
          if sumBin x = j then Sum.elim leftWeight rightWeight x else 0 := by
      unfold starBinLoad
      exact Fintype.sum_equiv (P.mixedStarEquiv v) _ _ (fun o ↦ by
        have hw := congrArg
          (fun w : ℝ => if sumBin (P.mixedStarEquiv v o) = j then w else 0)
          (hequivWeight o)
        simpa only [mixedBin] using hw.symm)
    _ ≤ 1 := hsumBin j

/-- Restricting the mixed packing gives the same bound for the heavy core. -/
theorem coreObjectGraph_locallyPacksInto_nat_add_ceil_four_mul
    {n : ℕ} (htau0 : 0 ≤ tau) (htauquarter : tau ≤ 1 / 4)
    (hlocal : G.LocallyPacksInto n) :
    P.coreObjectGraph.LocallyPacksInto
      (n + Nat.ceil (4 * tau * n) + 1) := by
  exact P.mixedObjectGraph.edgeRestriction_locallyPacksInto P.coreObjects
    (P.mixedObjectGraph_locallyPacksInto_nat_add_ceil_four_mul
      htau0 htauquarter hlocal)

end GeneralTinyThresholdPacketization

end

end WeightedMultigraph
end WeightedEdgeColoring
