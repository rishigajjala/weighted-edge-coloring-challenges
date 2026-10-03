import WeightedEdgeColoring.BipartitePackets

/-!
# Packetization without a bipartition

The general multigraph `bp` proof groups parallel physical edges into
packets before applying an ordinary edge-colouring theorem.  This file
contains the graph-independent packet interface and proves that expanding a
packet colour preserves every vertex--colour load exactly.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- A partition of the physical edges into nonempty loopless packets of
total weight at most one.  `incidence` says that replacing an edge by its
packet preserves its two endpoints; it avoids choosing an orientation of an
unordered parallel bundle. -/
structure Packetization where
  Packet : Type u
  instFintypePacket : Fintype Packet
  instDecidableEqPacket : DecidableEq Packet
  packetOf : G.E → Packet
  tail : Packet → G.V
  head : Packet → G.V
  noLoop : ∀ p, tail p ≠ head p
  incidence : ∀ v e,
    tail (packetOf e) = v ∨ head (packetOf e) = v ↔ G.Inc v e
  onto : Function.Surjective packetOf
  weight_le_one : ∀ p,
    (∑ e : G.E, if packetOf e = p then G.weight e else 0) ≤ 1

attribute [instance]
  Packetization.instFintypePacket
  Packetization.instDecidableEqPacket

namespace Packetization

variable {G} (P : G.Packetization)

/-- Total physical weight in a packet. -/
def packetWeight (p : P.Packet) : ℝ :=
  ∑ e : G.E, if P.packetOf e = p then G.weight e else 0

theorem packetWeight_pos (p : P.Packet) : 0 < P.packetWeight p := by
  classical
  obtain ⟨e, he⟩ := P.onto p
  calc
    0 < G.weight e := G.weight_pos e
    _ = (if P.packetOf e = p then G.weight e else 0) := by simp [he]
    _ ≤ ∑ x : G.E, if P.packetOf x = p then G.weight x else 0 := by
      change (if P.packetOf e = p then G.weight e else 0) ≤
        ∑ x ∈ (Finset.univ : Finset G.E),
          if P.packetOf x = p then G.weight x else 0
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset G.E))
        (f := fun x ↦ if P.packetOf x = p then G.weight x else 0)
        (fun x _hx ↦ by
          by_cases hx : P.packetOf x = p
          · simp [hx, G.weight_nonneg]
          · simp [hx])
        (Finset.mem_univ e)

theorem packetWeight_le_one (p : P.Packet) : P.packetWeight p ≤ 1 :=
  P.weight_le_one p

/-- The ordinary weighted multigraph whose indexed edges are packets. -/
noncomputable def groupedGraph : WeightedMultigraph.{u} where
  V := G.V
  E := P.Packet
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst := P.tail
  snd := P.head
  noLoop := P.noLoop
  weight := P.packetWeight
  weight_pos := P.packetWeight_pos
  weight_le_one := P.packetWeight_le_one

theorem groupedGraph_inc_packetOf (v : G.V) (e : G.E) :
    P.groupedGraph.Inc v (P.packetOf e) ↔ G.Inc v e := by
  exact P.incidence v e

/-- Expand a packet colour to all physical edges in that packet. -/
def expandColor {q : ℕ} (color : P.Packet → Fin q) : G.E → Fin q :=
  fun e ↦ color (P.packetOf e)

/-- Physical edges lying in a chosen packet set. -/
def originalEdgesOfPackets (S : Finset P.Packet) : Finset G.E :=
  Finset.univ.filter fun e ↦ P.packetOf e ∈ S

theorem originalEdgesOfPackets_compl (S : Finset P.Packet) :
    P.originalEdgesOfPackets (Finset.univ \ S) =
      Finset.univ \ P.originalEdgesOfPackets S := by
  classical
  ext e
  simp [originalEdgesOfPackets]

/-- A packet color is used at a physical vertex exactly when it is used at
that vertex in the grouped graph.  In particular, packet expansion preserves
the whole missing-color set, even though several physical edges in one packet
receive the same color. -/
theorem missingColorsAt_originalEdgesOfPackets
    {q : ℕ} (S : Finset P.Packet) (color : P.Packet → Fin q)
    (v : G.V) :
    G.missingColorsAt (P.originalEdgesOfPackets S)
        (P.expandColor color) v =
      P.groupedGraph.missingColorsAt S color v := by
  classical
  unfold WeightedMultigraph.missingColorsAt
  congr 1
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨e, he, hei⟩
    have he' := Finset.mem_filter.mp he
    have heS : P.packetOf e ∈ S := by
      exact (Finset.mem_filter.mp he'.1).2
    have heInc : G.Inc v e := he'.2
    apply Finset.mem_image.mpr
    refine ⟨P.packetOf e, Finset.mem_filter.mpr ⟨heS, ?_⟩, ?_⟩
    · exact (P.groupedGraph_inc_packetOf v e).2 heInc
    · exact hei
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    have hp' := Finset.mem_filter.mp hp
    obtain ⟨e, hePacket⟩ := P.onto p
    have heInc : G.Inc v e := by
      apply (P.groupedGraph_inc_packetOf v e).1
      simpa [hePacket] using hp'.2
    apply Finset.mem_image.mpr
    refine ⟨e, Finset.mem_filter.mpr ⟨?_, heInc⟩, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa [hePacket] using hp'.1⟩
    · simpa [expandColor, hePacket] using hpi

/-- For a proper packet coloring, the physical missing palette has size
`q` minus the packet degree. -/
theorem card_missingColorsAt_expandColor
    {q : ℕ} (S : Finset P.Packet) (color : P.Packet → Fin q)
    (hproper : P.groupedGraph.IsProperOn S color) (v : G.V) :
    (G.missingColorsAt (P.originalEdgesOfPackets S)
      (P.expandColor color) v).card =
      q - P.groupedGraph.degreeOn S v := by
  rw [P.missingColorsAt_originalEdgesOfPackets S color v]
  exact P.groupedGraph.card_missingColorsAt S color hproper v

/-- Restricted star weight is preserved by packet expansion. -/
theorem restrictedWeight_originalEdgesOfPackets
    (S : Finset P.Packet) (v : G.V) :
    (∑ e ∈ P.originalEdgesOfPackets S,
      if G.Inc v e then G.weight e else 0) =
    ∑ p ∈ S,
      if P.groupedGraph.Inc v p then P.packetWeight p else 0 := by
  classical
  change
    (∑ e ∈ Finset.univ.filter (fun e ↦ P.packetOf e ∈ S),
      if G.Inc v e then G.weight e else 0) = _
  rw [Finset.sum_filter]
  calc
    (∑ e : G.E,
      if P.packetOf e ∈ S then
        (if G.Inc v e then G.weight e else 0) else 0) =
      ∑ p ∈ S, ∑ e : G.E,
        if P.packetOf e = p ∧ P.groupedGraph.Inc v p
          then G.weight e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases heS : P.packetOf e ∈ S
      · rw [Finset.sum_eq_single (P.packetOf e)]
        · have hinc := P.groupedGraph_inc_packetOf v e
          by_cases heinc : G.Inc v e
          · have hpinc := hinc.mpr heinc
            simp [heS, heinc, hpinc]
          · have hpinc : ¬P.groupedGraph.Inc v (P.packetOf e) :=
              fun h ↦ heinc (hinc.mp h)
            simp [heS, heinc, hpinc]
        · intro p _hpS hp
          simp [Ne.symm hp]
        · intro hnot
          exact (hnot heS).elim
      · have hzero :
          (∑ p ∈ S, if P.packetOf e = p ∧ P.groupedGraph.Inc v p
            then G.weight e else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro p hpS
          have hne : P.packetOf e ≠ p := fun h ↦ heS (h ▸ hpS)
          simp [hne]
        rw [hzero]
        simp [heS]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpinc : P.groupedGraph.Inc v p
      · simp [packetWeight, hpinc, and_comm]
      · simp [hpinc]

/-- Every restricted vertex--colour load is preserved exactly. -/
theorem colorLoadOn_originalEdgesOfPackets
    {q : ℕ} (S : Finset P.Packet) (color : P.Packet → Fin q)
    (v : G.V) (i : Fin q) :
    G.colorLoadOn (P.originalEdgesOfPackets S) (P.expandColor color) v i =
      P.groupedGraph.colorLoadOn S color v i := by
  classical
  unfold WeightedMultigraph.colorLoadOn
  change
    (∑ e ∈ Finset.univ.filter (fun e ↦ P.packetOf e ∈ S),
      if G.Inc v e ∧ color (P.packetOf e) = i
        then G.weight e else 0) = _
  rw [Finset.sum_filter]
  change
    (∑ e : G.E,
      if P.packetOf e ∈ S then
        (if G.Inc v e ∧ color (P.packetOf e) = i
          then G.weight e else 0) else 0) =
    ∑ p ∈ S,
      if P.groupedGraph.Inc v p ∧ color p = i
        then P.packetWeight p else 0
  calc
    _ = ∑ p ∈ S, ∑ e : G.E,
        if P.packetOf e = p ∧
            (P.groupedGraph.Inc v p ∧ color p = i)
          then G.weight e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases heS : P.packetOf e ∈ S
      · rw [Finset.sum_eq_single (P.packetOf e)]
        · have hinc := P.groupedGraph_inc_packetOf v e
          by_cases heinc : G.Inc v e
          · have hpinc := hinc.mpr heinc
            simp [heS, heinc, hpinc]
          · have hpinc : ¬P.groupedGraph.Inc v (P.packetOf e) :=
              fun h ↦ heinc (hinc.mp h)
            simp [heS, heinc, hpinc]
        · intro p _hpS hp
          simp [Ne.symm hp]
        · intro hnot
          exact (hnot heS).elim
      · have hzero :
          (∑ p ∈ S,
            if P.packetOf e = p ∧
                (P.groupedGraph.Inc v p ∧ color p = i)
              then G.weight e else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro p hpS
          have hne : P.packetOf e ≠ p := fun h ↦ heS (h ▸ hpS)
          simp [hne]
        rw [hzero]
        simp [heS]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpi : P.groupedGraph.Inc v p ∧ color p = i
      · simp [packetWeight, hpi, and_assoc]
      · simp [hpi]

theorem isFeasibleOn_originalEdgesOfPackets
    {q : ℕ} (S : Finset P.Packet) (color : P.Packet → Fin q)
    (hcolor : P.groupedGraph.IsFeasibleOn S color) :
    G.IsFeasibleOn (P.originalEdgesOfPackets S) (P.expandColor color) := by
  intro v i
  rw [P.colorLoadOn_originalEdgesOfPackets S color v i]
  exact hcolor v i

/-- A coloring of the whole packet graph expands to a weighted coloring of
all physical edges. -/
theorem isWeightedColoring_expandColor
    {q : ℕ} (color : P.Packet → Fin q)
    (hcolor : P.groupedGraph.IsWeightedColoring color) :
    G.IsWeightedColoring (P.expandColor color) := by
  have hpacket : P.groupedGraph.IsFeasibleOn Finset.univ color :=
    (P.groupedGraph.isWeightedColoring_iff_feasibleOn_univ color).1 hcolor
  have hphysical :=
    P.isFeasibleOn_originalEdgesOfPackets Finset.univ color hpacket
  have hphysical' :
      G.IsFeasibleOn Finset.univ (P.expandColor color) := by
    simpa [originalEdgesOfPackets] using hphysical
  exact (G.isWeightedColoring_iff_feasibleOn_univ
    (P.expandColor color)).2 hphysical'

theorem hasWeightedColoring_of_groupedGraph
    {q : ℕ} (h : P.groupedGraph.HasWeightedColoring q) :
    G.HasWeightedColoring q := by
  rcases h with ⟨color, hcolor⟩
  exact ⟨P.expandColor color, P.isWeightedColoring_expandColor color hcolor⟩

end Packetization

end WeightedMultigraph
end WeightedEdgeColoring
