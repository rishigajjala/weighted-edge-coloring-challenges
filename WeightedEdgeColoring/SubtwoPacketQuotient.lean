import WeightedEdgeColoring.GeneralPacketization
import WeightedEdgeColoring.SubtwoContraction
import WeightedEdgeColoring.SubtwoPacketLifting

/-! Contracting a packetization retains precisely the crossing packets. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section

universe u
variable {G : WeightedMultigraph.{u}}
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

namespace Packetization

variable (P : G.Packetization)

theorem packetOf_endpoints (e : G.E) :
    (P.tail (P.packetOf e) = G.fst e ∧
      P.head (P.packetOf e) = G.snd e) ∨
    (P.tail (P.packetOf e) = G.snd e ∧
      P.head (P.packetOf e) = G.fst e) := by
  have hf : P.tail (P.packetOf e) = G.fst e ∨
      P.head (P.packetOf e) = G.fst e :=
    (P.incidence (G.fst e) e).2 (Or.inl rfl)
  have hs : P.tail (P.packetOf e) = G.snd e ∨
      P.head (P.packetOf e) = G.snd e :=
    (P.incidence (G.snd e) e).2 (Or.inr rfl)
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · exact (G.noLoop e (hf.symm.trans hs)).elim
  · exact Or.inl ⟨hf, hs⟩
  · exact Or.inr ⟨hs, hf⟩
  · exact (G.noLoop e (hf.symm.trans hs)).elim

theorem packetOf_crossing_iff (block : G.V → Q) (e : G.E) :
    block (P.tail (P.packetOf e)) ≠
        block (P.head (P.packetOf e)) ↔
      block (G.fst e) ≠ block (G.snd e) := by
  rcases P.packetOf_endpoints e with h | h
  · simp [h.1, h.2]
  · simpa [h.1, h.2, ne_comm]

/-- Original packets on crossing edges form an exact packetization of the
physical quotient. Its packet index is the crossing-edge type of the
quotient grouped graph. -/
def subtwoQuotientPacketization (block : G.V → Q) :
    (G.subtwoQuotient block).Packetization where
  Packet := (P.groupedGraph.subtwoQuotient block).E
  instFintypePacket := inferInstance
  instDecidableEqPacket := inferInstance
  packetOf := fun e =>
    ⟨P.packetOf e.1, (P.packetOf_crossing_iff block e.1).2 e.2⟩
  tail := fun p => block (P.tail p.1)
  head := fun p => block (P.head p.1)
  noLoop := fun p => p.2
  incidence := by
    intro q e
    rcases P.packetOf_endpoints e.1 with h | h
    · change block (P.tail (P.packetOf e.1)) = q ∨
          block (P.head (P.packetOf e.1)) = q ↔
          block (G.fst e.1) = q ∨ block (G.snd e.1) = q
      simp [h.1, h.2]
    · change block (P.tail (P.packetOf e.1)) = q ∨
          block (P.head (P.packetOf e.1)) = q ↔
          block (G.fst e.1) = q ∨ block (G.snd e.1) = q
      simp [h.1, h.2, or_comm]
  onto := by
    intro p
    obtain ⟨e, he⟩ := P.onto p.1
    have hc : block (G.fst e) ≠ block (G.snd e) := by
      apply (P.packetOf_crossing_iff block e).1
      simpa [he] using p.2
    refine ⟨⟨e, hc⟩, ?_⟩
    apply Subtype.ext
    exact he
  weight_le_one := by
    intro p
    have heq :
        (∑ e : (G.subtwoQuotient block).E,
          if (⟨P.packetOf e.1,
              (P.packetOf_crossing_iff block e.1).2 e.2⟩ :
                (P.groupedGraph.subtwoQuotient block).E) = p
            then (G.subtwoQuotient block).weight e else 0) =
          P.packetWeight p.1 := by
      have hsum :
          (∑ e : (G.subtwoQuotient block).E,
            if (⟨P.packetOf e.1,
                (P.packetOf_crossing_iff block e.1).2 e.2⟩ :
                  (P.groupedGraph.subtwoQuotient block).E) = p
              then (G.subtwoQuotient block).weight e else 0) =
            ∑ e : (G.subtwoQuotient block).E,
              if P.packetOf e.1 = p.1 then G.weight e.1 else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases hp : P.packetOf e.1 = p.1
        · have hsub :
            (⟨P.packetOf e.1,
              (P.packetOf_crossing_iff block e.1).2 e.2⟩ :
                (P.groupedGraph.subtwoQuotient block).E) = p :=
            Subtype.ext hp
          simp [hp, hsub, subtwoQuotient]
        · have hsub :
            (⟨P.packetOf e.1,
              (P.packetOf_crossing_iff block e.1).2 e.2⟩ :
                (P.groupedGraph.subtwoQuotient block).E) ≠ p := by
            intro he
            exact hp (congrArg Subtype.val he)
          simp [hp, hsub]
      rw [hsum]
      have hquotient :
          (∑ e : (G.subtwoQuotient block).E,
            if P.packetOf e.1 = p.1 then G.weight e.1 else 0) =
          ∑ e : G.E,
            if block (G.fst e) ≠ block (G.snd e) then
              (if P.packetOf e = p.1 then G.weight e else 0) else 0 := by
        exact G.subtwo_sum_quotient_edges block
          (fun e => if P.packetOf e = p.1 then G.weight e else 0)
      rw [hquotient]
      unfold packetWeight
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : P.packetOf e = p.1
      · have hc : block (G.fst e) ≠ block (G.snd e) := by
          apply (P.packetOf_crossing_iff block e).1
          simpa [hp] using p.2
        simp [hp, hc]
      · by_cases hc : block (G.fst e) ≠ block (G.snd e)
        · simp [hp, hc]
        · simp [hp, hc]
    exact heq.trans_le (P.packetWeight_le_one p.1)

theorem subtwoQuotientPacketization_packetWeight (block : G.V → Q)
    (p : (P.groupedGraph.subtwoQuotient block).E) :
    (P.subtwoQuotientPacketization block).packetWeight p = P.packetWeight p.1 := by
  classical
  change (∑ e : (G.subtwoQuotient block).E,
    if (⟨P.packetOf e.1,
        (P.packetOf_crossing_iff block e.1).2 e.2⟩ :
        (P.groupedGraph.subtwoQuotient block).E) = p
      then (G.subtwoQuotient block).weight e else 0) = P.packetWeight p.1
  calc
    _ = ∑ e : (G.subtwoQuotient block).E,
        if P.packetOf e.1 = p.1 then G.weight e.1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : P.packetOf e.1 = p.1
      · have hsub :
          (⟨P.packetOf e.1, (P.packetOf_crossing_iff block e.1).2 e.2⟩ :
            (P.groupedGraph.subtwoQuotient block).E) = p := Subtype.ext hp
        simp [hp, hsub, subtwoQuotient]
      · have hsub :
          (⟨P.packetOf e.1, (P.packetOf_crossing_iff block e.1).2 e.2⟩ :
            (P.groupedGraph.subtwoQuotient block).E) ≠ p := by
          intro he
          exact hp (congrArg Subtype.val he)
        simp [hp, hsub]
    _ = ∑ e : G.E,
        if block (G.fst e) ≠ block (G.snd e) then
          (if P.packetOf e = p.1 then G.weight e else 0) else 0 :=
      G.subtwo_sum_quotient_edges block
        (fun e => if P.packetOf e = p.1 then G.weight e else 0)
    _ = P.packetWeight p.1 := by
      unfold packetWeight
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : P.packetOf e = p.1
      · have hc : block (G.fst e) ≠ block (G.snd e) := by
          apply (P.packetOf_crossing_iff block e).1
          simpa [hp] using p.2
        simp [hp, hc]
      · by_cases hc : block (G.fst e) ≠ block (G.snd e)
        · simp [hp, hc]
        · simp [hp, hc]

/-- The two grouped quotient graphs have the same packet incidence.  Their
weight fields also agree, although properness needs only incidence. -/
theorem subtwoQuotientPacketization_incidence (block : G.V → Q)
    (q : Q) (p : (P.groupedGraph.subtwoQuotient block).E) :
    (P.subtwoQuotientPacketization block).groupedGraph.Inc q p ↔
      (P.groupedGraph.subtwoQuotient block).Inc q p := by
  rfl

theorem subtwoQuotientPacketization_properOn (block : G.V → Q)
    {k : ℕ} (S : Finset (P.groupedGraph.subtwoQuotient block).E)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn S color) :
    (P.subtwoQuotientPacketization block).groupedGraph.IsProperOn S color := by
  intro q e he f hf hcolor
  exact hproper q (by simpa only [P.subtwoQuotientPacketization_incidence block] using he)
    (by simpa only [P.subtwoQuotientPacketization_incidence block] using hf) hcolor

theorem subtwoQuotientPacketization_selectedEdges (block : G.V → Q)
    (S : Finset P.Packet) :
    (P.subtwoQuotientPacketization block).originalEdgesOfPackets
        (P.groupedGraph.subtwoQuotientSelectedEdges block S) =
      G.subtwoQuotientSelectedEdges block (P.originalEdgesOfPackets S) := by
  classical
  ext e
  simp [originalEdgesOfPackets, subtwoQuotientPacketization,
    WeightedMultigraph.subtwoQuotientSelectedEdges]

end Packetization
end
end WeightedEdgeColoring.WeightedMultigraph
