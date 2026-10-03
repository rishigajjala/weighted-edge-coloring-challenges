import WeightedEdgeColoring.SubtwoPacketQuotient
import WeightedEdgeColoring.SubtwoPacketLifting
import WeightedEdgeColoring.BPGeneralPacketCompletion
import WeightedEdgeColoring.SubtwoUnconditionalPhysicalPackets

/-! The selected quotient packet coloring is an actual colored packet base
on the physical contracted multigraph. -/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable {G : WeightedMultigraph.{u}}
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

namespace Packetization

variable (P : G.Packetization)

/-- A proper coloring of selected crossing original packets gives a colored
packet base on the physical quotient, with the same packet indices and colors. -/
noncomputable def subtwoQuotientColoredPacketBase
    {k : ℕ} (hk : 0 < k) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color) :
    (G.subtwoQuotient block).GeneralColoredPacketBase k where
  packetization := P.subtwoQuotientPacketization block
  fullPackets := P.groupedGraph.subtwoQuotientSelectedEdges block S
  palette_pos := hk
  packetColor := color
  packetProper := P.subtwoQuotientPacketization_properOn block
    (P.groupedGraph.subtwoQuotientSelectedEdges block S) color hproper

theorem subtwoQuotientColoredPacketBase_fullEdges
    {k : ℕ} (hk : 0 < k) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color) :
    (P.subtwoQuotientColoredPacketBase hk block S color hproper).fullEdges =
      G.subtwoQuotientSelectedEdges block (P.originalEdgesOfPackets S) := by
  exact P.subtwoQuotientPacketization_selectedEdges block S

theorem subtwoQuotientColoredPacketBase_baseColor
    {k : ℕ} (hk : 0 < k) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    (e : (G.subtwoQuotient block).E) :
    (P.subtwoQuotientColoredPacketBase hk block S color hproper).baseColor e =
      color ⟨P.packetOf e.1, (P.packetOf_crossing_iff block e.1).2 e.2⟩ := by
  rfl

end Packetization

/-- The actual full floor-packet quotient coloring is a colored packet base
on the physical quotient. -/
noncomputable def subtwoFloorPhysicalColoredPacketBase
    (G : WeightedMultigraph.{u}) {k : ℕ} (hk : 0 < k) (n : ℕ)
    (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color) :
    (G.subtwoQuotient (G.subtwoFloorBlock n)).GeneralColoredPacketBase k :=
  G.floorPacketization.subtwoQuotientColoredPacketBase hk
    (G.subtwoFloorBlock n) G.fullFloorPacketSet color hproper

theorem subtwoFloorPhysicalColoredPacketBase_fullEdges
    (G : WeightedMultigraph.{u}) {k : ℕ} (hk : 0 < k) (n : ℕ)
    (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color) :
    (G.subtwoFloorPhysicalColoredPacketBase hk n color hproper).fullEdges =
      G.subtwoQuotientSelectedEdges (G.subtwoFloorBlock n)
        (G.subtwoFloorBaseEdges n) := by
  classical
  ext e
  simp [subtwoFloorPhysicalColoredPacketBase,
    Packetization.subtwoQuotientColoredPacketBase_fullEdges,
    subtwoQuotientSelectedEdges, subtwoFloorBaseEdges,
    Packetization.originalEdgesOfPackets,
    subtwoCrossingSelectedEdges]
  intro _
  exact (G.floorPacketization.packetOf_crossing_iff
    (G.subtwoFloorBlock n) e.1).2 e.2

/-- The ordinary quotient coloring theorem supplies an actual physical
quotient packet base with the same uniform palette bound. -/
theorem exists_subtwoFloorPhysicalColoredPacketBase_uniform
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n : ℕ),
      N ≤ n → G.LocallyPacksInto n →
      ∃ k : ℕ, ∃ C :
        (G.subtwoQuotient (G.subtwoFloorBlock n)).GeneralColoredPacketBase k,
        (k : ℝ) ≤ (subtwoKappa + eta) * n ∧
          C.fullEdges = G.subtwoQuotientSelectedEdges
            (G.subtwoFloorBlock n) (G.subtwoFloorBaseEdges n) := by
  obtain ⟨N, hN⟩ := exists_subtwoFloorBaseColor_uniform.{u} eta heta
  refine ⟨N, ?_⟩
  intro G n hn hlocal
  obtain ⟨k, hk, hbound, color, hproper, _, _⟩ := hN G n hn hlocal
  let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
  refine ⟨k, C, hbound, ?_⟩
  exact G.subtwoFloorPhysicalColoredPacketBase_fullEdges hk n color hproper

end WeightedEdgeColoring.WeightedMultigraph
