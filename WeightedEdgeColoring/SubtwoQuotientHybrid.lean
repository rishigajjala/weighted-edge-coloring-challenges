import WeightedEdgeColoring.BPGeneralPacketCompletion
import WeightedEdgeColoring.BPEdgeRestriction



/-!
# A packet/core-residual/tiny hybrid without a bipartition

The left side of this hybrid consists of the packet labels of a colored base
on the non-tiny core.  Its right side is the joint residual from
`GeneralFiniteTinyJointResidual`: finite core residual objects together with
the endpoint-simple tiny objects.  Palette mixing therefore sees a proper
packet skeleton and the physical residual in one multigraph, without ever
asserting that the expanded packet coloring is an ordinary proper coloring.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u

namespace GeneralColoredPacketBase

variable {G : WeightedMultigraph.{u}} {K : ℕ}
variable (C : G.GeneralColoredPacketBase K)

/-- The graph whose left edges are core packet labels and whose right edges
are the joint residual objects. -/
def quotientHybridGraph : WeightedMultigraph.{u} where
  V := G.V
  E := C.packetization.Packet ⊕ C.residualGraph.E
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst
    | Sum.inl p => C.packetization.groupedGraph.fst p
    | Sum.inr e => C.residualGraph.fst e
  snd
    | Sum.inl p => C.packetization.groupedGraph.snd p
    | Sum.inr e => C.residualGraph.snd e
  noLoop
    | Sum.inl p => C.packetization.groupedGraph.noLoop p
    | Sum.inr e => C.residualGraph.noLoop e
  weight
    | Sum.inl p => C.packetization.groupedGraph.weight p
    | Sum.inr e => C.residualGraph.weight e
  weight_pos
    | Sum.inl p => C.packetization.groupedGraph.weight_pos p
    | Sum.inr e => C.residualGraph.weight_pos e
  weight_le_one
    | Sum.inl p => C.packetization.groupedGraph.weight_le_one p
    | Sum.inr e => C.residualGraph.weight_le_one e

/-- The selected, properly colored packet labels on the left side. -/
def quotientHybridPacketEdges : Finset C.quotientHybridGraph.E := by
  classical
  exact Finset.univ.filter fun e => match e with
    | Sum.inl p => p ∈ C.fullPackets
    | Sum.inr _ => False

/-- Every joint residual object, embedded on the right side. -/
def quotientHybridResidualEdges : Finset C.quotientHybridGraph.E := by
  classical
  exact Finset.univ.filter fun e => match e with
    | Sum.inl _ => False
    | Sum.inr _ => True

@[simp] theorem mem_quotientHybridPacketEdges_inl
    (p : C.packetization.Packet) :
    Sum.inl p ∈ C.quotientHybridPacketEdges ↔ p ∈ C.fullPackets := by
  simp [quotientHybridPacketEdges]

@[simp] theorem not_mem_quotientHybridPacketEdges_inr
    (e : C.residualGraph.E) :
    Sum.inr e ∉ C.quotientHybridPacketEdges := by
  simp [quotientHybridPacketEdges]

@[simp] theorem not_mem_quotientHybridResidualEdges_inl
    (p : C.packetization.Packet) :
    Sum.inl p ∉ C.quotientHybridResidualEdges := by
  simp [quotientHybridResidualEdges]

@[simp] theorem mem_quotientHybridResidualEdges_inr
    (e : C.residualGraph.E) :
    Sum.inr e ∈ C.quotientHybridResidualEdges := by
  simp [quotientHybridResidualEdges]

theorem quotientHybridPacketEdges_disjoint_residualEdges :
    Disjoint C.quotientHybridPacketEdges
      C.quotientHybridResidualEdges := by
  rw [Finset.disjoint_left]
  intro e heF heR
  rcases e with p | e
  · exact C.not_mem_quotientHybridResidualEdges_inl p heR
  · exact C.not_mem_quotientHybridPacketEdges_inr e heF

/-- Extend the packet coloring arbitrarily to the residual side. -/
def quotientHybridBaseColor : C.quotientHybridGraph.E → Fin K
  | Sum.inl p => C.packetColor p
  | Sum.inr _ => ⟨0, C.palette_pos⟩

/-- Properness used by palette mixing is exactly packet-level properness. -/
theorem quotientHybridBaseColor_isProperOn :
    C.quotientHybridGraph.IsProperOn C.quotientHybridPacketEdges
      C.quotientHybridBaseColor := by
  intro v e he f hf hef
  rcases e with p | e
  · rcases f with q | f
    · apply congrArg Sum.inl
      apply C.packetProper v
      · have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨(C.mem_quotientHybridPacketEdges_inl p).1 he'.1,
            by simpa [quotientHybridGraph] using he'.2⟩)
      · have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨(C.mem_quotientHybridPacketEdges_inl q).1 hf'.1,
            by simpa [quotientHybridGraph] using hf'.2⟩)
      · simpa [quotientHybridBaseColor] using hef
    · have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
      exact (C.not_mem_quotientHybridPacketEdges_inr f hf'.1).elim
  · have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    exact (C.not_mem_quotientHybridPacketEdges_inr e he'.1).elim

/-- Missing colors on the hybrid packet side are the missing colors of the
selected packet labels in the core packet graph. -/
theorem quotientHybrid_missingColorsAt_eq_packetGraph
    {q : ℕ} (color : C.quotientHybridGraph.E → Fin q) (v : G.V) :
    C.quotientHybridGraph.missingColorsAt
        C.quotientHybridPacketEdges color v =
      C.packetization.groupedGraph.missingColorsAt C.fullPackets
        (fun p => color (Sum.inl p)) v := by
  classical
  unfold missingColorsAt
  congr 1
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨e, he, rfl⟩
    rcases e with p | e
    · apply Finset.mem_image.mpr
      refine ⟨p, ?_, rfl⟩
      have he' := Finset.mem_filter.mp he
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · exact (C.mem_quotientHybridPacketEdges_inl p).1 he'.1
      · simpa [quotientHybridGraph] using he'.2
    · exact (C.not_mem_quotientHybridPacketEdges_inr e
        (Finset.mem_filter.mp he).1).elim
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl p, ?_, rfl⟩
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact (C.mem_quotientHybridPacketEdges_inl p).2 hp'.1
    · simpa [quotientHybridGraph] using hp'.2

/-- The hybrid missing palette is the packet-base missing palette. -/
theorem quotientHybrid_missingColorsAt_eq_base (v : G.V) :
    C.quotientHybridGraph.missingColorsAt
      C.quotientHybridPacketEdges C.quotientHybridBaseColor v =
    G.missingColorsAt C.fullEdges C.baseColor v := by
  calc
    _ = C.packetization.groupedGraph.missingColorsAt C.fullPackets
        C.packetColor v := by
      simpa [quotientHybridBaseColor] using
        C.quotientHybrid_missingColorsAt_eq_packetGraph
          C.quotientHybridBaseColor v
    _ = _ := (C.packetization.missingColorsAt_originalEdgesOfPackets
      C.fullPackets C.packetColor v).symm

/-- Repackage a mixed proper packet coloring as a colored core packet base.
The packetization and selected packet set, hence the residual, are unchanged. -/
def quotientRecoloredBase
    (mixed : C.quotientHybridGraph.E → Fin K)
    (hmixed : C.quotientHybridGraph.IsProperOn
      C.quotientHybridPacketEdges mixed) :
    G.GeneralColoredPacketBase K where
  packetization := C.packetization
  fullPackets := C.fullPackets
  palette_pos := C.palette_pos
  packetColor := fun p => mixed (Sum.inl p)
  packetProper := by
    intro v p hp q hq heq
    apply Sum.inl_injective
    apply hmixed v
    · apply Finset.mem_filter.mpr
      exact ⟨(C.mem_quotientHybridPacketEdges_inl p).2
        (Finset.mem_filter.mp hp).1,
        by simpa [quotientHybridGraph] using (Finset.mem_filter.mp hp).2⟩
    · apply Finset.mem_filter.mpr
      exact ⟨(C.mem_quotientHybridPacketEdges_inl q).2
        (Finset.mem_filter.mp hq).1,
        by simpa [quotientHybridGraph] using (Finset.mem_filter.mp hq).2⟩
    · exact heq

@[simp] theorem quotientRecoloredBase_fullPackets
    (mixed : C.quotientHybridGraph.E → Fin K)
    (hmixed : C.quotientHybridGraph.IsProperOn
      C.quotientHybridPacketEdges mixed) :
    (C.quotientRecoloredBase mixed hmixed).fullPackets = C.fullPackets := rfl

@[simp] theorem quotientRecoloredBase_residualEdges
    (mixed : C.quotientHybridGraph.E → Fin K)
    (hmixed : C.quotientHybridGraph.IsProperOn
      C.quotientHybridPacketEdges mixed) :
    (C.quotientRecoloredBase mixed hmixed).residualEdges = C.residualEdges := rfl

/-- Recoloring changes only packet colors, not the residual edge set. -/
theorem quotientRecolored_missingColorsAt_eq_hybrid
    (mixed : C.quotientHybridGraph.E → Fin K)
    (hmixed : C.quotientHybridGraph.IsProperOn
      C.quotientHybridPacketEdges mixed) (v : G.V) :
    G.missingColorsAt (C.quotientRecoloredBase mixed hmixed).fullEdges
      (C.quotientRecoloredBase mixed hmixed).baseColor v =
    C.quotientHybridGraph.missingColorsAt
      C.quotientHybridPacketEdges mixed v := by
  calc
    _ = C.packetization.groupedGraph.missingColorsAt C.fullPackets
        (fun p => mixed (Sum.inl p)) v := by
      simpa [quotientRecoloredBase] using
        C.packetization.missingColorsAt_originalEdgesOfPackets
          C.fullPackets (fun p => mixed (Sum.inl p)) v
    _ = _ :=
      (C.quotientHybrid_missingColorsAt_eq_packetGraph mixed v).symm

end GeneralColoredPacketBase

end

end WeightedMultigraph
end WeightedEdgeColoring
