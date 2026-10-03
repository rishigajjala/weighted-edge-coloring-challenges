import WeightedEdgeColoring.GeneralFiniteTinyJointResidual
import WeightedEdgeColoring.FiniteClassesTinyProposalLocalPolytope
import WeightedEdgeColoring.WeightedMomentPaletteMixingProof

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

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
variable {P : G.GeneralTinyThresholdPacketization tau}
variable {K : ℕ}
variable (C : P.coreObjectGraph.GeneralColoredPacketBase K)

/-- The graph whose left edges are core packet labels and whose right edges
are the joint residual objects. -/
def finiteTinyHybridGraph : WeightedMultigraph.{u} where
  V := G.V
  E := C.packetization.Packet ⊕ C.jointResidualGraph.E
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst
    | Sum.inl p => C.packetization.groupedGraph.fst p
    | Sum.inr e => C.jointResidualGraph.fst e
  snd
    | Sum.inl p => C.packetization.groupedGraph.snd p
    | Sum.inr e => C.jointResidualGraph.snd e
  noLoop
    | Sum.inl p => C.packetization.groupedGraph.noLoop p
    | Sum.inr e => C.jointResidualGraph.noLoop e
  weight
    | Sum.inl p => C.packetization.groupedGraph.weight p
    | Sum.inr e => C.jointResidualGraph.weight e
  weight_pos
    | Sum.inl p => C.packetization.groupedGraph.weight_pos p
    | Sum.inr e => C.jointResidualGraph.weight_pos e
  weight_le_one
    | Sum.inl p => C.packetization.groupedGraph.weight_le_one p
    | Sum.inr e => C.jointResidualGraph.weight_le_one e

/-- The selected, properly colored packet labels on the left side. -/
def finiteTinyHybridPacketEdges : Finset C.finiteTinyHybridGraph.E := by
  classical
  exact Finset.univ.filter fun e => match e with
    | Sum.inl p => p ∈ C.fullPackets
    | Sum.inr _ => False

/-- Every joint residual object, embedded on the right side. -/
def finiteTinyHybridResidualEdges : Finset C.finiteTinyHybridGraph.E := by
  classical
  exact Finset.univ.filter fun e => match e with
    | Sum.inl _ => False
    | Sum.inr _ => True

@[simp] theorem mem_finiteTinyHybridPacketEdges_inl
    (p : C.packetization.Packet) :
    Sum.inl p ∈ C.finiteTinyHybridPacketEdges ↔ p ∈ C.fullPackets := by
  simp [finiteTinyHybridPacketEdges]

@[simp] theorem not_mem_finiteTinyHybridPacketEdges_inr
    (e : C.jointResidualGraph.E) :
    Sum.inr e ∉ C.finiteTinyHybridPacketEdges := by
  simp [finiteTinyHybridPacketEdges]

@[simp] theorem not_mem_finiteTinyHybridResidualEdges_inl
    (p : C.packetization.Packet) :
    Sum.inl p ∉ C.finiteTinyHybridResidualEdges := by
  simp [finiteTinyHybridResidualEdges]

@[simp] theorem mem_finiteTinyHybridResidualEdges_inr
    (e : C.jointResidualGraph.E) :
    Sum.inr e ∈ C.finiteTinyHybridResidualEdges := by
  simp [finiteTinyHybridResidualEdges]

theorem finiteTinyHybridPacketEdges_disjoint_residualEdges :
    Disjoint C.finiteTinyHybridPacketEdges
      C.finiteTinyHybridResidualEdges := by
  rw [Finset.disjoint_left]
  intro e heF heR
  rcases e with p | e
  · exact C.not_mem_finiteTinyHybridResidualEdges_inl p heR
  · exact C.not_mem_finiteTinyHybridPacketEdges_inr e heF

/-- Extend the packet coloring arbitrarily to the residual side. -/
def finiteTinyHybridBaseColor : C.finiteTinyHybridGraph.E → Fin K
  | Sum.inl p => C.packetColor p
  | Sum.inr _ => ⟨0, C.palette_pos⟩

/-- Properness used by palette mixing is exactly packet-level properness. -/
theorem finiteTinyHybridBaseColor_isProperOn :
    C.finiteTinyHybridGraph.IsProperOn C.finiteTinyHybridPacketEdges
      C.finiteTinyHybridBaseColor := by
  intro v e he f hf hef
  rcases e with p | e
  · rcases f with q | f
    · apply congrArg Sum.inl
      apply C.packetProper v
      · have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨(C.mem_finiteTinyHybridPacketEdges_inl p).1 he'.1,
            by simpa [finiteTinyHybridGraph] using he'.2⟩)
      · have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
        exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
          ⟨(C.mem_finiteTinyHybridPacketEdges_inl q).1 hf'.1,
            by simpa [finiteTinyHybridGraph] using hf'.2⟩)
      · simpa [finiteTinyHybridBaseColor] using hef
    · have hf' := Finset.mem_filter.mp (Finset.mem_coe.mp hf)
      exact (C.not_mem_finiteTinyHybridPacketEdges_inr f hf'.1).elim
  · have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
    exact (C.not_mem_finiteTinyHybridPacketEdges_inr e he'.1).elim

/-- Missing colors on the hybrid packet side are the missing colors of the
selected packet labels in the core packet graph. -/
theorem finiteTinyHybrid_missingColorsAt_eq_packetGraph
    {q : ℕ} (color : C.finiteTinyHybridGraph.E → Fin q) (v : G.V) :
    C.finiteTinyHybridGraph.missingColorsAt
        C.finiteTinyHybridPacketEdges color v =
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
      · exact (C.mem_finiteTinyHybridPacketEdges_inl p).1 he'.1
      · exact he'.2
    · exact (C.not_mem_finiteTinyHybridPacketEdges_inr e
        (Finset.mem_filter.mp he).1).elim
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl p, ?_, rfl⟩
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact (C.mem_finiteTinyHybridPacketEdges_inl p).2 hp'.1
    · exact hp'.2

/-- The initial hybrid missing palette is exactly the ambient missing
palette of the expanded full core packets. -/
theorem finiteTinyHybrid_missingColorsAt_eq_ambientBase (v : G.V) :
    C.finiteTinyHybridGraph.missingColorsAt
        C.finiteTinyHybridPacketEdges C.finiteTinyHybridBaseColor v =
      P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        C.ambientBaseColor v := by
  calc
    _ = C.packetization.groupedGraph.missingColorsAt C.fullPackets
        C.packetColor v := by
      simpa [finiteTinyHybridBaseColor] using
        C.finiteTinyHybrid_missingColorsAt_eq_packetGraph
          C.finiteTinyHybridBaseColor v
    _ = P.coreObjectGraph.missingColorsAt C.fullEdges C.baseColor v := by
      exact (C.packetization.missingColorsAt_originalEdgesOfPackets
        C.fullPackets C.packetColor v).symm
    _ = _ := (C.ambient_missingColorsAt_eq_core v).symm

/-- Repackage a mixed proper packet coloring as a colored core packet base.
The packetization and selected packet set, hence the residual, are unchanged. -/
def finiteTinyRecoloredBase
    (mixed : C.finiteTinyHybridGraph.E → Fin K)
    (hmixed : C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges mixed) :
    P.coreObjectGraph.GeneralColoredPacketBase K where
  packetization := C.packetization
  fullPackets := C.fullPackets
  palette_pos := C.palette_pos
  packetColor := fun p => mixed (Sum.inl p)
  packetProper := by
    intro v p hp q hq heq
    apply Sum.inl_injective
    apply hmixed v
    · apply Finset.mem_filter.mpr
      exact ⟨(C.mem_finiteTinyHybridPacketEdges_inl p).2
        (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    · apply Finset.mem_filter.mpr
      exact ⟨(C.mem_finiteTinyHybridPacketEdges_inl q).2
        (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩
    · exact heq

@[simp] theorem finiteTinyRecoloredBase_fullPackets
    (mixed : C.finiteTinyHybridGraph.E → Fin K)
    (hmixed : C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges mixed) :
    (C.finiteTinyRecoloredBase mixed hmixed).fullPackets = C.fullPackets := rfl

@[simp] theorem finiteTinyRecoloredBase_residualEdges
    (mixed : C.finiteTinyHybridGraph.E → Fin K)
    (hmixed : C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges mixed) :
    (C.finiteTinyRecoloredBase mixed hmixed).residualEdges = C.residualEdges := rfl

/-- After mixing, the ambient missing palette of the recolored core base is
the hybrid missing palette of the mixed packet coloring. -/
theorem finiteTinyRecolored_missingColorsAt_eq_hybrid
    (mixed : C.finiteTinyHybridGraph.E → Fin K)
    (hmixed : C.finiteTinyHybridGraph.IsProperOn
      C.finiteTinyHybridPacketEdges mixed) (v : G.V) :
    P.mixedObjectGraph.missingColorsAt
        (C.finiteTinyRecoloredBase mixed hmixed).fullCoreObjects
        (C.finiteTinyRecoloredBase mixed hmixed).ambientBaseColor v =
      C.finiteTinyHybridGraph.missingColorsAt
        C.finiteTinyHybridPacketEdges mixed v := by
  let C' := C.finiteTinyRecoloredBase mixed hmixed
  calc
    P.mixedObjectGraph.missingColorsAt C'.fullCoreObjects
        C'.ambientBaseColor v =
        P.coreObjectGraph.missingColorsAt C'.fullEdges C'.baseColor v :=
      C'.ambient_missingColorsAt_eq_core v
    _ = C.packetization.groupedGraph.missingColorsAt C.fullPackets
        (fun p => mixed (Sum.inl p)) v := by
      simpa [C', finiteTinyRecoloredBase] using
        C.packetization.missingColorsAt_originalEdgesOfPackets
          C.fullPackets (fun p => mixed (Sum.inl p)) v
    _ = _ :=
      (C.finiteTinyHybrid_missingColorsAt_eq_packetGraph mixed v).symm

end GeneralColoredPacketBase

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.WeightedMultigraph.GeneralColoredPacketBase.finiteTinyRecolored_missingColorsAt_eq_hybrid
