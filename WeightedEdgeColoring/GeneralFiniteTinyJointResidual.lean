import WeightedEdgeColoring.GeneralTinyThresholdCombined
import WeightedEdgeColoring.BPGeneralPacketCompletion
import WeightedEdgeColoring.EdgeRestrictionPairMultiplicityUnion
import WeightedEdgeColoring.BPEdgeRestriction
import WeightedEdgeColoring.SamePaletteResidualAdapter

/-!
# A general finite-core and endpoint-simple tiny residual

A colored packet base may be built on the non-tiny core of a general
tiny-threshold packetization.  This file embeds its full and residual core
objects back into the mixed-object graph and joins the core residual to the
endpoint-simple tiny remainder.  No bipartition is used.
-/

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

/-- Full core objects, embedded in the ambient mixed-object graph. -/
def fullCoreObjects : Finset P.Object :=
  P.mixedObjectGraph.liftRestrictionFinset P.coreObjects C.fullEdges

/-- Residual core objects, embedded in the ambient mixed-object graph. -/
def residualCoreObjects : Finset P.Object :=
  P.mixedObjectGraph.liftRestrictionFinset P.coreObjects C.residualEdges

/-- The residual used by mixing and rounding: the core residual together
with the endpoint-simple tiny objects. -/
def jointResidualObjects : Finset P.Object :=
  C.residualCoreObjects ∪ P.smallObjects

/-- Lift the expanded core packet coloring to all mixed objects. -/
def ambientBaseColor : P.Object → Fin K :=
  P.mixedObjectGraph.liftRestrictedColor C.palette_pos P.coreObjects C.baseColor

theorem fullCoreObjects_disjoint_residualCoreObjects :
    Disjoint C.fullCoreObjects C.residualCoreObjects := by
  rw [Finset.disjoint_left]
  intro o hoF hoR
  rcases (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
    P.coreObjects C.fullEdges o).mp hoF with ⟨hoCore, hoFull⟩
  rcases (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
    P.coreObjects C.residualEdges o).mp hoR with ⟨_hoCore', hoResidual⟩
  exact Finset.disjoint_left.mp C.fullEdges_disjoint_residualEdges
    hoFull hoResidual

theorem fullCoreObjects_disjoint_smallObjects :
    Disjoint C.fullCoreObjects P.smallObjects := by
  rw [Finset.disjoint_left]
  intro o hoF hoSmall
  have hoCore := P.mixedObjectGraph.liftRestrictionFinset_subset
    P.coreObjects C.fullEdges hoF
  exact (Finset.mem_sdiff.mp hoCore).2 hoSmall

theorem fullCoreObjects_disjoint_jointResidualObjects :
    Disjoint C.fullCoreObjects C.jointResidualObjects := by
  rw [jointResidualObjects, Finset.disjoint_union_right]
  exact ⟨C.fullCoreObjects_disjoint_residualCoreObjects,
    C.fullCoreObjects_disjoint_smallObjects⟩

theorem fullCoreObjects_union_residualCoreObjects :
    C.fullCoreObjects ∪ C.residualCoreObjects = P.coreObjects := by
  ext o
  constructor
  · intro ho
    rcases Finset.mem_union.mp ho with ho | ho
    · exact P.mixedObjectGraph.liftRestrictionFinset_subset
        P.coreObjects C.fullEdges ho
    · exact P.mixedObjectGraph.liftRestrictionFinset_subset
        P.coreObjects C.residualEdges ho
  · intro hoCore
    have hsub : (⟨o, hoCore⟩ : P.coreObjectGraph.E) ∈
        C.fullEdges ∪ C.residualEdges := by
      rw [C.fullEdges_union_residualEdges]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hsub with ho | ho
    · exact Finset.mem_union_left _
        ((P.mixedObjectGraph.mem_liftRestrictionFinset_iff
          P.coreObjects C.fullEdges o).mpr ⟨hoCore, ho⟩)
    · exact Finset.mem_union_right _
        ((P.mixedObjectGraph.mem_liftRestrictionFinset_iff
          P.coreObjects C.residualEdges o).mpr ⟨hoCore, ho⟩)

theorem fullCoreObjects_union_jointResidualObjects :
    C.fullCoreObjects ∪ C.jointResidualObjects = Finset.univ := by
  rw [jointResidualObjects, ← Finset.union_assoc,
    C.fullCoreObjects_union_residualCoreObjects]
  exact Finset.sdiff_union_of_subset (Finset.subset_univ P.smallObjects)

theorem ambientBaseColor_feasibleOn :
    P.mixedObjectGraph.IsFeasibleOn C.fullCoreObjects C.ambientBaseColor := by
  exact P.mixedObjectGraph.feasibleOn_liftRestrictionFinset C.palette_pos
    P.coreObjects C.fullEdges C.baseColor C.baseColor_feasibleOn

/-- Lifting the core edge set and its expanded packet coloring to the
ambient mixed-object graph preserves the missing palette exactly. -/
theorem ambient_missingColorsAt_eq_core (v : G.V) :
    P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        C.ambientBaseColor v =
      P.coreObjectGraph.missingColorsAt C.fullEdges C.baseColor v := by
  classical
  unfold missingColorsAt
  congr 1
  ext c
  constructor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨e, he, hcolor⟩
    have he' := Finset.mem_filter.mp he
    rcases (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
      P.coreObjects C.fullEdges e).mp he'.1 with ⟨heCore, heFull⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨e, heCore⟩, Finset.mem_filter.mpr ⟨heFull, ?_⟩, ?_⟩
    · exact he'.2
    · simpa [ambientBaseColor, liftRestrictedColor, heCore] using hcolor
  · intro hc
    rcases Finset.mem_image.mp hc with ⟨e, he, hcolor⟩
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_image.mpr
    refine ⟨e.1, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
        P.coreObjects C.fullEdges e.1).mpr ⟨e.2, he'.1⟩
    · exact he'.2
    · simpa [ambientBaseColor, liftRestrictedColor, e.2] using hcolor

/-- The one residual multigraph seen simultaneously by palette mixing and
whole-edge rounding. -/
abbrev jointResidualGraph : WeightedMultigraph.{u} :=
  P.mixedObjectGraph.edgeRestriction C.jointResidualObjects

/-- The predicate separating the finite core residual from the tiny part. -/
def isFiniteCoreResidual (e : C.jointResidualGraph.E) : Prop :=
  e.1 ∈ C.residualCoreObjects

instance instDecidableIsFiniteCoreResidual :
    DecidablePred C.isFiniteCoreResidual := by
  intro e
  exact Finset.decidableMem e.1 C.residualCoreObjects

/-- Recover the core-restriction edge represented by a finite joint edge. -/
def jointFiniteCoreEdge
    (e : {e : C.jointResidualGraph.E // C.isFiniteCoreResidual e}) :
    P.coreObjectGraph.E :=
  ⟨e.1.1, (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
    P.coreObjects C.residualEdges e.1.1).mp e.2 |>.choose⟩

theorem jointFiniteCoreEdge_mem_residual
    (e : {e : C.jointResidualGraph.E // C.isFiniteCoreResidual e}) :
    C.jointFiniteCoreEdge e ∈ C.residualEdges := by
  exact (P.mixedObjectGraph.mem_liftRestrictionFinset_iff
    P.coreObjects C.residualEdges e.1.1).mp e.2 |>.choose_spec

@[simp] theorem jointFiniteCoreEdge_weight
    (e : {e : C.jointResidualGraph.E // C.isFiniteCoreResidual e}) :
    P.coreObjectGraph.weight (C.jointFiniteCoreEdge e) =
      C.jointResidualGraph.weight e.1 := rfl

/-- A joint-residual edge outside the finite core residual is tiny. -/
theorem jointResidual_mem_small_of_not_finite
    (e : C.jointResidualGraph.E) (he : ¬ C.isFiniteCoreResidual e) :
    e.1 ∈ P.smallObjects := by
  rcases Finset.mem_union.mp e.2 with hfinite | htiny
  · exact (he hfinite).elim
  · exact htiny

/-- A fixed core pair-multiplicity bound and endpoint-simplicity of the tiny
part add to a fixed bound on the joint residual. -/
theorem jointResidualGraph_pairMultiplicityAtMost
    {L : ℕ} (hmult : C.residualGraph.PairMultiplicityAtMost L) :
    C.jointResidualGraph.PairMultiplicityAtMost (L + 1) := by
  intro u v
  let H := C.jointResidualGraph
  let HF := C.residualGraph
  let HS := P.smallObjectGraph.asMultigraph
  let source := {e : H.E // e ∈ H.endpointPairCell u v}
  let leftTarget := {e : HF.E // e ∈ HF.endpointPairCell u v}
  let rightTarget := {e : HS.E // e ∈ HS.endpointPairCell u v}
  let f : source → leftTarget ⊕ rightTarget := fun e ↦
    if heF : C.isFiniteCoreResidual e.1 then
      let core := C.jointFiniteCoreEdge ⟨e.1, heF⟩
      let residual : HF.E := ⟨core,
        C.jointFiniteCoreEdge_mem_residual ⟨e.1, heF⟩⟩
      Sum.inl ⟨residual, by
        apply (HF.mem_endpointPairCell_iff u v residual).mpr
        have he := (H.mem_endpointPairCell_iff u v e.1).mp e.2
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v) at he
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v)
        exact he⟩
    else
      let small : HS.E := ⟨e.1.1,
        C.jointResidual_mem_small_of_not_finite e.1 heF⟩
      Sum.inr ⟨small, by
        apply (HS.mem_endpointPairCell_iff u v small).mpr
        have he := (H.mem_endpointPairCell_iff u v e.1).mp e.2
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v) at he
        change P.mixedObjectGraph.endpoints e.1.1 = s(u, v)
        exact he⟩
  have hf : Function.Injective f := by
    intro e d hed
    by_cases he : C.isFiniteCoreResidual e.1 <;>
      by_cases hd : C.isFiniteCoreResidual d.1
    · dsimp only [f] at hed
      rw [dif_pos he, dif_pos hd] at hed
      have h := Sum.inl.inj hed
      have hval : e.1.1 = d.1.1 :=
        congrArg (fun z : leftTarget ↦ z.1.1.1) h
      exact Subtype.ext (Subtype.ext hval)
    · have : False := by
        dsimp only [f] at hed
        rw [dif_pos he, dif_neg hd] at hed
        cases hed
      contradiction
    · have : False := by
        dsimp only [f] at hed
        rw [dif_neg he, dif_pos hd] at hed
        cases hed
      contradiction
    · dsimp only [f] at hed
      rw [dif_neg he, dif_neg hd] at hed
      have h := Sum.inr.inj hed
      have hval : e.1.1 = d.1.1 :=
        congrArg (fun z : rightTarget ↦ z.1.1) h
      exact Subtype.ext (Subtype.ext hval)
  have hcard : Fintype.card source ≤ Fintype.card (leftTarget ⊕ rightTarget) :=
    Fintype.card_le_of_injective f hf
  have hleft : Fintype.card leftTarget ≤ L := by
    simpa only [leftTarget, Fintype.card_coe, HF] using hmult u v
  have hright : Fintype.card rightTarget ≤ 1 := by
    simpa only [rightTarget, Fintype.card_coe, HS] using
      P.smallObjectGraph_pairMultiplicityAtMost u v
  have htarget : Fintype.card (leftTarget ⊕ rightTarget) ≤ L + 1 := by
    rw [Fintype.card_sum]
    exact Nat.add_le_add hleft hright
  have htotal := hcard.trans htarget
  simpa only [source, Fintype.card_coe, H] using htotal

end GeneralColoredPacketBase

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.WeightedMultigraph.GeneralColoredPacketBase.jointResidualGraph_pairMultiplicityAtMost
