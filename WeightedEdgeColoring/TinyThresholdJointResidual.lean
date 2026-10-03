import WeightedEdgeColoring.TinyThresholdMixedObjects
import WeightedEdgeColoring.FiniteHarmonicClassEncoding
import WeightedEdgeColoring.SamePaletteResidualAdapter

/-!
# Embedding a finite harmonic core and the tiny tail in one ambient graph

The finite harmonic certificate is built on the core edge restriction of the
mixed-object graph.  Weighted-moment mixing and coordinated rounding must see
its residual together with the endpoint-simple tiny objects.  These
definitions put both pieces back in the ambient mixed-object edge type and
record the exact partition and base-color transfer.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

namespace FiniteHarmonicPacketColoringCertificate

variable {G : WeightedMultigraph.{u}} {b : G.Bipartition} {tau : ℝ}
variable {P : G.TinyThresholdPacketization b tau}
variable {T K : ℕ}
variable {classOf : P.coreObjectGraph.E → Fin T}
variable (C : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
  P.coreBipartition classOf K)

/-- Full finite-class core edges, embedded in the mixed-object graph. -/
def fullCoreObjects : Finset P.Object :=
  P.mixedObjectGraph.liftRestrictionFinset P.coreObjects C.fullEdges

/-- Finite-class residual core edges, embedded in the mixed-object graph. -/
def residualCoreObjects : Finset P.Object :=
  P.mixedObjectGraph.liftRestrictionFinset P.coreObjects C.residualEdges

/-- The residual on which rounding must be coordinated: finite-class core
residual plus the endpoint-simple tiny remainder. -/
def jointResidualObjects : Finset P.Object :=
  C.residualCoreObjects ∪ P.smallObjects

/-- The finite certificate's base coloring lifted to all mixed objects. -/
def ambientBaseColor (hK : 0 < K) : P.Object → Fin K :=
  P.mixedObjectGraph.liftRestrictedColor hK P.coreObjects (C.baseColor hK)

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

theorem ambientBaseColor_feasibleOn (hK : 0 < K) :
    P.mixedObjectGraph.IsFeasibleOn C.fullCoreObjects
      (ambientBaseColor C hK) := by
  exact P.mixedObjectGraph.feasibleOn_liftRestrictionFinset hK
    P.coreObjects C.fullEdges (C.baseColor hK) (C.baseColor_feasibleOn hK)

end FiniteHarmonicPacketColoringCertificate

end

end WeightedMultigraph
end WeightedEdgeColoring
