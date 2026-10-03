import WeightedEdgeColoring.GeneralFiniteTinyHybridProposal
import WeightedEdgeColoring.EdgeLocalCharge

/-!
# Charge accounting for the general finite/tiny residual

The joint residual consists of a finite core residual and the endpoint-simple
tiny tail.  Its artificial charge is exactly the harmonic charge of the core
residual plus the tiny physical load divided by `1 - tau`.  These identities
do not use a bipartition.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u

/-- Sums are preserved when a finite subset of an edge restriction is
lifted to the ambient edge type. -/
theorem sum_liftRestrictionFinset_generalTiny
    (G : WeightedMultigraph.{u}) (R : Finset G.E)
    (S : Finset (G.edgeRestriction R).E) (f : G.E → ℝ) :
    (∑ e ∈ G.liftRestrictionFinset R S, f e) =
      ∑ e ∈ S, f e.1 := by
  classical
  unfold liftRestrictionFinset
  rw [Finset.sum_image]
  intro e _he d _hd hed
  exact Subtype.ext hed

namespace GeneralTinyThresholdPacketization

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
variable (P : G.GeneralTinyThresholdPacketization tau)

/-- Physical load in the endpoint-simple tiny remainder. -/
def smallObjectStarWeight (v : G.V) : ℝ :=
  ∑ o ∈ P.smallObjects,
    if P.mixedObjectGraph.Inc v o then P.mixedObjectGraph.weight o else 0

theorem smallObjectStarWeight_nonneg (v : G.V) :
    0 ≤ P.smallObjectStarWeight v := by
  unfold smallObjectStarWeight
  exact Finset.sum_nonneg fun o _ho ↦ by
    split
    · exact P.mixedObjectGraph.weight_nonneg o
    · exact le_rfl

/-- Tiny object load is no larger than the original physical star load. -/
theorem smallObjectStarWeight_le_original (v : G.V) :
    P.smallObjectStarWeight v ≤ G.starWeight v := by
  have hrestrict : P.smallObjectStarWeight v ≤
      P.mixedObjectGraph.starWeight v := by
    unfold smallObjectStarWeight
    rw [P.mixedObjectGraph.starWeight_eq_inc_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun o _ho _hne ↦ by
        split
        · exact P.mixedObjectGraph.weight_nonneg o
        · exact le_rfl)
  rw [P.mixedObjectGraph_starWeight] at hrestrict
  exact hrestrict

end GeneralTinyThresholdPacketization

namespace GeneralColoredPacketBase

variable {G : WeightedMultigraph.{u}} {tau : ℝ}
variable {P : G.GeneralTinyThresholdPacketization tau}
variable {K : ℕ}
variable (C : P.coreObjectGraph.GeneralColoredPacketBase K)

/-- The embedded finite residual lies in the core and is disjoint from the
tiny remainder. -/
theorem residualCoreObjects_disjoint_smallObjects :
    Disjoint C.residualCoreObjects P.smallObjects := by
  rw [Finset.disjoint_left]
  intro o hoR hoS
  have hoCore := P.mixedObjectGraph.liftRestrictionFinset_subset
    P.coreObjects C.residualEdges hoR
  exact (Finset.mem_sdiff.mp hoCore).2 hoS

/-- Harmonic charge is unchanged when the finite residual is lifted from
the core restriction to the ambient mixed-object graph. -/
theorem residualCoreObjects_harmonicCharge (v : G.V) :
    (∑ o ∈ C.residualCoreObjects,
        if P.mixedObjectGraph.Inc v o then
          harmonicCharge (P.mixedObjectGraph.weight o) else 0) =
      C.residualGraph.starCharge harmonicCharge v := by
  rw [P.coreObjectGraph.edgeRestriction_starCharge_as_edgeSum
      C.residualEdges harmonicCharge v]
  unfold residualCoreObjects
  calc
    _ = ∑ e ∈ C.residualEdges,
        (if P.mixedObjectGraph.Inc v e.1 then
          harmonicCharge (P.mixedObjectGraph.weight e.1) else 0) :=
      P.mixedObjectGraph.sum_liftRestrictionFinset_generalTiny
        P.coreObjects C.residualEdges
        (fun o ↦ if P.mixedObjectGraph.Inc v o then
          harmonicCharge (P.mixedObjectGraph.weight o) else 0)
    _ = _ := rfl

/-- Write the joint charge as an ambient sum over its two parts. -/
theorem jointResidualStarCharge_eq_ambient (v : G.V) :
    C.jointResidualStarCharge v =
      ∑ o ∈ C.jointResidualObjects,
        if P.mixedObjectGraph.Inc v o then
          if o ∈ C.residualCoreObjects then
            harmonicCharge (P.mixedObjectGraph.weight o)
          else P.mixedObjectGraph.weight o / (1 - tau)
        else 0 := by
  classical
  unfold jointResidualStarCharge
  calc
    (∑ e : C.jointResidualGraph.StarEdge v,
        C.jointResidualCharge e.1) =
        ∑ e : C.jointResidualGraph.E,
          if C.jointResidualGraph.Inc v e then
            C.jointResidualCharge e else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (p := fun e : C.jointResidualGraph.E ↦
          C.jointResidualGraph.Inc v e)
        ((Finset.univ : Finset C.jointResidualGraph.E).filter
          (C.jointResidualGraph.Inc v)) (by
            intro e
            rw [Finset.mem_filter]
            simp only [Finset.mem_univ, true_and])
        C.jointResidualCharge).symm
    _ = _ := by
      symm
      exact Finset.sum_subtype
        (p := fun o : P.Object ↦ o ∈ C.jointResidualObjects)
        (F := inferInstance) C.jointResidualObjects (by intro o; rfl)
        (fun o ↦ if P.mixedObjectGraph.Inc v o then
          if o ∈ C.residualCoreObjects then
            harmonicCharge (P.mixedObjectGraph.weight o)
          else P.mixedObjectGraph.weight o / (1 - tau)
          else 0)

/-- Exact split of the artificial joint charge. -/
theorem jointResidualStarCharge_eq_residual_add_small (v : G.V) :
    C.jointResidualStarCharge v =
      C.residualGraph.starCharge harmonicCharge v +
        P.smallObjectStarWeight v / (1 - tau) := by
  classical
  rw [C.jointResidualStarCharge_eq_ambient]
  unfold jointResidualObjects
  rw [Finset.sum_union C.residualCoreObjects_disjoint_smallObjects]
  have hfinite :
      (∑ o ∈ C.residualCoreObjects,
          if P.mixedObjectGraph.Inc v o then
            (if o ∈ C.residualCoreObjects then
              harmonicCharge (P.mixedObjectGraph.weight o)
            else P.mixedObjectGraph.weight o / (1 - tau))
          else 0) =
        C.residualGraph.starCharge harmonicCharge v := by
    calc
      _ = ∑ o ∈ C.residualCoreObjects,
          if P.mixedObjectGraph.Inc v o then
            harmonicCharge (P.mixedObjectGraph.weight o) else 0 := by
        apply Finset.sum_congr rfl
        intro o ho
        simp [ho]
      _ = _ := C.residualCoreObjects_harmonicCharge v
  have htiny :
      (∑ o ∈ P.smallObjects,
          if P.mixedObjectGraph.Inc v o then
            (if o ∈ C.residualCoreObjects then
              harmonicCharge (P.mixedObjectGraph.weight o)
            else P.mixedObjectGraph.weight o / (1 - tau))
          else 0) =
        P.smallObjectStarWeight v / (1 - tau) := by
    calc
      _ = ∑ o ∈ P.smallObjects,
          if P.mixedObjectGraph.Inc v o then
            P.mixedObjectGraph.weight o / (1 - tau) else 0 := by
        apply Finset.sum_congr rfl
        intro o ho
        have hnot : o ∉ C.residualCoreObjects := fun hmem ↦
          Finset.disjoint_left.mp C.residualCoreObjects_disjoint_smallObjects
            hmem ho
        simp [hnot]
      _ = P.smallObjectStarWeight v / (1 - tau) := by
        unfold GeneralTinyThresholdPacketization.smallObjectStarWeight
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro o _ho
        by_cases hinc : P.mixedObjectGraph.Inc v o <;> simp [hinc]
  rw [hfinite, htiny]

theorem jointResidualStarCharge_nonneg
    (htau1 : tau < 1) (v : G.V) :
    0 ≤ C.jointResidualStarCharge v := by
  unfold jointResidualStarCharge
  exact Finset.sum_nonneg fun e _he ↦ C.jointResidualCharge_nonneg htau1 e.1

/-- If the core residual harmonic charge and inflated tiny load fit under a
missing-color reserve, then the complete joint charge fits under it exactly. -/
theorem jointResidualStarCharge_add_gap_le_missingColors
    (gap : ℝ) (v : G.V)
    (hfit : C.residualGraph.starCharge harmonicCharge v +
        P.smallObjectStarWeight v / (1 - tau) + gap ≤
      ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        C.ambientBaseColor v).card : ℝ)) :
    C.jointResidualStarCharge v + gap ≤
      ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        C.ambientBaseColor v).card : ℝ) := by
  rw [C.jointResidualStarCharge_eq_residual_add_small]
  exact hfit

end GeneralColoredPacketBase

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.WeightedMultigraph.GeneralColoredPacketBase.jointResidualStarCharge_eq_residual_add_small
