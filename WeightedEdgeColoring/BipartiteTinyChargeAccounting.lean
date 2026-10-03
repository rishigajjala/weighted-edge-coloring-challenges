import WeightedEdgeColoring.EdgeLocalCharge
import WeightedEdgeColoring.FiniteHarmonicTinyHybridMixing
import WeightedEdgeColoring.BPGeneralPacketSlack

/-!
# Charge accounting for the finite-plus-tiny bipartite construction

The packet palette is chosen from the harmonic charge of the complete mixed
object graph.  Its unused colors therefore pay for both the finite-class
residual and the tiny remainder.  The tiny artificial charge is
`w / (1 - tau)`; compared with harmonic charge this costs at most
`tau / (1 - tau)` times the tiny physical load.  This file records those
identities without any asymptotic choices.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable {G : WeightedMultigraph.{u}}

/-- A positive additive gap below a quantity of size at most `C*n` becomes
a uniform multiplicative gap after division. -/
theorem div_le_one_sub_of_add_gap_le
    {J M alpha C n : ℝ}
    (hJ : 0 ≤ J) (halpha : 0 < alpha) (hC : 0 < C) (hn : 0 < n)
    (hgap : J + alpha * n ≤ M) (hupper : M ≤ C * n) :
    J / M ≤ 1 - alpha / C := by
  have hM : 0 < M := by
    have : 0 < J + alpha * n := by positivity
    exact this.trans_le hgap
  apply (div_le_iff₀ hM).2
  have hscaled : alpha * M / C ≤ alpha * n := by
    apply (div_le_iff₀ hC).2
    have hmul := mul_le_mul_of_nonneg_left hupper halpha.le
    nlinarith
  calc
    J ≤ M - alpha * n := by linarith
    _ ≤ M - alpha * M / C := by linarith
    _ = (1 - alpha / C) * M := by ring

/-- Convenient row-budget form of the preceding ratio estimate. -/
theorem div_add_errors_le_one_of_add_gap_le
    {J M alpha C n eps diffuse : ℝ}
    (hJ : 0 ≤ J) (halpha : 0 < alpha) (hC : 0 < C) (hn : 0 < n)
    (hgap : J + alpha * n ≤ M) (hupper : M ≤ C * n)
    (heps : eps ≤ alpha / (4 * C))
    (hdiffuse : diffuse ≤ alpha / (4 * C)) :
    J / M + eps + diffuse ≤ 1 := by
  have hratio := div_le_one_sub_of_add_gap_le
    hJ halpha hC hn hgap hupper
  have hpos : 0 < 4 * C := mul_pos (by norm_num) hC
  have hquarter : alpha / (4 * C) + alpha / (4 * C) ≤ alpha / C := by
    field_simp [hC.ne', hpos.ne']
    nlinarith [halpha.le]
  linarith

/-- Sums are preserved when a finite set of an edge restriction is lifted
to the ambient edge type. -/
theorem sum_liftRestrictionFinset
    (R : Finset G.E) (S : Finset (G.edgeRestriction R).E)
    (f : G.E → ℝ) :
    (∑ e ∈ G.liftRestrictionFinset R S, f e) =
      ∑ e ∈ S, f e.1 := by
  classical
  unfold liftRestrictionFinset
  rw [Finset.sum_image]
  intro e _he d _hd hed
  exact Subtype.ext hed

namespace TinyThresholdPacketization

variable {b : G.Bipartition} {tau : ℝ}
variable (P : G.TinyThresholdPacketization b tau)

/-- Harmonic charge in the endpoint-simple tiny remainder. -/
def smallObjectStarCharge (v : G.V) : ℝ :=
  ∑ o ∈ P.smallObjects,
    if P.mixedObjectGraph.Inc v o then
      harmonicCharge (P.mixedObjectGraph.weight o) else 0

/-- Physical load in the endpoint-simple tiny remainder. -/
def smallObjectStarWeight (v : G.V) : ℝ :=
  ∑ o ∈ P.smallObjects,
    if P.mixedObjectGraph.Inc v o then
      P.mixedObjectGraph.weight o else 0

/-- The core and tiny remainder partition the harmonic charge of the mixed
object graph. -/
theorem core_add_small_starCharge (v : G.V) :
    P.coreObjectGraph.starCharge harmonicCharge v +
        P.smallObjectStarCharge v =
      P.mixedObjectGraph.starCharge harmonicCharge v := by
  rw [P.mixedObjectGraph.edgeRestriction_starCharge_as_edgeSum
      P.coreObjects harmonicCharge v]
  rw [P.mixedObjectGraph.starCharge_eq_edgeStarCharge,
    P.mixedObjectGraph.edgeStarCharge_eq_inc_sum]
  unfold coreObjects smallObjectStarCharge
  let f : P.Object → ℝ := fun o ↦
    if P.mixedObjectGraph.Inc v o then
      harmonicCharge (P.mixedObjectGraph.weight o) else 0
  change (∑ o ∈ Finset.univ \ P.smallObjects, f o) +
      (∑ o ∈ P.smallObjects, f o) = ∑ o : P.Object, f o
  calc
    _ = ∑ o ∈ (Finset.univ \ P.smallObjects) ∪ P.smallObjects, f o :=
      (Finset.sum_union Finset.sdiff_disjoint).symm
    _ = ∑ o ∈ (Finset.univ : Finset P.Object), f o := by
      rw [Finset.sdiff_union_of_subset (Finset.subset_univ P.smallObjects)]
    _ = _ := by simp

/-- Tiny physical load is bounded by tiny harmonic charge. -/
theorem smallObjectStarWeight_le_charge (v : G.V) :
    P.smallObjectStarWeight v ≤ P.smallObjectStarCharge v := by
  unfold smallObjectStarWeight smallObjectStarCharge
  apply Finset.sum_le_sum
  intro o _ho
  by_cases hinc : P.mixedObjectGraph.Inc v o
  · simp only [hinc, if_true]
    exact TinyThresholdPacketization.weight_le_harmonicCharge
      (G := P.mixedObjectGraph) o
  · simp [hinc]

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
  rw [P.mixedPacketization.groupedGraph_starWeight v] at hrestrict
  exact hrestrict

end TinyThresholdPacketization

namespace FiniteHarmonicPacketColoringCertificate

variable {b : G.Bipartition} {tau : ℝ}
variable {P : G.TinyThresholdPacketization b tau}
variable {T K : ℕ}
variable {classOf : P.coreObjectGraph.E → Fin T}
variable (C : P.coreObjectGraph.FiniteHarmonicPacketColoringCertificate
  P.coreBipartition classOf K)

/-- The embedded finite residual lies in the core and is therefore disjoint
from the tiny remainder. -/
theorem residualCoreObjects_disjoint_smallObjects :
    Disjoint C.residualCoreObjects P.smallObjects := by
  rw [Finset.disjoint_left]
  intro o hoR hoS
  have hoCore := P.mixedObjectGraph.liftRestrictionFinset_subset
    P.coreObjects C.residualEdges hoR
  exact (Finset.mem_sdiff.mp hoCore).2 hoS

/-- Harmonic charge on the embedded finite residual is unchanged by lifting
it from the core restriction to the mixed-object graph. -/
theorem residualCoreObjects_harmonicCharge (v : G.V) :
    (∑ o ∈ C.residualCoreObjects,
        if P.mixedObjectGraph.Inc v o then
          harmonicCharge (P.mixedObjectGraph.weight o) else 0) =
      C.residualGraph.starCharge harmonicCharge v := by
  rw [C.residualGraph_starCharge_eq]
  unfold residualCoreObjects
  calc
    _ = ∑ e ∈ C.residualEdges,
        (if P.mixedObjectGraph.Inc v e.1 then
          harmonicCharge (P.mixedObjectGraph.weight e.1) else 0) :=
      P.mixedObjectGraph.sum_liftRestrictionFinset
        P.coreObjects C.residualEdges
        (fun o ↦ if P.mixedObjectGraph.Inc v o then
          harmonicCharge (P.mixedObjectGraph.weight o) else 0)
    _ = _ := rfl

/-- Write the edge-dependent joint-residual charge as an ambient sum over
the finite residual and the tiny remainder. -/
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
      have h := Finset.sum_subtype
        (p := fun o : P.Object ↦ o ∈ C.jointResidualObjects)
        (F := inferInstance) C.jointResidualObjects (by intro o; rfl)
        (fun o ↦ if P.mixedObjectGraph.Inc v o then
          if o ∈ C.residualCoreObjects then
            harmonicCharge (P.mixedObjectGraph.weight o)
          else P.mixedObjectGraph.weight o / (1 - tau)
          else 0)
      exact h

/-- Exact split of the artificial joint charge into finite harmonic charge
and the inflated tiny physical load. -/
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
        unfold TinyThresholdPacketization.smallObjectStarWeight
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro o _ho
        by_cases hinc : P.mixedObjectGraph.Inc v o <;> simp [hinc]
  rw [hfinite, htiny]

/-- The joint artificial charge exceeds the mixed harmonic charge only by
the displayed tiny inflation. -/
theorem jointResidualStarCharge_le_mixed_add_tinyInflation
    (hcharge : ∀ e : P.coreObjectGraph.E,
      harmonicCharge (P.coreObjectGraph.weight e) =
        (1 : ℝ) / finiteClassSize (classOf e))
    (n : ℝ) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hsmall : P.smallObjectStarWeight v ≤ n) :
    C.jointResidualStarCharge v ≤
      P.mixedObjectGraph.starCharge harmonicCharge v +
        tau / (1 - tau) * n := by
  let d : ℕ := C.decomposition.packetDegreeAt v
  let R : ℝ := C.residualGraph.starCharge harmonicCharge v
  let S : ℝ := P.smallObjectStarCharge v
  let W : ℝ := P.smallObjectStarWeight v
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hWS : W ≤ S := P.smallObjectStarWeight_le_charge v
  have haccount : (d : ℝ) + R =
      P.coreObjectGraph.starCharge harmonicCharge v := by
    unfold d R
    rw [C.residualGraph_starCharge_eq,
      P.coreObjectGraph.starCharge_eq_edgeStarCharge,
      P.coreObjectGraph.edgeStarCharge_eq_inc_sum]
    exact C.packetDegree_add_residualHarmonicChargeAt hcharge v
  have hden : 0 < 1 - tau := sub_pos.mpr htau1
  have hcoef0 : 0 ≤ tau / (1 - tau) :=
    div_nonneg htau0 hden.le
  have hfrac : W / (1 - tau) = W + tau / (1 - tau) * W := by
    field_simp [hden.ne']
    ring
  have hinflate : W / (1 - tau) ≤ S + tau / (1 - tau) * n := by
    rw [hfrac]
    exact add_le_add hWS (mul_le_mul_of_nonneg_left hsmall hcoef0)
  rw [C.jointResidualStarCharge_eq_residual_add_small]
  have hmixed := P.core_add_small_starCharge v
  dsimp [R, S, W] at haccount hinflate ⊢
  linarith

/-- If the packet palette covers the mixed harmonic charge, the tiny
inflation, and a positive gap, then that gap remains after paying the whole
joint residual artificial charge. -/
theorem jointResidualStarCharge_add_gap_le_missingColors
    (hK : 0 < K)
    (hcharge : ∀ e : P.coreObjectGraph.E,
      harmonicCharge (P.coreObjectGraph.weight e) =
        (1 : ℝ) / finiteClassSize (classOf e))
    (Q gap n : ℝ) (htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hgap : 0 ≤ gap) (hn : 0 ≤ n)
    (hmixed : P.mixedObjectGraph.starCharge harmonicCharge v ≤ Q)
    (hsmall : P.smallObjectStarWeight v ≤ n)
    (hpalette :
      Q + tau / (1 - tau) * n + gap ≤ (K : ℝ)) :
    C.jointResidualStarCharge v + gap ≤
      ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v).card : ℝ) := by
  let d : ℕ := C.decomposition.packetDegreeAt v
  let R : ℝ := C.residualGraph.starCharge harmonicCharge v
  let S : ℝ := P.smallObjectStarCharge v
  let W : ℝ := P.smallObjectStarWeight v
  let M : ℝ := P.mixedObjectGraph.starCharge harmonicCharge v
  have hR0 : 0 ≤ R := by
    unfold R starCharge
    exact Finset.sum_nonneg fun e _he ↦ harmonicCharge_nonneg _
  have hW0 : 0 ≤ W := by
    unfold W TinyThresholdPacketization.smallObjectStarWeight
    exact Finset.sum_nonneg fun o _ho ↦ by
      split
      · exact P.mixedObjectGraph.weight_nonneg o
      · exact le_rfl
  have hS0 : 0 ≤ S := by
    unfold S TinyThresholdPacketization.smallObjectStarCharge
    exact Finset.sum_nonneg fun o _ho ↦ by
      split
      · exact harmonicCharge_nonneg _
      · exact le_rfl
  have hWS : W ≤ S := P.smallObjectStarWeight_le_charge v
  have haccount : (d : ℝ) + R =
      P.coreObjectGraph.starCharge harmonicCharge v := by
    unfold d R
    rw [C.residualGraph_starCharge_eq,
      P.coreObjectGraph.starCharge_eq_edgeStarCharge,
      P.coreObjectGraph.edgeStarCharge_eq_inc_sum]
    exact C.packetDegree_add_residualHarmonicChargeAt hcharge v
  have hmixedEq :
      P.coreObjectGraph.starCharge harmonicCharge v + S = M := by
    simpa [S, M] using P.core_add_small_starCharge v
  have hden : 0 < 1 - tau := sub_pos.mpr htau1
  have hcoef0 : 0 ≤ tau / (1 - tau) :=
    div_nonneg htau0 hden.le
  have hfrac : W / (1 - tau) = W + tau / (1 - tau) * W := by
    field_simp [hden.ne']
    ring
  have hinflate : W / (1 - tau) ≤ S + tau / (1 - tau) * n := by
    rw [hfrac]
    exact add_le_add hWS (mul_le_mul_of_nonneg_left hsmall hcoef0)
  have hjoint : C.jointResidualStarCharge v ≤
      R + S + tau / (1 - tau) * n := by
    rw [C.jointResidualStarCharge_eq_residual_add_small]
    dsimp [R, W]
    linarith
  have hQK : Q ≤ (K : ℝ) := by
    have hextra : 0 ≤ tau / (1 - tau) * n := mul_nonneg hcoef0 hn
    linarith
  have hdQ : (d : ℝ) ≤ Q := by
    have hcoreM : P.coreObjectGraph.starCharge harmonicCharge v ≤ M := by
      linarith [hmixedEq, hS0]
    have hdcore : (d : ℝ) ≤
        P.coreObjectGraph.starCharge harmonicCharge v := by
      linarith [haccount, hR0]
    exact hdcore.trans (hcoreM.trans hmixed)
  have hdKreal : (d : ℝ) ≤ (K : ℝ) := hdQ.trans hQK
  have hdK : d ≤ K := by exact_mod_cast hdKreal
  have hcard :
      ((P.mixedObjectGraph.missingColorsAt C.fullCoreObjects
        (C.ambientBaseColor hK) v).card : ℝ) =
        (K : ℝ) - (d : ℝ) := by
    rw [C.ambient_missingColorsAt_eq_core hK v,
      C.card_missingColorsAt_baseColor hK v, Nat.cast_sub hdK]
  rw [hcard]
  have htotal : (d : ℝ) + C.jointResidualStarCharge v + gap ≤
      Q + tau / (1 - tau) * n + gap := by
    calc
      (d : ℝ) + C.jointResidualStarCharge v + gap ≤
          (d : ℝ) + (R + S + tau / (1 - tau) * n) + gap := by
        gcongr
      _ = ((d : ℝ) + R + S) + tau / (1 - tau) * n + gap := by ring
      _ = M + tau / (1 - tau) * n + gap := by
        rw [haccount, hmixedEq]
      _ ≤ Q + tau / (1 - tau) * n + gap := by gcongr
  linarith

end FiniteHarmonicPacketColoringCertificate

end

end WeightedMultigraph
end WeightedEdgeColoring
