import WeightedEdgeColoring.BPLocalCharge
import WeightedEdgeColoring.BPEdgeRestriction
import WeightedEdgeColoring.GeneralPacketization

/-!
# Edge-dependent local charges

`WeightedMultigraph.starCharge` is designed for a charge which is a function
of the edge weight.  The finite-plus-tiny construction needs a charge which
also remembers whether an edge belongs to the finite residual or to the tiny
tail.  This file supplies that edge-dependent version and the restriction
identities used in its accounting.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Total of an edge-dependent charge at one vertex. -/
def edgeStarCharge (charge : G.E → ℝ) (v : G.V) : ℝ :=
  ∑ e : G.StarEdge v, charge e.1

/-- Rewrite an edge-dependent star sum as a sum over all indexed edges. -/
theorem edgeStarCharge_eq_inc_sum (charge : G.E → ℝ) (v : G.V) :
    G.edgeStarCharge charge v =
      ∑ e : G.E, if G.Inc v e then charge e else 0 := by
  classical
  unfold edgeStarCharge
  calc
    (∑ e : G.StarEdge v, charge e.1) =
        ∑ e ∈ (Finset.univ : Finset G.E).filter (G.Inc v), charge e := by
      symm
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter (G.Inc v)) (by simp) charge
    _ = _ := by rw [Finset.sum_filter]

/-- The old weight-only charge is the edge-dependent charge obtained by
composing with the weight function. -/
theorem starCharge_eq_edgeStarCharge (charge : ℝ → ℝ) (v : G.V) :
    G.starCharge charge v =
      G.edgeStarCharge (fun e ↦ charge (G.weight e)) v := by
  rfl

/-- Edge-dependent charge on an edge restriction, written in the ambient
edge type. -/
theorem edgeRestriction_edgeStarCharge
    (R : Finset G.E) (charge : G.E → ℝ) (v : G.V) :
    (G.edgeRestriction R).edgeStarCharge (fun e ↦ charge e.1) v =
      ∑ e ∈ R, if G.Inc v e then charge e else 0 := by
  classical
  rw [(G.edgeRestriction R).edgeStarCharge_eq_inc_sum]
  symm
  exact Finset.sum_subtype (p := fun e : G.E ↦ e ∈ R) R (by simp)
    (fun e ↦ if G.Inc v e then charge e else 0)

/-- Weight-dependent charge on an edge restriction, written in the ambient
edge type. -/
theorem edgeRestriction_starCharge_as_edgeSum
    (R : Finset G.E) (charge : ℝ → ℝ) (v : G.V) :
    (G.edgeRestriction R).starCharge charge v =
      ∑ e ∈ R, if G.Inc v e then charge (G.weight e) else 0 := by
  rw [(G.edgeRestriction R).starCharge_eq_edgeStarCharge]
  change (G.edgeRestriction R).edgeStarCharge
      (fun e ↦ charge (G.weight e.1)) v = _
  exact G.edgeRestriction_edgeStarCharge R
    (fun e ↦ charge (G.weight e)) v

/-- Restricting a nonnegative edge charge cannot increase its star total. -/
theorem edgeRestriction_edgeStarCharge_le
    (R : Finset G.E) (charge : G.E → ℝ)
    (hcharge : ∀ e, 0 ≤ charge e) (v : G.V) :
    (G.edgeRestriction R).edgeStarCharge (fun e ↦ charge e.1) v ≤
      G.edgeStarCharge charge v := by
  rw [G.edgeRestriction_edgeStarCharge R charge v,
    G.edgeStarCharge_eq_inc_sum charge v]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun e _he _hne ↦ by
      split
      · exact hcharge e
      · exact le_rfl)

/-- A set and its complement partition every edge-dependent star charge. -/
theorem edgeRestriction_edgeStarCharge_complement_add
    (R : Finset G.E) (charge : G.E → ℝ) (v : G.V) :
    (G.edgeRestriction (Finset.univ \ R)).edgeStarCharge
          (fun e ↦ charge e.1) v +
        (G.edgeRestriction R).edgeStarCharge
          (fun e ↦ charge e.1) v =
      G.edgeStarCharge charge v := by
  classical
  rw [G.edgeRestriction_edgeStarCharge,
    G.edgeRestriction_edgeStarCharge,
    G.edgeStarCharge_eq_inc_sum]
  let f : G.E → ℝ := fun e ↦ if G.Inc v e then charge e else 0
  change (∑ e ∈ Finset.univ \ R, f e) + (∑ e ∈ R, f e) = ∑ e, f e
  rw [← Finset.sum_union Finset.sdiff_disjoint,
    Finset.sdiff_union_of_subset (Finset.subset_univ R)]

/-- Disjoint restrictions add exactly. -/
theorem edgeRestriction_edgeStarCharge_union
    (R S : Finset G.E) (hdisj : Disjoint R S)
    (charge : G.E → ℝ) (v : G.V) :
    (G.edgeRestriction (R ∪ S)).edgeStarCharge
          (fun e ↦ charge e.1) v =
      (G.edgeRestriction R).edgeStarCharge
          (fun e ↦ charge e.1) v +
        (G.edgeRestriction S).edgeStarCharge
          (fun e ↦ charge e.1) v := by
  classical
  rw [G.edgeRestriction_edgeStarCharge,
    G.edgeRestriction_edgeStarCharge,
    G.edgeRestriction_edgeStarCharge,
    Finset.sum_union hdisj]

/-- A missing-color set is a subset of the palette. -/
theorem card_missingColorsAt_le
    {q : ℕ} (F : Finset G.E) (color : G.E → Fin q) (v : G.V) :
    (G.missingColorsAt F color v).card ≤ q := by
  simpa using Finset.card_le_card
    (show G.missingColorsAt F color v ⊆ (Finset.univ : Finset (Fin q)) from
      Finset.subset_univ _)

namespace Packetization

variable {G : WeightedMultigraph.{u}} (P : G.Packetization)

/-- Grouping a partition of all physical edges into packets preserves the
total incident weight at every vertex. -/
theorem groupedGraph_starWeight (v : G.V) :
    P.groupedGraph.starWeight v = G.starWeight v := by
  have h := P.restrictedWeight_originalEdgesOfPackets
    (Finset.univ : Finset P.Packet) v
  simpa [Packetization.originalEdgesOfPackets,
    WeightedMultigraph.starWeight_eq_inc_sum] using h.symm

end Packetization

end

end WeightedMultigraph
end WeightedEdgeColoring
