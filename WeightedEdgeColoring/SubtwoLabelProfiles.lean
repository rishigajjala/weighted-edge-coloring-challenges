import WeightedEdgeColoring.SubtwoBoundaryLabelChoice
import WeightedEdgeColoring.MultigraphProfileRepresentation

/-!
# Endpoint labels carried through local profile laws

The profile construction retains an exact marginal identity.  Therefore a
positive-probability local outcome contains only edges with positive input
proposal.  A proposal supported on one endpoint label per block and color
automatically forces every such outcome to have that label.  This avoids a
separate downward-closed-family generalization for this support property.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedEdgeColoring.WeightedMultigraph.{u})

/-- Positive-probability outcomes cannot contain a zero-marginal edge. -/
theorem positive_probability_outcome_edge_has_positive_marginal
    {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (k : Fin L.m) (hk : 0 < L.probability k)
    (e : G.StarEdge v) (he : e ∈ L.outcome k) : 0 < x e := by
  have hsingle : L.probability k ≤
      ∑ j : Fin L.m, if e ∈ L.outcome j then L.probability j else 0 := by
    have hnonneg : ∀ j : Fin L.m,
        0 ≤ if e ∈ L.outcome j then L.probability j else 0 := by
      intro j
      split_ifs
      · exact L.probability_nonneg j
      · exact le_rfl
    have h := Finset.single_le_sum
      (fun j _ => hnonneg j) (Finset.mem_univ k)
    simpa [he] using h
  rw [L.original_marginal e] at hsingle
  exact hk.trans_le hsingle

/-- A support predicate on the input proposal is inherited by every edge
of every positive-probability profile-law outcome. -/
theorem positive_probability_outcome_respects_support
    {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} (L : G.BoundedProfileLaw x s β q r)
    (Allowed : G.StarEdge v → Prop)
    (hsupport : ∀ e, 0 < x e → Allowed e)
    (k : Fin L.m) (hk : 0 < L.probability k) :
    ∀ e ∈ L.outcome k, Allowed e := by
  intro e he
  exact hsupport e (G.positive_probability_outcome_edge_has_positive_marginal
    L k hk e he)

/-- In particular, a bounded profile realization made from a
label-compatible proposal has only that endpoint label in every positive
outcome.  This is the exact support fact used by a label-aware local list. -/
theorem BoundedProfileRealization.positive_outcome_single_label
    {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    {Label : Type*} (edgeLabel : G.StarEdge v → Label) (chosen : Label)
    (hsupport : ∀ e, 0 < x e → edgeLabel e = chosen)
    (k : Fin R.law.m) (hk : 0 < R.law.probability k) :
    ∀ e ∈ R.law.outcome k, edgeLabel e = chosen := by
  exact G.positive_probability_outcome_respects_support
    R.law (fun e => edgeLabel e = chosen) hsupport k hk

/-- Every positive large-slot transport entry comes from positive input
marginal.  Thus the transport cannot assign a different endpoint label. -/
theorem BoundedProfileRealization.positive_largeAssign_respects_support
    {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (hs : 0 ≤ s)
    (Allowed : G.StarEdge v → Prop)
    (hsupport : ∀ e, 0 < x e → Allowed e)
    (e : G.StarEdge v) (j : G.ExplicitLargeSlot R.law hβ hr)
    (hpos : 0 < R.largeAssign e j) : Allowed e := by
  have hsingle : R.largeAssign e j ≤ ∑ k, R.largeAssign e k :=
    Finset.single_le_sum
      (fun k _ => R.largeAssign_nonneg e k) (Finset.mem_univ j)
  rw [R.largeAssign_marginal e] at hsingle
  have hprod : 0 < s * x e := by
    by_cases he : β ≤ G.weight e.1
    · exact hpos.trans_le (by simpa [he] using hsingle)
    · have hzero : R.largeAssign e j ≤ 0 := by simpa [he] using hsingle
      exact False.elim ((not_lt_of_ge hzero) hpos)
  have hx : 0 < x e := by
    by_contra hnot
    have hxle : x e ≤ 0 := le_of_not_gt hnot
    have hnonpos : s * x e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hxle
    exact (not_lt_of_ge hnonpos) hprod
  exact hsupport e hx

/-- The rounded-reservoir transport also preserves positive input support.
This covers tiny objects, including their repair profiles. -/
theorem BoundedProfileRealization.positive_tinyAssign_respects_support
    {v : G.V} {x : G.StarEdge v → ℝ}
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (R : G.BoundedProfileRealization x s β q r hβ hr)
    (hs : 0 ≤ s)
    (Allowed : G.StarEdge v → Prop)
    (hsupport : ∀ e, 0 < x e → Allowed e)
    (e : G.StarEdge v) (P : G.RoundedProfileIndex R.law hβ hr)
    (hpos : 0 < R.tinyAssign e P) : Allowed e := by
  have hsingle : R.tinyAssign e P ≤ ∑ Q, R.tinyAssign e Q :=
    Finset.single_le_sum
      (fun Q _ => R.tinyAssign_nonneg e Q) (Finset.mem_univ P)
  rw [R.tinyAssign_marginal e] at hsingle
  have hprod : 0 < s * x e := by
    by_cases he : G.weight e.1 < β
    · exact hpos.trans_le (by simpa [tinyOccurrenceDemand, he] using hsingle)
    · have hzero : R.tinyAssign e P ≤ 0 := by
        simpa [tinyOccurrenceDemand, he] using hsingle
      exact False.elim ((not_lt_of_ge hzero) hpos)
  have hx : 0 < x e := by
    by_contra hnot
    have hxle : x e ≤ 0 := le_of_not_gt hnot
    have hnonpos : s * x e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs hxle
    exact (not_lt_of_ge hnonpos) hprod
  exact hsupport e hx

end WeightedEdgeColoring.WeightedMultigraph
