import WeightedEdgeColoring.SubtwoLocalLabelledProfileAtoms
import WeightedEdgeColoring.SubtwoLabelMixtureAtom

/-!
# Concrete one-label graph atoms

At one graph star and one color, a state first chooses an endpoint label
with its original mass, then a rounded profile of that label's conditional
realization.  The inactive `none` atom absorbs empty-set mass.  Large and
tiny assignment masses carry the *same* outer label factor.  Therefore
their total edge marginals return to the original (unconditioned) proposal,
and local capacities are bounded by the actual mixed-state probability.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {v : G.V} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (edgeLabel : G.StarEdge v → Label)
variable (x : G.StarEdge v → ℝ)
variable (q : Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ label : Label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal edgeLabel x q label)
    s β qstep r hβ hr)

abbrev MixedLabelGraphAtom :=
  Subtwo.LabelMixtureAtom
    (fun label ↦ G.LocalExtendedProfileState (R label))

def mixedLabelGraphAtomProbability
    (a : G.MixedLabelGraphAtom edgeLabel x q R) : ℝ :=
  Subtwo.labelMixtureAtomProbability
    (fun label ↦ G.LocalExtendedProfileState (R label))
    (subsetLabelMass edgeLabel q)
    (fun label z ↦ G.localExtendedProfileProbability (R label) z) a

def mixedLabelGraphLargeAssign
    (e : G.StarEdge v)
    (a : G.MixedLabelGraphAtom edgeLabel x q R)
    (i : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  match a with
  | none => 0
  | some ⟨label, z⟩ =>
      subsetLabelMass edgeLabel q label *
        G.localExtendedProfileLargeAssign (R label) e z i

def mixedLabelGraphTinyAssign
    (e : G.StarEdge v)
    (a : G.MixedLabelGraphAtom edgeLabel x q R) : ℝ :=
  match a with
  | none => 0
  | some ⟨label, z⟩ =>
      subsetLabelMass edgeLabel q label *
        G.localExtendedProfileTinyAssign (R label) e z

theorem subsetLabelMass_nonneg_local
    (hq0 : ∀ S, 0 ≤ q S) (label : Label) :
    0 ≤ subsetLabelMass edgeLabel q label := by
  unfold subsetLabelMass
  apply Finset.sum_nonneg
  intro S _
  split
  · exact hq0 S
  · exact le_rfl

theorem mixedLabelGraphAtomProbability_nonneg
    (hq0 : ∀ S, 0 ≤ q S)
    (hqsum : ∑ S, q S = 1)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (a : G.MixedLabelGraphAtom edgeLabel x q R) :
    0 ≤ G.mixedLabelGraphAtomProbability edgeLabel x q R a := by
  unfold mixedLabelGraphAtomProbability
  apply Subtwo.labelMixtureAtomProbability_nonneg
  · exact G.subsetLabelMass_nonneg_local edgeLabel q hq0
  · exact sum_subsetLabelMass_le_one edgeLabel q hq0 hqsum hqsingle
  · intro label z
    exact G.localExtendedProfileProbability_nonneg
      (R label) hs hqstep hr0 hleft z

theorem sum_mixedLabelGraphAtomProbability :
    (∑ a : G.MixedLabelGraphAtom edgeLabel x q R,
      G.mixedLabelGraphAtomProbability edgeLabel x q R a) = 1 := by
  unfold mixedLabelGraphAtomProbability
  exact Subtwo.sum_labelMixtureAtomProbability
    (fun label ↦ G.LocalExtendedProfileState (R label))
    (subsetLabelMass edgeLabel q)
    (fun label z ↦ G.localExtendedProfileProbability (R label) z)
    (fun label ↦ G.sum_localExtendedProfileProbability (R label))

theorem sum_mixedLabelGraphLargeAssign
    (hq0 : ∀ S, 0 ≤ q S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel e = label)
    (e : G.StarEdge v) :
    (∑ a : G.MixedLabelGraphAtom edgeLabel x q R,
      ∑ i, G.mixedLabelGraphLargeAssign edgeLabel x q R e a i) =
      if β ≤ G.weight e.1 then s * x e else 0 := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [mixedLabelGraphLargeAssign, Finset.sum_const_zero, zero_add]
  calc
    (∑ label : Label,
      ∑ z : G.LocalExtendedProfileState (R label),
        ∑ i, subsetLabelMass edgeLabel q label *
          G.localExtendedProfileLargeAssign (R label) e z i) =
      ∑ label : Label, subsetLabelMass edgeLabel q label *
        (∑ z : G.LocalExtendedProfileState (R label),
          ∑ i, G.localExtendedProfileLargeAssign (R label) e z i) := by
      apply Finset.sum_congr rfl
      intro label _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
    _ = ∑ label : Label, subsetLabelMass edgeLabel q label *
        (if β ≤ G.weight e.1 then
          s * G.conditionalEndpointProposal edgeLabel x q label e
          else 0) := by
      apply Finset.sum_congr rfl
      intro label _
      rw [G.sum_localExtendedProfileLargeAssign (R label) e]
    _ = if β ≤ G.weight e.1 then s * x e else 0 := by
      have hmix := sum_labelMass_mul_conditionalMarginal
        edgeLabel x q hq0 hqmarg hqsingle e
      change (∑ label : Label, subsetLabelMass edgeLabel q label *
        G.conditionalEndpointProposal edgeLabel x q label e) = x e at hmix
      by_cases he : β ≤ G.weight e.1
      · simp only [he, ite_true]
        calc
          (∑ label : Label, subsetLabelMass edgeLabel q label *
            (s * G.conditionalEndpointProposal edgeLabel x q label e)) =
              s * (∑ label : Label, subsetLabelMass edgeLabel q label *
                G.conditionalEndpointProposal edgeLabel x q label e) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro label _
            ring
          _ = s * x e := by rw [hmix]
      · simp [he]

theorem sum_mixedLabelGraphTinyAssign
    (hq0 : ∀ S, 0 ≤ q S)
    (hqmarg : ∀ e, (∑ S, if e ∈ S then q S else 0) = x e)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel e = label)
    (e : G.StarEdge v) :
    (∑ a : G.MixedLabelGraphAtom edgeLabel x q R,
      G.mixedLabelGraphTinyAssign edgeLabel x q R e a) =
      if G.weight e.1 < β then s * x e else 0 := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [mixedLabelGraphTinyAssign, zero_add]
  calc
    (∑ label : Label,
      ∑ z : G.LocalExtendedProfileState (R label),
        subsetLabelMass edgeLabel q label *
          G.localExtendedProfileTinyAssign (R label) e z) =
      ∑ label : Label, subsetLabelMass edgeLabel q label *
        (∑ z : G.LocalExtendedProfileState (R label),
          G.localExtendedProfileTinyAssign (R label) e z) := by
      apply Finset.sum_congr rfl
      intro label _
      rw [Finset.mul_sum]
    _ = ∑ label : Label, subsetLabelMass edgeLabel q label *
        (if G.weight e.1 < β then
          s * G.conditionalEndpointProposal edgeLabel x q label e
          else 0) := by
      apply Finset.sum_congr rfl
      intro label _
      rw [G.sum_localExtendedProfileTinyAssign (R label) e]
    _ = if G.weight e.1 < β then s * x e else 0 := by
      have hmix := sum_labelMass_mul_conditionalMarginal
        edgeLabel x q hq0 hqmarg hqsingle e
      change (∑ label : Label, subsetLabelMass edgeLabel q label *
        G.conditionalEndpointProposal edgeLabel x q label e) = x e at hmix
      by_cases he : G.weight e.1 < β
      · simp only [he, ite_true]
        calc
          (∑ label : Label, subsetLabelMass edgeLabel q label *
            (s * G.conditionalEndpointProposal edgeLabel x q label e)) =
              s * (∑ label : Label, subsetLabelMass edgeLabel q label *
                G.conditionalEndpointProposal edgeLabel x q label e) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro label _
            ring
          _ = s * x e := by rw [hmix]
      · simp [he]

theorem sum_mixedLabelGraphLargeAssign_star_le
    (hq0 : ∀ S, 0 ≤ q S)
    (hqsum : ∑ S, q S = 1)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (a : G.MixedLabelGraphAtom edgeLabel x q R)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    (∑ e : G.StarEdge v,
      G.mixedLabelGraphLargeAssign edgeLabel x q R e a i) ≤
      G.mixedLabelGraphAtomProbability edgeLabel x q R a := by
  cases a with
  | none =>
      simp only [mixedLabelGraphLargeAssign, Finset.sum_const_zero,
        mixedLabelGraphAtomProbability,
        Subtwo.labelMixtureAtomProbability]
      exact sub_nonneg.mpr
        (sum_subsetLabelMass_le_one edgeLabel q hq0 hqsum hqsingle)
  | some lz =>
      simp only [mixedLabelGraphLargeAssign,
        mixedLabelGraphAtomProbability,
        Subtwo.labelMixtureAtomProbability]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (G.sum_localExtendedProfileLargeAssign_star_le
          (R lz.1) hs hqstep hr0 hleft lz.2 i)
        (G.subsetLabelMass_nonneg_local edgeLabel q hq0 lz.1)

theorem sum_weight_mul_mixedLabelGraphTinyAssign_le
    (hq0 : ∀ S, 0 ≤ q S)
    (hqsum : ∑ S, q S = 1)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (a : G.MixedLabelGraphAtom edgeLabel x q R) :
    (∑ e : G.StarEdge v,
      G.weight e.1 *
        G.mixedLabelGraphTinyAssign edgeLabel x q R e a) ≤
      G.mixedLabelGraphAtomProbability edgeLabel x q R a := by
  cases a with
  | none =>
      simp only [mixedLabelGraphTinyAssign, mul_zero,
        Finset.sum_const_zero, mixedLabelGraphAtomProbability,
        Subtwo.labelMixtureAtomProbability]
      exact sub_nonneg.mpr
        (sum_subsetLabelMass_le_one edgeLabel q hq0 hqsum hqsingle)
  | some lz =>
      simp only [mixedLabelGraphTinyAssign,
        mixedLabelGraphAtomProbability,
        Subtwo.labelMixtureAtomProbability]
      calc
        (∑ e : G.StarEdge v,
          G.weight e.1 *
            (subsetLabelMass edgeLabel q lz.1 *
              G.localExtendedProfileTinyAssign (R lz.1) e lz.2)) =
          subsetLabelMass edgeLabel q lz.1 *
            (∑ e : G.StarEdge v,
              G.weight e.1 *
                G.localExtendedProfileTinyAssign (R lz.1) e lz.2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ ≤ subsetLabelMass edgeLabel q lz.1 *
            G.localExtendedProfileProbability (R lz.1) lz.2 :=
          mul_le_mul_of_nonneg_left
            (G.sum_weight_mul_localExtendedProfileTinyAssign_le
              (R lz.1) hs hqstep hr0 hleft lz.2)
            (G.subsetLabelMass_nonneg_local edgeLabel q hq0 lz.1)

end WeightedMultigraph

end

end WeightedEdgeColoring
