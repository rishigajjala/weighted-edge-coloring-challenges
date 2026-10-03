import WeightedEdgeColoring.SubtwoLabelPackedDecoder
import WeightedEdgeColoring.SubtwoLabelConditionalLaw

/-!
# One-label categorical atom for each color

The old profile selector takes one local state per color.  Here the state
first chooses an endpoint label with its *original* probability mass, then
a conditional profile state for that label.  A separate `none` state carries
the leftover probability.  This is the finite state needed by the labelled
packed-word decoder; it has exact original edge marginals and cannot assign
an edge to a different label.
-/

namespace WeightedEdgeColoring.Subtwo

open scoped BigOperators

noncomputable section

variable {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (State : Label → Type*) [∀ label, Fintype (State label)]

/-- One inactive atom or one endpoint label paired with its conditional
profile state. -/
abbrev LabelMixtureAtom := Option (Sigma State)

def labelMixtureAtomLabel : LabelMixtureAtom State → Option Label
  | none => none
  | some ⟨label, _⟩ => some label

/-- Original outer mass times normalized conditional inner law. -/
def labelMixtureAtomProbability
    (mass : Label → ℝ)
    (innerProb : ∀ label, State label → ℝ) :
    LabelMixtureAtom State → ℝ
  | none => 1 - ∑ label, mass label
  | some ⟨label, z⟩ => mass label * innerProb label z

theorem labelMixtureAtomProbability_nonneg
    (mass : Label → ℝ)
    (innerProb : ∀ label, State label → ℝ)
    (hmass0 : ∀ label, 0 ≤ mass label)
    (hmassSum : ∑ label, mass label ≤ 1)
    (hinner0 : ∀ label z, 0 ≤ innerProb label z) :
    ∀ a, 0 ≤ labelMixtureAtomProbability State mass innerProb a := by
  intro a
  cases a with
  | none => exact sub_nonneg.mpr hmassSum
  | some lz => exact mul_nonneg (hmass0 lz.1) (hinner0 lz.1 lz.2)

theorem sum_labelMixtureAtomProbability
    (mass : Label → ℝ)
    (innerProb : ∀ label, State label → ℝ)
    (hinnerSum : ∀ label, ∑ z, innerProb label z = 1) :
    (∑ a : LabelMixtureAtom State,
      labelMixtureAtomProbability State mass innerProb a) = 1 := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [labelMixtureAtomProbability]
  calc
    (1 - ∑ label, mass label) +
      ∑ label, ∑ z : State label, mass label * innerProb label z =
        (1 - ∑ label, mass label) +
          ∑ label, mass label * (∑ z : State label, innerProb label z) := by
      congr 1
      apply Finset.sum_congr rfl
      intro label _
      rw [Finset.mul_sum]
    _ = 1 := by simp [hinnerSum]

/-- An inactive atom uses no edge; an active atom delegates to exactly its
selected label's conditional profile. -/
def labelMixtureAtomUse {I : Type*}
    (innerUse : ∀ label, State label → I → ℝ)
    (a : LabelMixtureAtom State) (i : I) : ℝ :=
  match a with
  | none => 0
  | some ⟨label, z⟩ => innerUse label z i

/-- Integrating an edge-use statistic against the mixture is exactly the
outer-mass-weighted sum of its conditional profile expectations. -/
theorem sum_labelMixtureAtomProbability_mul_use
    {I : Type*} (mass : Label → ℝ)
    (innerProb : ∀ label, State label → ℝ)
    (innerUse : ∀ label, State label → I → ℝ) (i : I) :
    (∑ a : LabelMixtureAtom State,
      labelMixtureAtomProbability State mass innerProb a *
        labelMixtureAtomUse State innerUse a i) =
      ∑ label, mass label *
        (∑ z : State label, innerProb label z * innerUse label z i) := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [labelMixtureAtomProbability, labelMixtureAtomUse,
    mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro label _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Positive use of an edge certifies that the atom's chosen label is the
edge's endpoint label. -/
theorem positive_labelMixtureAtomUse_matches
    {I : Type*} (edgeLabel : I → Label)
    (innerUse : ∀ label, State label → I → ℝ)
    (hsupport : ∀ label z i, 0 < innerUse label z i →
      edgeLabel i = label)
    (a : LabelMixtureAtom State) (i : I)
    (hpos : 0 < labelMixtureAtomUse State innerUse a i) :
    labelMixtureAtomLabel State a = some (edgeLabel i) := by
  cases a with
  | none => simp [labelMixtureAtomUse] at hpos
  | some lz =>
      have heq := hsupport lz.1 lz.2 i hpos
      simp [labelMixtureAtomLabel, heq]

/-- Fixed label and profile alphabets give a fixed atom alphabet. -/
theorem labelMixtureAtom_card_le
    (N : ℕ) (hcard : ∀ label, Fintype.card (State label) ≤ N) :
    Fintype.card (LabelMixtureAtom State) ≤
      1 + Fintype.card Label * N := by
  classical
  calc
    Fintype.card (LabelMixtureAtom State) =
        Fintype.card (Sigma State) + 1 := Fintype.card_option
    _ ≤ Fintype.card Label * N + 1 := by
      exact Nat.add_le_add_right
        (labelDependentAtom_card_le State N hcard) 1
    _ = 1 + Fintype.card Label * N := by omega

end

end WeightedEdgeColoring.Subtwo

namespace WeightedEdgeColoring.Subtwo

open scoped BigOperators

noncomputable section

variable {I Label : Type*}
  [Fintype I] [DecidableEq I]
  [Fintype Label] [DecidableEq Label]
  (State : Label → Type*) [∀ label, Fintype (State label)]

/-- The actual original edge marginals are recovered by the one-label atom
once each conditional profile realizes its conditional marginal.  Zero-mass
labels contribute zero, so no division by zero enters the construction. -/
theorem sum_labelMixtureAtomProbability_mul_use_eq_original
    (edgeLabel : I → Label) (x : I → ℝ)
    (q : Finset I → ℝ)
    (hq0 : ∀ S, 0 ≤ q S)
    (hqmarg : ∀ i, (∑ S, if i ∈ S then q S else 0) = x i)
    (hqsingle : ∀ S, q S ≠ 0 → S ≠ ∅ →
      ∃ a : Label, ∀ i ∈ S, edgeLabel i = a)
    (innerProb : ∀ label, State label → ℝ)
    (innerUse : ∀ label, State label → I → ℝ)
    (hinnerMarg : ∀ label i,
      (∑ z : State label, innerProb label z * innerUse label z i) =
        if 0 < subsetLabelMass edgeLabel q label then
          (if edgeLabel i = label then
            x i / subsetLabelMass edgeLabel q label else 0)
        else 0)
    (i : I) :
    (∑ a : LabelMixtureAtom State,
      labelMixtureAtomProbability State
          (subsetLabelMass edgeLabel q) innerProb a *
        labelMixtureAtomUse State innerUse a i) = x i := by
  rw [sum_labelMixtureAtomProbability_mul_use]
  simp_rw [hinnerMarg]
  exact sum_labelMass_mul_conditionalMarginal
    edgeLabel x q hq0 hqmarg hqsingle i

end

end WeightedEdgeColoring.Subtwo
