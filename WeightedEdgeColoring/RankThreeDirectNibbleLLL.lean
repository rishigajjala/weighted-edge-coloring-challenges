import WeightedEdgeColoring.RankThreeDirectBernoulliLLL

/-!
# A direct local-lemma nibble with linear preservation rows

Besides conflicting pairs and lower-tail coverage rows, this file allows
upper-tail rows.  An upper row can record any linear overestimate for the
number or weight of objects deleted by the selected options.  Thus one LLL
outcome can be conflict-free, cover every declared coarse group, and preserve
all declared residual degrees and codegrees.

The final theorem uses two LLL weights.  Conflict events get `pairX`; every
linear row gets `rowX`.  A common cap `cap` turns support-incidence estimates
into explicit powers of `1-cap`.  Small coverage groups need not be declared:
applications may take the lower-row type to be a subtype of groups whose mean
is above the desired scale.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x y z

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  {Conflict : Type x} {LowerRow : Type y} {UpperRow : Type z}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [Fintype Conflict] [Fintype LowerRow] [Fintype UpperRow]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  [DecidableEq Conflict] [DecidableEq LowerRow] [DecidableEq UpperRow]

/-- Conflict events, lower-tail coverage rows, and upper-tail deletion rows. -/
abbrev DirectNibbleBadIndex (Conflict LowerRow UpperRow : Type*) :=
  Conflict ⊕ (LowerRow ⊕ UpperRow)

/-- The coordinates with nonzero coefficient in a linear row. -/
noncomputable def linearRowSupport
    (a : LowerRow → Option → ℝ) (r : LowerRow) : Finset Option :=
  Finset.univ.filter fun o ↦ a r o ≠ 0

/-- Expected value of one linear row under the independent thinning. -/
noncomputable def linearRowMean
    (q : Option → ℝ) (a : LowerRow → Option → ℝ) (r : LowerRow) : ℝ :=
  mean (insideParameter q (linearRowSupport a r))
    (fun o : Inside (linearRowSupport a r) ↦ a r o)

/-- Support of every bad event in the direct nibble. -/
noncomputable def directNibbleSupport
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) :
    DirectNibbleBadIndex Conflict LowerRow UpperRow → Finset Option
  | Sum.inl c => conflictPairSupport left right c
  | Sum.inr (Sum.inl r) => linearRowSupport lowerWeight r
  | Sum.inr (Sum.inr r) => linearRowSupport upperWeight r

/-- The local bad events: a retained conflict pair, a failed coverage row, or
an excessive deletion-load row. -/
noncomputable def directNibbleLocalBad
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ) (upperThreshold : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c) :
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) →
      Finset (Finset (Inside
        (directNibbleSupport left right lowerWeight upperWeight b)))
  | Sum.inl c => conflictPairLocalBad left right hne c
  | Sum.inr (Sum.inl r) =>
      lowerTail
        (weightedSum (fun o : Inside (linearRowSupport lowerWeight r) ↦
          lowerWeight r o)) (lowerThreshold r)
  | Sum.inr (Sum.inr r) =>
      upperTail
        (weightedSum (fun o : Inside (linearRowSupport upperWeight r) ↦
          upperWeight r o)) (upperThreshold r)

/-- Other direct-nibble events reading at least one common option. -/
noncomputable def directNibbleNeighbor
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) :
    Finset (DirectNibbleBadIndex Conflict LowerRow UpperRow) :=
  Finset.univ.filter fun a ↦ a ≠ b ∧
    ¬ Disjoint (directNibbleSupport left right lowerWeight upperWeight b)
      (directNibbleSupport left right lowerWeight upperWeight a)

/-- Conflict-pair and upper-tail events are increasing; lower-tail coverage
events are decreasing. -/
def directNibbleIsIncreasing :
    DirectNibbleBadIndex Conflict LowerRow UpperRow → Bool
  | Sum.inl _ => true
  | Sum.inr (Sum.inl _) => false
  | Sum.inr (Sum.inr _) => true

/-- The sharper Harris neighbor graph: only opposite-polarity events whose
supports overlap.  Same-polarity events are handled by negative association
with their complements. -/
noncomputable def directNibbleMixedNeighbor
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) :
    Finset (DirectNibbleBadIndex Conflict LowerRow UpperRow) :=
  Finset.univ.filter fun a ↦
    directNibbleIsIncreasing a ≠ directNibbleIsIncreasing b ∧
      ¬ Disjoint (directNibbleSupport left right lowerWeight upperWeight b)
        (directNibbleSupport left right lowerWeight upperWeight a)

/-- Opposite-polarity events containing one option coordinate. -/
noncomputable def directNibbleMixedIncidence
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) (o : Option) :
    Finset (DirectNibbleBadIndex Conflict LowerRow UpperRow) :=
  Finset.univ.filter fun a ↦
    directNibbleIsIncreasing a ≠ directNibbleIsIncreasing b ∧
      o ∈ directNibbleSupport left right lowerWeight upperWeight a

/-- Cross-polarity incidence gives the degree in the Harris graph. -/
theorem directNibbleMixedNeighbor_card_le
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) (L : ℕ)
    (hincidence : ∀ o,
      (directNibbleMixedIncidence left right lowerWeight upperWeight b o).card ≤ L)
    :
    (directNibbleMixedNeighbor left right lowerWeight upperWeight b).card ≤
      (directNibbleSupport left right lowerWeight upperWeight b).card * L := by
  have hsub : directNibbleMixedNeighbor left right lowerWeight upperWeight b ⊆
      (directNibbleSupport left right lowerWeight upperWeight b).biUnion
        (directNibbleMixedIncidence left right lowerWeight upperWeight b) := by
    intro a ha
    have hdata := (Finset.mem_filter.mp ha).2
    rw [Finset.not_disjoint_iff] at hdata
    rcases hdata.2 with ⟨o, hob, hoa⟩
    exact Finset.mem_biUnion.mpr ⟨o, hob,
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hdata.1, hoa⟩⟩
  calc
    (directNibbleMixedNeighbor left right lowerWeight upperWeight b).card ≤
        ((directNibbleSupport left right lowerWeight upperWeight b).biUnion
          (directNibbleMixedIncidence left right lowerWeight upperWeight b)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ o ∈ directNibbleSupport left right lowerWeight upperWeight b,
        (directNibbleMixedIncidence left right lowerWeight upperWeight b o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ directNibbleSupport left right lowerWeight upperWeight b, L := by
      exact Finset.sum_le_sum fun o _ ↦ hincidence o
    _ = (directNibbleSupport left right lowerWeight upperWeight b).card * L := by
      simp

/-- Direct-nibble events containing one option coordinate. -/
noncomputable def directNibbleIncidence
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (o : Option) :
    Finset (DirectNibbleBadIndex Conflict LowerRow UpperRow) :=
  Finset.univ.filter fun b ↦
    o ∈ directNibbleSupport left right lowerWeight upperWeight b

/-- Listed conflicts in which an option occurs. -/
noncomputable def optionConflictIncidence
    (left right : Conflict → Option) (o : Option) : Finset Conflict :=
  Finset.univ.filter fun c ↦ o = left c ∨ o = right c

/-- Linear rows whose support contains an option. -/
noncomputable def linearRowIncidence
    (a : LowerRow → Option → ℝ) (o : Option) : Finset LowerRow :=
  Finset.univ.filter fun r ↦ o ∈ linearRowSupport a r

/-- The combined incidence is exactly conflict incidence plus the incidences
of the lower and upper linear rows. -/
theorem directNibbleIncidence_card
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (o : Option) :
    (directNibbleIncidence left right lowerWeight upperWeight o).card =
      (optionConflictIncidence left right o).card +
        (linearRowIncidence lowerWeight o).card +
          (linearRowIncidence upperWeight o).card := by
  have hset :
      directNibbleIncidence left right lowerWeight upperWeight o =
        (optionConflictIncidence left right o).disjSum
          ((linearRowIncidence lowerWeight o).disjSum
            (linearRowIncidence upperWeight o)) := by
    ext b
    rcases b with c | r
    · simp [directNibbleIncidence, directNibbleSupport,
        optionConflictIncidence, conflictPairSupport]
    · rcases r with r | r
      · simp [directNibbleIncidence, directNibbleSupport,
          linearRowIncidence]
      · simp [directNibbleIncidence, directNibbleSupport,
          linearRowIncidence]
  rw [hset, Finset.card_disjSum, Finset.card_disjSum]
  omega

/-- Separate `O(m)`, lower-row, and upper-row incidence estimates combine
additively.  In particular, a constant number of coarse groups costs only an
additive constant here. -/
theorem directNibbleIncidence_card_le_add
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (D Rₗ Rᵤ : ℕ)
    (hconflict : ∀ o,
      (optionConflictIncidence left right o).card ≤ D)
    (hlower : ∀ o, (linearRowIncidence lowerWeight o).card ≤ Rₗ)
    (hupper : ∀ o, (linearRowIncidence upperWeight o).card ≤ Rᵤ)
    (o : Option) :
    (directNibbleIncidence left right lowerWeight upperWeight o).card ≤
      D + Rₗ + Rᵤ := by
  rw [directNibbleIncidence_card]
  exact Nat.add_le_add (Nat.add_le_add (hconflict o) (hlower o)) (hupper o)

/-- A pair event sees only lower coverage rows in the mixed graph. -/
theorem mixedIncidence_pair_card
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (c : Conflict) (o : Option) :
    (directNibbleMixedIncidence left right lowerWeight upperWeight
      (Sum.inl c) o).card = (linearRowIncidence lowerWeight o).card := by
  have hset :
      directNibbleMixedIncidence left right lowerWeight upperWeight
          (Sum.inl c) o =
        (∅ : Finset Conflict).disjSum
          ((linearRowIncidence lowerWeight o).disjSum (∅ : Finset UpperRow)) := by
    ext b
    rcases b with b | b
    · simp [directNibbleMixedIncidence, directNibbleIsIncreasing]
    · rcases b with b | b
      · simp [directNibbleMixedIncidence, directNibbleIsIncreasing,
          directNibbleSupport, linearRowIncidence]
      · simp [directNibbleMixedIncidence, directNibbleIsIncreasing]
  rw [hset, Finset.card_disjSum, Finset.card_disjSum]
  simp

/-- An upper deletion row also sees only lower coverage rows. -/
theorem mixedIncidence_upper_card
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (r : UpperRow) (o : Option) :
    (directNibbleMixedIncidence left right lowerWeight upperWeight
      (Sum.inr (Sum.inr r)) o).card =
        (linearRowIncidence lowerWeight o).card := by
  have hset :
      directNibbleMixedIncidence left right lowerWeight upperWeight
          (Sum.inr (Sum.inr r)) o =
        (∅ : Finset Conflict).disjSum
          ((linearRowIncidence lowerWeight o).disjSum (∅ : Finset UpperRow)) := by
    ext b
    rcases b with b | b
    · simp [directNibbleMixedIncidence, directNibbleIsIncreasing]
    · rcases b with b | b
      · simp [directNibbleMixedIncidence, directNibbleIsIncreasing,
          directNibbleSupport, linearRowIncidence]
      · simp [directNibbleMixedIncidence, directNibbleIsIncreasing]
  rw [hset, Finset.card_disjSum, Finset.card_disjSum]
  simp

/-- A lower coverage row sees conflicts and upper deletion rows, but no other
lower row. -/
theorem mixedIncidence_lower_card
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (r : LowerRow) (o : Option) :
    (directNibbleMixedIncidence left right lowerWeight upperWeight
      (Sum.inr (Sum.inl r)) o).card =
        (optionConflictIncidence left right o).card +
          (linearRowIncidence upperWeight o).card := by
  have hset :
      directNibbleMixedIncidence left right lowerWeight upperWeight
          (Sum.inr (Sum.inl r)) o =
        (optionConflictIncidence left right o).disjSum
          ((∅ : Finset LowerRow).disjSum (linearRowIncidence upperWeight o)) := by
    ext b
    rcases b with b | b
    · simp [directNibbleMixedIncidence, directNibbleIsIncreasing,
        directNibbleSupport, optionConflictIncidence, conflictPairSupport]
    · rcases b with b | b
      · simp [directNibbleMixedIncidence, directNibbleIsIncreasing]
      · simp [directNibbleMixedIncidence, directNibbleIsIncreasing,
          directNibbleSupport, linearRowIncidence]
  rw [hset, Finset.card_disjSum, Finset.card_disjSum]
  simp

theorem directNibbleNeighbor_nonneighbor_disjoint
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (b a : DirectNibbleBadIndex Conflict LowerRow UpperRow)
    (ha : a ∉ insert b
      (directNibbleNeighbor left right lowerWeight upperWeight b)) :
    Disjoint (directNibbleSupport left right lowerWeight upperWeight b)
      (directNibbleSupport left right lowerWeight upperWeight a) := by
  by_contra h
  apply ha
  by_cases hab : a = b
  · exact Finset.mem_insert.mpr (Or.inl hab)
  · exact Finset.mem_insert.mpr (Or.inr (by
      simp [directNibbleNeighbor, hab, h]))

/-- Support size times coordinate incidence bounds the dependency degree. -/
theorem directNibbleNeighbor_card_le
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ) (L : ℕ)
    (hincidence : ∀ o,
      (directNibbleIncidence left right lowerWeight upperWeight o).card ≤ L)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) :
    (directNibbleNeighbor left right lowerWeight upperWeight b).card ≤
      (directNibbleSupport left right lowerWeight upperWeight b).card * L := by
  have hsub : directNibbleNeighbor left right lowerWeight upperWeight b ⊆
      (directNibbleSupport left right lowerWeight upperWeight b).biUnion
        (directNibbleIncidence left right lowerWeight upperWeight) := by
    intro a ha
    have hoverlap := (Finset.mem_filter.mp ha).2.2
    rw [Finset.not_disjoint_iff] at hoverlap
    rcases hoverlap with ⟨o, hob, hoa⟩
    exact Finset.mem_biUnion.mpr ⟨o, hob,
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hoa⟩⟩
  calc
    (directNibbleNeighbor left right lowerWeight upperWeight b).card ≤
        ((directNibbleSupport left right lowerWeight upperWeight b).biUnion
          (directNibbleIncidence left right lowerWeight upperWeight)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ o ∈ directNibbleSupport left right lowerWeight upperWeight b,
        (directNibbleIncidence left right lowerWeight upperWeight o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ directNibbleSupport left right lowerWeight upperWeight b, L := by
      exact Finset.sum_le_sum fun o _ ↦ hincidence o
    _ = (directNibbleSupport left right lowerWeight upperWeight b).card * L := by
      simp

/-- A uniform upper bound on event weights and a degree bound give a useful
lower bound for the asymmetric-LLL product. -/
theorem one_sub_cap_pow_le_neighbor_product
    {B : Type*} [Fintype B] [DecidableEq B]
    (neighbor : B → Finset B) (x : B → ℝ) (cap : ℝ) (d : ℕ) (b : B)
    (hcap0 : 0 ≤ cap) (hcap1 : cap ≤ 1)
    (hx0 : ∀ a, 0 ≤ x a) (hxcap : ∀ a, x a ≤ cap)
    (hdegree : (neighbor b).card ≤ d) :
    (1 - cap) ^ d ≤ ∏ a ∈ neighbor b, (1 - x a) := by
  calc
    (1 - cap) ^ d ≤ (1 - cap) ^ (neighbor b).card :=
      pow_le_pow_of_le_one (sub_nonneg.mpr hcap1)
        (sub_le_self 1 hcap0) hdegree
    _ = ∏ _a ∈ neighbor b, (1 - cap) := by simp
    _ ≤ ∏ a ∈ neighbor b, (1 - x a) := by
      apply Finset.prod_le_prod
      · intro a ha
        exact sub_nonneg.mpr hcap1
      · intro a ha
        exact sub_le_sub_left (hxcap a) 1

/-- Two event-weight scales, one for pairs and one for linear rows. -/
def directNibbleLLLWeight (pairX rowX : ℝ) :
    DirectNibbleBadIndex Conflict LowerRow UpperRow → ℝ
  | Sum.inl _ => pairX
  | Sum.inr _ => rowX

/-- Exact asymmetric direct-nibble theorem.  Lower rows give coverage and
upper rows bound arbitrary linear deletion loads. -/
theorem exists_partialMatching_with_lower_and_upper_rows
    (H : RankThreeOptionSystem Job Slot Option)
    (left right : Conflict → Option)
    (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold lowerLambda : LowerRow → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬ H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (x : DirectNibbleBadIndex Conflict LowerRow UpperRow → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hlowerLambda : ∀ r, 0 ≤ lowerLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b < 1)
    (hpair : ∀ c,
      q (left c) * q (right c) ≤ x (Sum.inl c) *
        ∏ b ∈ directNibbleNeighbor left right lowerWeight upperWeight
          (Sum.inl c), (1 - x b))
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) *
          mean (insideParameter q (linearRowSupport lowerWeight r))
            (fun o : Inside (linearRowSupport lowerWeight r) ↦
              lowerWeight r o)) ≤
        x (Sum.inr (Sum.inl r)) *
          ∏ b ∈ directNibbleNeighbor left right lowerWeight upperWeight
            (Sum.inr (Sum.inl r)), (1 - x b))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) *
          mean (insideParameter q (linearRowSupport upperWeight r))
            (fun o : Inside (linearRowSupport upperWeight r) ↦
              upperWeight r o)) ≤
        x (Sum.inr (Sum.inr r)) *
          ∏ b ∈ directNibbleNeighbor left right lowerWeight upperWeight
            (Sum.inr (Sum.inr r)), (1 - x b)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) := by
  let support := directNibbleSupport left right lowerWeight upperWeight
  let localBad := directNibbleLocalBad left right lowerWeight upperWeight
    lowerThreshold upperThreshold hne
  let neighbor := directNibbleNeighbor left right lowerWeight upperWeight
  have hlocal : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass (insideParameter q (support b))) (localBad b) ≤
          x b * ∏ a ∈ neighbor b, (1 - x a) := by
    intro b
    rcases b with c | r
    · change WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (conflictPairSupport left right c)))
        (conflictPairLocalBad left right hne c) ≤
          x (Sum.inl c) *
            ∏ a ∈ directNibbleNeighbor left right lowerWeight upperWeight
              (Sum.inl c), (1 - x a)
      rw [conflictPairLocalBad_mass left right q hne c]
      exact hpair c
    · rcases r with r | r
      · exact (bernoulli_lowerTail_le
          (insideParameter q (linearRowSupport lowerWeight r))
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (lowerThreshold r) (lowerLambda r)
          (fun o ↦ hq0 o) (fun o ↦ hq1 o)
          (fun o ↦ hlower0 r o) (fun o ↦ hlower1 r o)
          (hlowerLambda r)).trans (hlower r)
      · exact (bernoulli_upperTail_le
          (insideParameter q (linearRowSupport upperWeight r))
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (upperThreshold r) (upperLambda r)
          (fun o ↦ hq0 o) (fun o ↦ hq1 o)
          (fun o ↦ hupper0 r o) (fun o ↦ hupper1 r o)
          (hupperLambda r)).trans (hupper r)
  have hpositive :=
    WeightedEdgeColoring.FiniteBernoulliSupportSplit.asymmetric_lopsided_local_lemma_of_disjoint_supports
      q support localBad neighbor x hq0 hq1 hx0 hx1
      (fun b a ha ↦ directNibbleNeighbor_nonneighbor_disjoint
        left right lowerWeight upperWeight b a ha) hlocal
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid
    (fun b ↦ insideCylinder (support b) (localBad b)) Finset.univ
  have hgood : good.Nonempty := by
    by_contra hempty
    have hz : WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) good = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
    rw [hz] at hpositive
    exact lt_irrefl 0 hpositive
  rcases hgood with ⟨S, hS⟩
  have havoid : ∀ b, S ∉ insideCylinder (support b) (localBad b) := by
    simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hS
  refine ⟨S, ?_, ?_, ?_⟩
  · constructor
    · intro o ho p hp hop
      by_contra hcompat
      rcases hcomplete o p hop (Or.inr hcompat) with ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
    · intro o ho p hp howner
      by_contra hop
      rcases hcomplete o p hop (Or.inl howner) with ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directNibbleSupport, directNibbleLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
  · intro r
    have hr := havoid (Sum.inr (Sum.inl r))
    simpa [support, localBad, directNibbleSupport, directNibbleLocalBad,
      lowerTail, not_le] using hr
  · intro r
    have hr := havoid (Sum.inr (Sum.inr r))
    simpa [support, localBad, directNibbleSupport, directNibbleLocalBad,
      upperTail, not_le] using hr

/-- Explicit incidence-based sufficient conditions.  Pair and row events may
have very different LLL weights, but both are bounded by `cap` when estimating
the dependency products. -/
theorem exists_partialMatching_with_lower_and_upper_rows_of_incidence
    (H : RankThreeOptionSystem Job Slot Option)
    (left right : Conflict → Option)
    (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold lowerLambda : LowerRow → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬ H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (L : ℕ) (pairX rowX cap : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hlowerLambda : ∀ r, 0 ≤ lowerLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hincidence : ∀ o,
      (directNibbleIncidence left right lowerWeight upperWeight o).card ≤ L)
    (hpair : ∀ c,
      q (left c) * q (right c) ≤ pairX * (1 - cap) ^ (2 * L))
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) *
          mean (insideParameter q (linearRowSupport lowerWeight r))
            (fun o : Inside (linearRowSupport lowerWeight r) ↦
              lowerWeight r o)) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport lowerWeight r).card * L))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) *
          mean (insideParameter q (linearRowSupport upperWeight r))
            (fun o : Inside (linearRowSupport upperWeight r) ↦
              upperWeight r o)) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport upperWeight r).card * L)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) := by
  let x : DirectNibbleBadIndex Conflict LowerRow UpperRow → ℝ :=
    directNibbleLLLWeight pairX rowX
  have hcap0 : 0 ≤ cap := hpairX0.trans hpairXcap
  have hx0 : ∀ b, 0 ≤ x b := by
    intro b
    rcases b with c | r
    · exact hpairX0
    · exact hrowX0
  have hxcap : ∀ b, x b ≤ cap := by
    intro b
    rcases b with c | r
    · exact hpairXcap
    · exact hrowXcap
  have hx1 : ∀ b, x b < 1 := fun b ↦ (hxcap b).trans_lt hcap1
  apply H.exists_partialMatching_with_lower_and_upper_rows left right q
    lowerWeight upperWeight lowerThreshold lowerLambda upperThreshold
    upperLambda hne hcomplete x hq0 hq1 hlower0 hlower1 hupper0 hupper1
    hlowerLambda hupperLambda hx0 hx1
  · intro c
    apply (hpair c).trans
    apply mul_le_mul_of_nonneg_left _ hpairX0
    apply one_sub_cap_pow_le_neighbor_product
      (directNibbleNeighbor left right lowerWeight upperWeight) x cap (2 * L)
      (Sum.inl c) hcap0 hcap1.le hx0 hxcap
    refine (directNibbleNeighbor_card_le left right lowerWeight upperWeight L
      hincidence (Sum.inl c)).trans ?_
    exact Nat.mul_le_mul_right L (conflictPairSupport_card_le_two left right c)
  · intro r
    apply (hlower r).trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    apply one_sub_cap_pow_le_neighbor_product
      (directNibbleNeighbor left right lowerWeight upperWeight) x cap
      ((linearRowSupport lowerWeight r).card * L) (Sum.inr (Sum.inl r))
      hcap0 hcap1.le hx0 hxcap
    exact directNibbleNeighbor_card_le left right lowerWeight upperWeight L
      hincidence (Sum.inr (Sum.inl r))
  · intro r
    apply (hupper r).trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    apply one_sub_cap_pow_le_neighbor_product
      (directNibbleNeighbor left right lowerWeight upperWeight) x cap
      ((linearRowSupport upperWeight r).card * L) (Sum.inr (Sum.inr r))
      hcap0 hcap1.le hx0 hxcap
    exact directNibbleNeighbor_card_le left right lowerWeight upperWeight L
      hincidence (Sum.inr (Sum.inr r))

/-- Constant-fraction coarse coverage.  Every declared lower row has mean at
least `eta`; the single displayed exponential inequality pays for its whole
support neighborhood.  Taking `eta = Ω(m)` and `cap = O(m⁻²)` makes the two
exponents directly comparable. -/
theorem exists_partialMatching_with_coarse_coverage_and_upper_rows
    (H : RankThreeOptionSystem Job Slot Option)
    (left right : Conflict → Option)
    (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬ H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (L : ℕ) (pairX rowX cap delta eta : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hdelta0 : 0 ≤ delta)
    (hcoefficient :
      delta * (1 - delta) + (Real.exp (-delta) - 1) ≤ 0)
    (heta : ∀ r, eta ≤ linearRowMean q lowerWeight r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hpairX0 : 0 ≤ pairX) (hrowX0 : 0 ≤ rowX)
    (hpairXcap : pairX ≤ cap) (hrowXcap : rowX ≤ cap)
    (hcap1 : cap < 1)
    (hincidence : ∀ o,
      (directNibbleIncidence left right lowerWeight upperWeight o).card ≤ L)
    (hpair : ∀ c,
      q (left c) * q (right c) ≤ pairX * (1 - cap) ^ (2 * L))
    (hlowerNumeric : ∀ r,
      Real.exp
        ((delta * (1 - delta) + (Real.exp (-delta) - 1)) * eta) ≤
          rowX * (1 - cap) ^
            ((linearRowSupport lowerWeight r).card * L))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q upperWeight r) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport upperWeight r).card * L)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      (∀ r, (1 - delta) * linearRowMean q lowerWeight r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) := by
  apply H.exists_partialMatching_with_lower_and_upper_rows_of_incidence
    left right q lowerWeight upperWeight
    (fun r ↦ (1 - delta) * linearRowMean q lowerWeight r)
    (fun _ ↦ delta) upperThreshold upperLambda hne hcomplete L pairX rowX cap
    hq0 hq1 hlower0 hlower1 hupper0 hupper1 (fun _ ↦ hdelta0)
    hupperLambda hpairX0 hrowX0 hpairXcap hrowXcap hcap1 hincidence hpair
  · intro r
    apply (Real.exp_le_exp.mpr ?_).trans (hlowerNumeric r)
    calc
      delta * ((1 - delta) * linearRowMean q lowerWeight r) +
          (Real.exp (-delta) - 1) * linearRowMean q lowerWeight r =
          (delta * (1 - delta) + (Real.exp (-delta) - 1)) *
            linearRowMean q lowerWeight r := by ring
      _ ≤ (delta * (1 - delta) + (Real.exp (-delta) - 1)) * eta :=
        mul_le_mul_of_nonpos_left (heta r) hcoefficient
  · intro r
    simpa [linearRowMean] using hupper r

/-- Groups below `eta` can be omitted by using this subtype as the lower-row
index.  Their contribution is then charged directly to the residual budget. -/
abbrev ActiveAbove (meanValue : LowerRow → ℝ) (eta : ℝ) :=
  {r : LowerRow // eta ≤ meanValue r}

end WeightedEdgeColoring.RankThreeOptionSystem
