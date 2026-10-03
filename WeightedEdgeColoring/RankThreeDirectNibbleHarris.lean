import WeightedEdgeColoring.RankThreeDirectNibbleNumeric
import WeightedEdgeColoring.RankThreeDirectNibblePolarity

/-!
# Sharp Harris local lemma for the direct nibble

This module connects the cross-polarity dependency graph to the direct
nibble output.  Conflict and upper-tail events are increasing; coverage
lower tails are decreasing.  Consequently only overlapping events of the
opposite polarity remain in the lopsided neighborhood.
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

/-- The global cylinder event attached to one direct-nibble constraint. -/
noncomputable def directNibbleGlobalBad
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ) (upperThreshold : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (b : DirectNibbleBadIndex Conflict LowerRow UpperRow) :
    Finset (Finset Option) :=
  insideCylinder (directNibbleSupport left right lowerWeight upperWeight b)
    (directNibbleLocalBad left right lowerWeight upperWeight
      lowerThreshold upperThreshold hne b)

/-- Positive mass for outcomes avoiding all direct-nibble events is enough
to extract the desired partial matching, lower coverage, and upper load
bounds. -/
theorem extract_partialMatching_with_lower_and_upper_rows_of_positive
    (H : RankThreeOptionSystem Job Slot Option)
    (left right : Conflict → Option)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ) (upperThreshold : UpperRow → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬ H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (q : Option → ℝ)
    (hpositive : 0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (directNibbleGlobalBad left right lowerWeight upperWeight
          lowerThreshold upperThreshold hne) Finset.univ)) :
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
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid
    (directNibbleGlobalBad left right lowerWeight upperWeight
      lowerThreshold upperThreshold hne) Finset.univ
  have hgood : good.Nonempty := by
    by_contra hempty
    have hz : WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) good = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
    rw [hz] at hpositive
    exact lt_irrefl 0 hpositive
  rcases hgood with ⟨S, hS⟩
  have havoid : ∀ b,
      S ∉ directNibbleGlobalBad left right lowerWeight upperWeight
        lowerThreshold upperThreshold hne b := by
    simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hS
  refine ⟨S, ?_, ?_, ?_⟩
  · constructor
    · intro o ho p hp hop
      by_contra hcompat
      rcases hcomplete o p hop (Or.inr hcompat) with ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl c)
        simp [directNibbleGlobalBad, directNibbleSupport,
          directNibbleLocalBad, conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl c)
        simp [directNibbleGlobalBad, directNibbleSupport,
          directNibbleLocalBad, conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
    · intro o ho p hp howner
      by_contra hop
      rcases hcomplete o p hop (Or.inl howner) with ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl c)
        simp [directNibbleGlobalBad, directNibbleSupport,
          directNibbleLocalBad, conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl c)
        simp [directNibbleGlobalBad, directNibbleSupport,
          directNibbleLocalBad, conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
  · intro r
    have hr := havoid (Sum.inr (Sum.inl r))
    simpa [directNibbleGlobalBad, directNibbleSupport, directNibbleLocalBad,
      lowerTail, not_le] using hr
  · intro r
    have hr := havoid (Sum.inr (Sum.inr r))
    simpa [directNibbleGlobalBad, directNibbleSupport, directNibbleLocalBad,
      upperTail, not_le] using hr

/-- Sharp exact direct-nibble theorem.  The LLL product contains only
support-overlapping events of the opposite monotonicity. -/
theorem exists_partialMatching_with_lower_and_upper_rows_harris
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
        ∏ b ∈ directNibbleMixedNeighbor left right lowerWeight upperWeight
          (Sum.inl c), (1 - x b))
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) *
          linearRowMean q lowerWeight r) ≤
        x (Sum.inr (Sum.inl r)) *
          ∏ b ∈ directNibbleMixedNeighbor left right lowerWeight upperWeight
            (Sum.inr (Sum.inl r)), (1 - x b))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q upperWeight r) ≤
        x (Sum.inr (Sum.inr r)) *
          ∏ b ∈ directNibbleMixedNeighbor left right lowerWeight upperWeight
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
  let polarity : DirectNibbleBadIndex Conflict LowerRow UpperRow → Bool :=
    directNibbleIsIncreasing
  let neighbor : DirectNibbleBadIndex Conflict LowerRow UpperRow →
      Finset (DirectNibbleBadIndex Conflict LowerRow UpperRow) :=
    directNibbleMixedNeighbor left right lowerWeight upperWeight
  have hmonoLocal : ∀ b,
      WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided.HasPolarity (polarity b)
        (localBad b) := by
    intro b
    rcases b with c | r
    · change WeightedEdgeColoring.FiniteBernoulliHarris.IsIncreasing
        (conflictPairLocalBad left right hne c)
      exact conflictPairLocalBad_isIncreasing left right hne c
    · rcases r with r | r
      · change WeightedEdgeColoring.FiniteBernoulliHarris.IsDecreasing
          (lowerTail
            (weightedSum
              (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o))
            (lowerThreshold r))
        exact WeightedEdgeColoring.FiniteBernoulliTailMonotone.lowerTail_weightedSum_isDecreasing
          _ _ (fun o ↦ hlower0 r o)
      · change WeightedEdgeColoring.FiniteBernoulliHarris.IsIncreasing
          (upperTail
            (weightedSum
              (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o))
            (upperThreshold r))
        exact WeightedEdgeColoring.FiniteBernoulliTailMonotone.upperTail_weightedSum_isIncreasing
          _ _ (fun o ↦ hupper0 r o)
  have hmono : ∀ b,
      WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided.HasPolarity (polarity b)
        (insideCylinder (support b) (localBad b)) := by
    intro b
    cases hp : polarity b
    · change WeightedEdgeColoring.FiniteBernoulliHarris.IsDecreasing
        (insideCylinder (support b) (localBad b))
      exact WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isDecreasing
        (support b) (localBad b) (by
          simpa [WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided.HasPolarity, hp] using
            hmonoLocal b)
    · change WeightedEdgeColoring.FiniteBernoulliHarris.IsIncreasing
        (insideCylinder (support b) (localBad b))
      exact WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isIncreasing
        (support b) (localBad b) (by
          simpa [WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided.HasPolarity, hp] using
            hmonoLocal b)
  have hneighbor : ∀ b a, a ≠ b → polarity a ≠ polarity b →
      (¬ Disjoint (support b) (support a) ↔ a ∈ neighbor b) := by
    intro b a hab hpolarity
    dsimp [support, neighbor]
    simp only [directNibbleMixedNeighbor, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (¬ Disjoint
        (directNibbleSupport left right lowerWeight upperWeight b)
        (directNibbleSupport left right lowerWeight upperWeight a)) ↔
      (directNibbleIsIncreasing a ≠ directNibbleIsIncreasing b ∧
        ¬ Disjoint
          (directNibbleSupport left right lowerWeight upperWeight b)
          (directNibbleSupport left right lowerWeight upperWeight a))
    exact ⟨fun h ↦ ⟨hpolarity, h⟩, fun h ↦ h.2⟩
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
            ∏ a ∈ directNibbleMixedNeighbor left right lowerWeight upperWeight
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
    WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided.asymmetric_lopsided_local_lemma_of_polarity_support
      q support localBad polarity neighbor x hq0 hq1 hx0 hx1
      hmonoLocal hmono hneighbor hlocal
  exact H.extract_partialMatching_with_lower_and_upper_rows_of_positive
    left right lowerWeight upperWeight lowerThreshold upperThreshold hne
    hcomplete q (by
      change 0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (WeightedEdgeColoring.FiniteLocalLemma.avoid
          (fun b ↦ insideCylinder
            (directNibbleSupport left right lowerWeight upperWeight b)
            (directNibbleLocalBad left right lowerWeight upperWeight
              lowerThreshold upperThreshold hne b)) Finset.univ)
      exact hpositive)

/-- Incidence-based sharp criterion.  Pairs and upper rows pay only for
coverage-row incidence `R`; lower rows pay for conflict incidence `D` and
upper-row incidence `U`. -/
theorem exists_partialMatching_with_lower_and_upper_rows_harris_of_incidence
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
    (D R U : ℕ) (pairX rowX cap : ℝ)
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
    (hconflictIncidence : ∀ o,
      (optionConflictIncidence left right o).card ≤ D)
    (hlowerIncidence : ∀ o,
      (linearRowIncidence lowerWeight o).card ≤ R)
    (hupperIncidence : ∀ o,
      (linearRowIncidence upperWeight o).card ≤ U)
    (hpair : ∀ c,
      q (left c) * q (right c) ≤
        pairX * (1 - rowX) ^ (2 * R))
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) *
          linearRowMean q lowerWeight r) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport lowerWeight r).card * (D + U)))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q upperWeight r) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport upperWeight r).card * R)) :
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
  have hrowX1 : rowX ≤ 1 := hrowXcap.trans hcap1.le
  have hx0 : ∀ b, 0 ≤ x b := by
    intro b
    rcases b with c | r
    · exact hpairX0
    · exact hrowX0
  have hx1 : ∀ b, x b < 1 := by
    intro b
    rcases b with c | r
    · exact hpairXcap.trans_lt hcap1
    · exact hrowXcap.trans_lt hcap1
  apply H.exists_partialMatching_with_lower_and_upper_rows_harris
    left right q lowerWeight upperWeight lowerThreshold lowerLambda
    upperThreshold upperLambda hne hcomplete x hq0 hq1 hlower0 hlower1
    hupper0 hupper1 hlowerLambda hupperLambda hx0 hx1
  · intro c
    apply (hpair c).trans
    apply mul_le_mul_of_nonneg_left _ hpairX0
    exact pair_cross_product_lower_bound left right lowerWeight upperWeight
      pairX rowX R hrowX0 hrowX1 hlowerIncidence c
  · intro r
    apply (hlower r).trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    exact lower_cross_product_lower_bound left right lowerWeight upperWeight
      pairX rowX cap D U hcap0 hcap1.le hpairXcap hrowXcap
      hconflictIncidence hupperIncidence r
  · intro r
    apply (hupper r).trans
    apply mul_le_mul_of_nonneg_left _ hrowX0
    exact upper_cross_product_lower_bound left right lowerWeight upperWeight
      pairX rowX R hrowX0 hrowX1 hlowerIncidence r

/-- Constant-fraction coarse coverage under the sharp Harris incidence
criterion.  The lower-row type may be `ActiveAbove mean eta`, so rows below
the `eta` scale are omitted and charged to the residual budget. -/
theorem exists_partialMatching_with_coarse_coverage_harris
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
    (D R U : ℕ) (pairX rowX cap delta eta : ℝ)
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
    (hconflictIncidence : ∀ o,
      (optionConflictIncidence left right o).card ≤ D)
    (hlowerIncidence : ∀ o,
      (linearRowIncidence lowerWeight o).card ≤ R)
    (hupperIncidence : ∀ o,
      (linearRowIncidence upperWeight o).card ≤ U)
    (hpair : ∀ c,
      q (left c) * q (right c) ≤
        pairX * (1 - rowX) ^ (2 * R))
    (hlowerNumeric : ∀ r,
      Real.exp
        ((delta * (1 - delta) + (Real.exp (-delta) - 1)) * eta) ≤
        rowX * (1 - cap) ^
          ((linearRowSupport lowerWeight r).card * (D + U)))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) *
          linearRowMean q upperWeight r) ≤
        rowX * (1 - rowX) ^
          ((linearRowSupport upperWeight r).card * R)) :
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
  apply H.exists_partialMatching_with_lower_and_upper_rows_harris_of_incidence
    left right q lowerWeight upperWeight
    (fun r ↦ (1 - delta) * linearRowMean q lowerWeight r)
    (fun _ ↦ delta) upperThreshold upperLambda hne hcomplete
    D R U pairX rowX cap hq0 hq1 hlower0 hlower1 hupper0 hupper1
    (fun _ ↦ hdelta0) hupperLambda hpairX0 hrowX0 hpairXcap hrowXcap
    hcap1 hconflictIncidence hlowerIncidence hupperIncidence hpair
  · intro r
    apply (Real.exp_le_exp.mpr ?_).trans (hlowerNumeric r)
    calc
      delta * ((1 - delta) * linearRowMean q lowerWeight r) +
          (Real.exp (-delta) - 1) * linearRowMean q lowerWeight r =
          (delta * (1 - delta) + (Real.exp (-delta) - 1)) *
            linearRowMean q lowerWeight r := by ring
      _ ≤ (delta * (1 - delta) + (Real.exp (-delta) - 1)) * eta :=
        mul_le_mul_of_nonpos_left (heta r) hcoefficient
  · exact hupper

end WeightedEdgeColoring.RankThreeOptionSystem
