import WeightedEdgeColoring.RankThreeDirectNibbleHarrisExtra

/-!
# Harris selection before conflict isolation

The direct nibble normally forbids every conflicting pair inside the local
lemma.  For the isolated nibble this is unnecessary: first choose a raw
Bernoulli set satisfying the quantitative row events, and only afterwards
delete every non-isolated option.  This file packages the raw Harris step.

There are three event families.  Lower linear rows are decreasing, upper
linear rows are increasing, and `Extra` is an arbitrary increasing family
(in the application, a quadratic bound on the weight lost to isolation).
No pair event occurs.  Consequently an increasing event pays only for the
overlapping lower rows, while a lower event pays only for upper and extra
events.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliHarris
open WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe w x y z

variable {Option : Type w} {LowerRow : Type x} {UpperRow : Type y}
  {Extra : Type z}
  [Fintype Option] [Fintype LowerRow] [Fintype UpperRow] [Fintype Extra]
  [DecidableEq Option] [DecidableEq LowerRow] [DecidableEq UpperRow]
  [DecidableEq Extra]

/-- Empty conflict lists let us reuse the support and incidence bookkeeping
of `RankThreeDirectNibbleHarrisExtra` without introducing pair events. -/
abbrev IsolatedRawBadIndex (LowerRow UpperRow Extra : Type*) :=
  DirectNibbleExtraBadIndex (Fin 0) LowerRow UpperRow Extra

def emptyOptionMap : Fin 0 → Option := fun i ↦ Fin.elim0 i

theorem emptyOptionMap_ne :
    ∀ i : Fin 0, (emptyOptionMap i : Option) ≠ emptyOptionMap i := by
  intro i
  exact Fin.elim0 i

/-- Positive mass of the raw avoidance event extracts a raw set satisfying
all lower, upper, and additional events.  No matching claim is made here;
the caller applies `isolatedOptions` afterwards. -/
theorem extract_raw_with_extra_of_positive
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold : LowerRow → ℝ) (upperThreshold : UpperRow → ℝ)
    (q : Option → ℝ)
    (extraSupport : Extra → Finset Option)
    (extraLocalBad : (a : Extra) → Finset (Finset (Inside (extraSupport a))))
    (hpositive : 0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun b ↦ insideCylinder
          (directNibbleExtraSupport
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight extraSupport b)
          (directNibbleExtraLocalBad
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight lowerThreshold upperThreshold
            emptyOptionMap_ne extraSupport extraLocalBad b))
        Finset.univ)) :
    ∃ S : Finset Option,
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) ∧
      (∀ a, (splitEquiv (extraSupport a) S).1 ∉ extraLocalBad a) := by
  let support := directNibbleExtraSupport
    (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight upperWeight
      extraSupport
  let localBad := directNibbleExtraLocalBad
    (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight upperWeight
      lowerThreshold upperThreshold emptyOptionMap_ne extraSupport extraLocalBad
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
  · intro r
    have hr := havoid (Sum.inl (Sum.inr (Sum.inl r)))
    simpa [support, localBad, directNibbleExtraSupport,
      directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
      lowerTail, not_le] using hr
  · intro r
    have hr := havoid (Sum.inl (Sum.inr (Sum.inr r)))
    simpa [support, localBad, directNibbleExtraSupport,
      directNibbleExtraLocalBad, directNibbleSupport, directNibbleLocalBad,
      upperTail, not_le] using hr
  · intro a
    have ha := havoid (Sum.inr a)
    simpa only [support, localBad, directNibbleExtraSupport,
      directNibbleExtraLocalBad, mem_insideCylinder] using ha

/-- Exact raw Harris theorem.  Its three numerical hypotheses are precisely
the lower linear, upper linear, and additional increasing event bounds. -/
theorem exists_raw_with_extra_increasing_harris
    (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold lowerLambda : LowerRow → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (extraSupport : Extra → Finset Option)
    (extraLocalBad : (a : Extra) → Finset (Finset (Inside (extraSupport a))))
    (hextraIncreasing : ∀ a, IsIncreasing (extraLocalBad a))
    (x : IsolatedRawBadIndex LowerRow UpperRow Extra → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hlowerLambda : ∀ r, 0 ≤ lowerLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b < 1)
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) * linearRowMean q lowerWeight r) ≤
        x (Sum.inl (Sum.inr (Sum.inl r))) *
          ∏ b ∈ directNibbleExtraNeighbor
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight extraSupport
            (Sum.inl (Sum.inr (Sum.inl r))), (1 - x b))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) * linearRowMean q upperWeight r) ≤
        x (Sum.inl (Sum.inr (Sum.inr r))) *
          ∏ b ∈ directNibbleExtraNeighbor
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight extraSupport
            (Sum.inl (Sum.inr (Sum.inr r))), (1 - x b))
    (hextra : ∀ a,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (extraSupport a)))
          (extraLocalBad a) ≤
        x (Sum.inr a) *
          ∏ b ∈ directNibbleExtraNeighbor
            (emptyOptionMap : Fin 0 → Option) emptyOptionMap
            lowerWeight upperWeight extraSupport (Sum.inr a), (1 - x b)) :
    ∃ S : Finset Option,
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) ∧
      (∀ a, (splitEquiv (extraSupport a) S).1 ∉ extraLocalBad a) := by
  let support := directNibbleExtraSupport
    (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight upperWeight
      extraSupport
  let localBad := directNibbleExtraLocalBad
    (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight upperWeight
      lowerThreshold upperThreshold emptyOptionMap_ne extraSupport extraLocalBad
  let polarity : IsolatedRawBadIndex LowerRow UpperRow Extra → Bool :=
    directNibbleExtraPolarity
  let neighbor := directNibbleExtraNeighbor
    (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight upperWeight
      extraSupport
  have hmonoLocal : ∀ b, HasPolarity (polarity b) (localBad b) := by
    intro b
    rcases b with b | a
    · exact directNibbleLocalBad_hasPolarity
        (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight
        upperWeight lowerThreshold upperThreshold emptyOptionMap_ne
        hlower0 hupper0 b
    · change IsIncreasing (extraLocalBad a)
      exact hextraIncreasing a
  have hmonoGlobal : ∀ b, HasPolarity (polarity b)
      (insideCylinder (support b) (localBad b)) := by
    intro b
    cases hb : polarity b
    · change IsDecreasing (insideCylinder (support b) (localBad b))
      exact WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isDecreasing
        (support b) (localBad b) (by
          simpa [HasPolarity, hb] using hmonoLocal b)
    · change IsIncreasing (insideCylinder (support b) (localBad b))
      exact WeightedEdgeColoring.FiniteBernoulliCylinderMonotone.insideCylinder_isIncreasing
        (support b) (localBad b) (by
          simpa [HasPolarity, hb] using hmonoLocal b)
  have hlocal : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (support b))) (localBad b) ≤
        x b * ∏ a ∈ neighbor b, (1 - x a) := by
    intro b
    rcases b with b | a
    · rcases b with c | r
      · exact Fin.elim0 c
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
    · exact hextra a
  have hpositive :=
    WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided.asymmetric_lopsided_local_lemma_of_polarity_support_canonical
        q support localBad polarity x hq0 hq1 hx0 hx1 hmonoLocal
        hmonoGlobal hlocal
  exact extract_raw_with_extra_of_positive lowerWeight upperWeight
    lowerThreshold upperThreshold q extraSupport extraLocalBad (by
      change 0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (WeightedEdgeColoring.FiniteLocalLemma.avoid
          (fun b ↦ insideCylinder (support b) (localBad b)) Finset.univ)
      exact hpositive)

/-- Incidence form of the raw Harris theorem.  Increasing events pay only
for lower-row incidence `R`; a lower row pays for upper and extra incidence.
There is no conflict-pair contribution. -/
theorem exists_raw_with_extra_increasing_harris_of_incidence
    (q : Option → ℝ)
    (lowerWeight : LowerRow → Option → ℝ)
    (upperWeight : UpperRow → Option → ℝ)
    (lowerThreshold lowerLambda : LowerRow → ℝ)
    (upperThreshold upperLambda : UpperRow → ℝ)
    (extraSupport : Extra → Finset Option)
    (extraLocalBad : (a : Extra) → Finset (Finset (Inside (extraSupport a))))
    (hextraIncreasing : ∀ a, IsIncreasing (extraLocalBad a))
    (R U E : ℕ) (lowerX upperX cap : ℝ) (extraX : Extra → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o)
    (hlower1 : ∀ r o, lowerWeight r o ≤ 1)
    (hupper0 : ∀ r o, 0 ≤ upperWeight r o)
    (hupper1 : ∀ r o, upperWeight r o ≤ 1)
    (hlowerLambda : ∀ r, 0 ≤ lowerLambda r)
    (hupperLambda : ∀ r, 0 ≤ upperLambda r)
    (hlowerX0 : 0 ≤ lowerX) (hupperX0 : 0 ≤ upperX)
    (hextraX0 : ∀ a, 0 ≤ extraX a)
    (hcap0 : 0 ≤ cap) (hupperXcap : upperX ≤ cap)
    (hextraXcap : ∀ a, extraX a ≤ cap)
    (hlowerX1 : lowerX < 1) (hcap1 : cap < 1)
    (hlowerIncidence : ∀ o,
      (linearRowIncidence lowerWeight o).card ≤ R)
    (hupperIncidence : ∀ o,
      (linearRowIncidence upperWeight o).card ≤ U)
    (hextraIncidence : ∀ o,
      (directNibbleExtraEventIncidence extraSupport o).card ≤ E)
    (hlower : ∀ r,
      Real.exp (lowerLambda r * lowerThreshold r +
        (Real.exp (-lowerLambda r) - 1) * linearRowMean q lowerWeight r) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport lowerWeight r).card * (U + E)))
    (hupper : ∀ r,
      Real.exp (-upperLambda r * upperThreshold r +
        (Real.exp (upperLambda r) - 1) * linearRowMean q upperWeight r) ≤
        upperX * (1 - lowerX) ^
          ((linearRowSupport upperWeight r).card * R))
    (hextra : ∀ a,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (extraSupport a)))
          (extraLocalBad a) ≤
        extraX a * (1 - lowerX) ^ ((extraSupport a).card * R)) :
    ∃ S : Finset Option,
      (∀ r, lowerThreshold r <
        weightedSum
          (fun o : Inside (linearRowSupport lowerWeight r) ↦ lowerWeight r o)
          (splitEquiv (linearRowSupport lowerWeight r) S).1) ∧
      (∀ r,
        weightedSum
          (fun o : Inside (linearRowSupport upperWeight r) ↦ upperWeight r o)
          (splitEquiv (linearRowSupport upperWeight r) S).1 <
        upperThreshold r) ∧
      (∀ a, (splitEquiv (extraSupport a) S).1 ∉ extraLocalBad a) := by
  let x : IsolatedRawBadIndex LowerRow UpperRow Extra → ℝ :=
    directNibbleExtraLLLWeight 0 lowerX upperX extraX
  have hx0 : ∀ b, 0 ≤ x b := by
    intro b
    rcases b with b | a
    · rcases b with c | r
      · exact le_rfl
      · rcases r with r | r
        · exact hlowerX0
        · exact hupperX0
    · exact hextraX0 a
  have hx1 : ∀ b, x b < 1 := by
    intro b
    rcases b with b | a
    · rcases b with c | r
      · exact Fin.elim0 c
      · rcases r with r | r
        · exact hlowerX1
        · exact hupperXcap.trans_lt hcap1
    · exact (hextraXcap a).trans_lt hcap1
  apply exists_raw_with_extra_increasing_harris q lowerWeight upperWeight
    lowerThreshold lowerLambda upperThreshold upperLambda extraSupport
    extraLocalBad hextraIncreasing x hq0 hq1 hlower0 hlower1 hupper0
    hupper1 hlowerLambda hupperLambda hx0 hx1
  · intro r
    apply (hlower r).trans
    apply mul_le_mul_of_nonneg_left _ hlowerX0
    simpa [Nat.zero_add] using
      (directNibbleExtra_lower_product_lower_bound_of_incidence
        (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight
        upperWeight extraSupport 0 lowerX upperX cap extraX 0 U E hcap0
        hcap1.le hcap0 hupperXcap hextraXcap
        (fun o ↦ by simp [optionConflictIncidence]) hupperIncidence
        hextraIncidence r)
  · intro r
    apply (hupper r).trans
    apply mul_le_mul_of_nonneg_left _ hupperX0
    exact directNibbleExtra_upper_product_lower_bound
      (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight
      upperWeight extraSupport 0 lowerX upperX extraX R hlowerX0
      hlowerX1.le hlowerIncidence r
  · intro a
    apply (hextra a).trans
    apply mul_le_mul_of_nonneg_left _ (hextraX0 a)
    exact directNibbleExtra_event_product_lower_bound
      (emptyOptionMap : Fin 0 → Option) emptyOptionMap lowerWeight
      upperWeight extraSupport 0 lowerX upperX extraX R hlowerX0
      hlowerX1.le hlowerIncidence a

end WeightedEdgeColoring.RankThreeOptionSystem
