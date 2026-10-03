import WeightedEdgeColoring.RankThreeIsolatedRawRound
import WeightedEdgeColoring.RankThreeSharpFixedSlackRound

/-!
# A sharp fixed-slack round using raw sampling and isolation

Pair-conflict events are omitted from the local lemma.  A raw Bernoulli set
is chosen subject to lower rows, upper rows, one quadratic isolation-loss
event per lower row, and the existing slot-collision events.  The output is
the set of isolated raw options.

The theorem keeps the isolation-loss thresholds and row-weight envelopes
explicit.  This is useful for slot rows: their total coefficient sum retains
the factor `1/(3*lambda)`, so the quadratic mean is of order
`a^2*d/lambda` rather than `a^2*d`.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliHarris
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

abbrev IsolatedSharpLowerRow := H.ActiveSlotLowerRow (Group := Group) 0

abbrev IsolatedSharpExtra := H.IsolatedSharpLowerRow (Group := Group) ⊕ Slot

/-- Supports of the two increasing quadratic families. -/
noncomputable def isolatedSharpExtraSupport
    (lowerWeight : H.IsolatedSharpLowerRow (Group := Group) → Option → ℝ) :
    H.IsolatedSharpExtra (Group := Group) → Finset Option
  | Sum.inl r => H.isolatedRowConflictSupport lowerWeight r
  | Sum.inr s => H.slotCollisionSupport s

/-- Isolation-loss events on the left and residual slot-collision events on
the right. -/
noncomputable def isolatedSharpExtraLocalBad
    (lowerWeight : H.IsolatedSharpLowerRow (Group := Group) → Option → ℝ)
    (lossThreshold : H.IsolatedSharpLowerRow (Group := Group) → ℝ)
    (collisionThreshold : Slot → ℝ) :
    (e : H.IsolatedSharpExtra (Group := Group)) →
      Finset (Finset (Inside (H.isolatedSharpExtraSupport lowerWeight e)))
  | Sum.inl r => H.isolatedRowConflictLocalBad lowerWeight r (lossThreshold r)
  | Sum.inr s => H.slotCollisionLocalBad s (collisionThreshold s)

/-- The extra-family incidence splits into isolation-loss incidence and
slot-collision incidence. -/
theorem isolatedSharpExtraIncidence_card
    (lowerWeight : H.IsolatedSharpLowerRow (Group := Group) → Option → ℝ)
    (o : Option) :
    (directNibbleExtraEventIncidence
      (H.isolatedSharpExtraSupport lowerWeight) o).card =
      (H.isolatedRowConflictIncidence lowerWeight o).card +
        (H.slotCollisionIncidence o).card := by
  have hset : directNibbleExtraEventIncidence
      (H.isolatedSharpExtraSupport lowerWeight) o =
      (H.isolatedRowConflictIncidence lowerWeight o).disjSum
        (H.slotCollisionIncidence o) := by
    ext e
    rcases e with r | s
    · simp [directNibbleExtraEventIncidence,
        isolatedSharpExtraSupport, isolatedRowConflictIncidence]
    · simp [directNibbleExtraEventIncidence,
        isolatedSharpExtraSupport, slotCollisionIncidence]
  rw [hset, Finset.card_disjSum]

/-- Under degree `D`, enlarging each lower row by conflict neighbours and
adding all slot-collision supports gives the displayed explicit incidence. -/
theorem isolatedSharpExtraIncidence_card_le
    (members : Group → Finset Job) (lambda D R : ℕ) (hlambda : 0 < lambda)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (o : Option) :
    (directNibbleExtraEventIncidence
      (H.isolatedSharpExtraSupport
        (H.activeSlotLowerWeight members lambda 0)) o).card ≤
      (3 * D + 1) * (R + 8 * D) + 8 * D := by
  rw [H.isolatedSharpExtraIncidence_card]
  exact Nat.add_le_add
    (H.isolatedRowConflictIncidence_card_le
      (H.activeSlotLowerWeight members lambda 0)
      (R + 8 * D) (3 * D)
      (H.activeSlotLowerWeight_incidence_card_le
        members lambda 0 D R hjobDegree hslotDegree hgroupIncidence)
      (H.conflictNeighbors_card_le_three_mul D hjobDegree hslotDegree) o)
    (H.slotCollisionIncidence_card_le_eight_mul
      lambda D hlambda hjobDegree hslotDegree o)

/-- All extra events used in the isolated sharp round are increasing. -/
theorem isolatedSharpExtraLocalBad_isIncreasing
    (lowerWeight : H.IsolatedSharpLowerRow (Group := Group) → Option → ℝ)
    (lossThreshold : H.IsolatedSharpLowerRow (Group := Group) → ℝ)
    (collisionThreshold : Slot → ℝ)
    (hlower0 : ∀ r o, 0 ≤ lowerWeight r o) :
    ∀ e, IsIncreasing
      (H.isolatedSharpExtraLocalBad lowerWeight lossThreshold
        collisionThreshold e) := by
  intro e
  rcases e with r | s
  · exact H.isolatedRowConflictLocalBad_isIncreasing
      lowerWeight hlower0 r (lossThreshold r)
  · exact H.slotCollisionLocalBad_isIncreasing s (collisionThreshold s)

/-- In the uniform degree-`D` regime, a normalized slot lower row has total
coefficient sum at most `D^2/lambda`. -/
theorem sum_residualDeleteWeight_slot_le_sq_div
    (lambda D : ℕ) (hlambda : 0 < lambda)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) (s : Slot) :
    (∑ o : Option, H.residualDeleteWeight lambda (Sum.inr s) o) ≤
      (D : ℝ) ^ 2 / lambda := by
  have h := H.sum_residualDeleteWeight_slot_le_job_slot
    lambda D D hlambda s hjobDegree hslotDegree
  calc
    (∑ o : Option, H.residualDeleteWeight lambda (Sum.inr s) o) ≤
        (H.slotDegree s : ℝ) * ((D + 2 * D : ℕ) : ℝ) /
          ((3 * lambda : ℕ) : ℝ) := h
    _ ≤ (D : ℝ) * ((3 * D : ℕ) : ℝ) /
          ((3 * lambda : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · gcongr
        · exact_mod_cast hslotDegree s
        · omega
      · positivity
    _ = (D : ℝ) ^ 2 / lambda := by
      have hlambdaR : (lambda : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp <;> ring

/-- Ordinary arithmetic form of the slot isolation-loss envelope.  The last
summand is the explicit `24*k^2*lambda` condition requested by the outer
parameter choice. -/
theorem isolatedSlotWeightedEnvelope_le_half
    (a eta : ℝ) (d lambda k : ℕ)
    (hd : 0 < d) (hlambda : 0 < lambda)
    (ha0 : 0 ≤ a)
    (hscaled :
      18 * a ^ 2 * d + 72 * a * k * lambda + 24 * k ^ 2 * lambda ≤
        eta * d) :
    isolatedRowConflictWeightedMomentEnvelope
        (a / d) ((d : ℝ) ^ 2 / lambda) (3 * d) k ≤
      (eta * d / (3 * lambda : ℕ)) / 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlambdaR : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have hidentity :
      isolatedRowConflictWeightedMomentEnvelope
          (a / d) ((d : ℝ) ^ 2 / lambda) (3 * d) k =
        (3 * a ^ 2 * d + 12 * a * k * lambda + 4 * k ^ 2 * lambda) /
          lambda := by
    unfold isolatedRowConflictWeightedMomentEnvelope
    push_cast
    field_simp
    ring
  rw [hidentity]
  have hden : (0 : ℝ) < 6 * lambda := by positivity
  have hscaled' :
      6 * (3 * a ^ 2 * d + 12 * a * k * lambda +
        4 * k ^ 2 * lambda) ≤ eta * d := by
    nlinarith
  calc
    (3 * a ^ 2 * d + 12 * a * k * lambda + 4 * k ^ 2 * lambda) /
        lambda =
      (6 * (3 * a ^ 2 * d + 12 * a * k * lambda +
        4 * k ^ 2 * lambda)) / (6 * lambda) := by
          field_simp <;> ring
    _ ≤ (eta * d) / (6 * lambda) :=
      (div_le_div_iff_of_pos_right hden).2 hscaled'
    _ = (eta * d / (3 * lambda : ℕ)) / 2 := by
      push_cast
      field_simp <;> ring

/-- Natural isolation-loss margins: arbitrary for endpoint groups and
`etaIsolation*d/(3*lambda)` for normalized slot rows. -/
noncomputable def isolatedSharpLossThreshold
    (groupLoss : Group → ℝ) (etaIsolation : ℝ) (lambda d : ℕ) :
    H.IsolatedSharpLowerRow (Group := Group) → ℝ
  | Sum.inl g => groupLoss g
  | Sum.inr _ => etaIsolation * d / (3 * lambda : ℕ)

/-- Natural total-row-weight envelopes. -/
noncomputable def isolatedSharpLossWeightSum
    (K D lambda : ℕ) :
    H.IsolatedSharpLowerRow (Group := Group) → ℝ
  | Sum.inl _ => K * D
  | Sum.inr _ => (D : ℝ) ^ 2 / lambda

/-- The natural total-row-weight envelopes follow from the standard support
and degree bounds. -/
theorem activeSlotLowerWeight_sum_le_isolatedSharpLossWeightSum
    (members : Group → Finset Job) (lambda K D : ℕ)
    (hlambda : 0 < lambda)
    (hmembers : ∀ g, (members g).card ≤ K)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D) :
    ∀ r,
      (∑ o : Option, H.activeSlotLowerWeight members lambda 0 r o) ≤
        H.isolatedSharpLossWeightSum (Group := Group) K D lambda r := by
  intro r
  rcases r with g | s
  · have hsum := sum_weight_le_linearRowSupport_card
      (H.activeSlotLowerWeight members lambda 0) (Sum.inl g)
      (fun o ↦ H.jobGroupCoverageWeight_nonneg members g o)
      (fun o ↦ H.jobGroupCoverageWeight_le_one members g o)
    have hcard := H.jobGroupCoverage_support_card_le
      members K D hmembers hjobDegree g
    have hcardR :
        ((linearRowSupport (H.jobGroupCoverageWeight members) g).card : ℝ) ≤
          K * D := by
      exact_mod_cast hcard
    exact hsum.trans (by
      simpa [activeSlotLowerWeight, isolatedSharpLossWeightSum] using hcardR)
  · exact H.sum_residualDeleteWeight_slot_le_sq_div
      lambda D hlambda hjobDegree hslotDegree s.1

/-- Exact one-round theorem with no pair-conflict events.  Its lower numeric
hypothesis uses the raw threshold `target + lossThreshold`.  The isolation
loss is discharged by the weight-sensitive quadratic moment envelope. -/
theorem exists_isolatedSharpFixedSlackRound
    (q : Option → ℝ) (qmax : ℝ)
    (members : Group → Finset Job)
    (groupThreshold groupLambda : Group → ℝ)
    (slotLambda : Slot → ℝ) (jobLambda : Job → ℝ)
    (lossThreshold : H.IsolatedSharpLowerRow (Group := Group) → ℝ)
    (lossWeightSum : H.IsolatedSharpLowerRow (Group := Group) → ℝ)
    (lossX : H.IsolatedSharpLowerRow (Group := Group) → ℝ)
    (collisionX : Slot → ℝ)
    (lambda d D R k : ℕ)
    (a gamma etaJob etaLoad etaCollision : ℝ)
    (lowerX upperX cap : ℝ)
    (hlambda : 0 < lambda)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ o, q o ≤ qmax)
    (hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j)
    (hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ D)
    (hslotDegree : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter
        (fun g ↦ j ∈ members g)).card ≤ R)
    (hgroupLambda : ∀ g, 0 ≤ groupLambda g)
    (hslotLambda : ∀ s, 0 ≤ slotLambda s)
    (hjobLambda : ∀ j, 0 ≤ jobLambda j)
    (hlowerX0 : 0 ≤ lowerX) (hupperX0 : 0 ≤ upperX)
    (hcap0 : 0 ≤ cap) (hupperXcap : upperX ≤ cap)
    (hlossX0 : ∀ r, 0 ≤ lossX r) (hlossXcap : ∀ r, lossX r ≤ cap)
    (hcollisionX0 : ∀ s, 0 ≤ collisionX s)
    (hcollisionXcap : ∀ s, collisionX s ≤ cap)
    (hlowerX1 : lowerX < 1) (hcap1 : cap < 1)
    (hlossThreshold : ∀ r, 0 < lossThreshold r)
    (hlossWeightSum : ∀ r,
      (∑ o : Option,
        H.activeSlotLowerWeight members lambda 0 r o) ≤ lossWeightSum r)
    (hlossEnvelope : ∀ r,
      isolatedRowConflictWeightedMomentEnvelope qmax (lossWeightSum r)
          (3 * D) k ≤ lossThreshold r / 2)
    (hlossProduct : ∀ r,
      (1 / 2 : ℝ) ^ k ≤ lossX r * (1 - lowerX) ^
        ((H.isolatedRowConflictSupport
          (H.activeSlotLowerWeight members lambda 0) r).card * (R + 8 * D)))
    (hgroupLowerNumeric : ∀ g,
      Real.exp (groupLambda g *
          (groupThreshold g + lossThreshold (Sum.inl g)) +
        (Real.exp (-groupLambda g) - 1) *
          linearRowMean q (H.jobGroupCoverageWeight members) g) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport
            (H.jobGroupCoverageWeight members) g).card *
              (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D))))
    (hslotLowerNumeric : ∀ s : H.ActiveSlot 0,
      Real.exp (slotLambda s.1 *
          (((a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
              (3 * lambda : ℕ)) + lossThreshold (Sum.inr s)) +
        (Real.exp (-slotLambda s.1) - 1) *
          linearRowMean q (H.residualDeleteWeight lambda) (Sum.inr s.1)) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inr s.1)).card *
              (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D))))
    (hjobUpperNumeric : ∀ j,
      Real.exp (-jobLambda j *
          ((2 * a * (1 - gamma) + etaJob) * d / (2 * lambda : ℕ)) +
        (Real.exp (jobLambda j) - 1) *
          linearRowMean q (H.residualDeleteWeight lambda) (Sum.inl j)) ≤
        upperX * (1 - lowerX) ^
          ((linearRowSupport (H.residualDeleteWeight lambda)
            (Sum.inl j)).card * (R + 8 * D)))
    (hcollisionNumeric : ∀ s,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (H.slotCollisionSupport s)))
          (H.slotCollisionLocalBad s (2 * etaCollision * d)) ≤
        collisionX s * (1 - lowerX) ^
          ((H.slotCollisionSupport s).card * (R + 8 * D))) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g, groupThreshold g <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention a gamma - etaJob) * d ≤
          H.residualJobDegree A j) ∧
      (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
        (H.residualSlotDegree A s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) +
            etaLoad + etaCollision) * d) := by
  let lowerWeight := H.activeSlotLowerWeight members lambda 0
  let upperWeight := H.residualJobUpperWeight lambda
  let target := H.sharpFixedSlackLowerThreshold
    groupThreshold lambda d a gamma etaLoad
  let lowerLambda := H.sharpFixedSlackLowerLambda groupLambda slotLambda
  let upperThreshold : Job → ℝ := sharpFixedSlackJobThreshold
    lambda d a gamma etaJob
  let extraSupport := H.isolatedSharpExtraSupport lowerWeight
  let extraLocalBad := H.isolatedSharpExtraLocalBad lowerWeight lossThreshold
    (fun _s ↦ 2 * etaCollision * d)
  let extraX : H.IsolatedSharpExtra (Group := Group) → ℝ
    | Sum.inl r => lossX r
    | Sum.inr s => collisionX s
  have hlower0 := H.activeSlotLowerWeight_nonneg members lambda 0
  have hlower1 := H.activeSlotLowerWeight_le_one members lambda 0 hlambda
    hjobSlot hslotPair
  have hupper0 := H.residualJobUpperWeight_nonneg lambda
  have hupper1 := H.residualJobUpperWeight_le_one lambda hlambda
    hjobSlot hslotPair
  have hlowerLambda : ∀ r, 0 ≤ lowerLambda r := by
    intro r
    rcases r with g | s
    · exact hgroupLambda g
    · exact hslotLambda s.1
  have hextraIncreasing : ∀ e, IsIncreasing (extraLocalBad e) := by
    exact H.isolatedSharpExtraLocalBad_isIncreasing lowerWeight lossThreshold
      (fun _s ↦ 2 * etaCollision * d) hlower0
  have hextraX0 : ∀ e, 0 ≤ extraX e := by
    intro e
    rcases e with r | s
    · exact hlossX0 r
    · exact hcollisionX0 s
  have hextraXcap : ∀ e, extraX e ≤ cap := by
    intro e
    rcases e with r | s
    · exact hlossXcap r
    · exact hcollisionXcap s
  have hlowerNumeric : ∀ r,
      Real.exp (lowerLambda r * (target r + lossThreshold r) +
        (Real.exp (-lowerLambda r) - 1) *
          linearRowMean q lowerWeight r) ≤
        lowerX * (1 - cap) ^
          ((linearRowSupport lowerWeight r).card *
            (2 * D + ((3 * D + 1) * (R + 8 * D) + 8 * D))) := by
    intro r
    rcases r with g | s
    · simpa [lowerWeight, target, lowerLambda,
        sharpFixedSlackLowerThreshold, sharpFixedSlackLowerLambda] using
        hgroupLowerNumeric g
    · simpa [lowerWeight, target, lowerLambda,
        sharpFixedSlackLowerThreshold, sharpFixedSlackLowerLambda] using
        hslotLowerNumeric s
  have hupperNumeric : ∀ j,
      Real.exp (-jobLambda j * upperThreshold j +
        (Real.exp (jobLambda j) - 1) * linearRowMean q upperWeight j) ≤
        upperX * (1 - lowerX) ^
          ((linearRowSupport upperWeight j).card * (R + 8 * D)) := by
    intro j
    simpa [upperWeight, upperThreshold, sharpFixedSlackJobThreshold] using
      hjobUpperNumeric j
  have hextraNumeric : ∀ e,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (extraSupport e)))
          (extraLocalBad e) ≤
        extraX e * (1 - lowerX) ^ ((extraSupport e).card * (R + 8 * D)) := by
    intro e
    rcases e with r | s
    · apply (H.isolatedRowConflictLocalBad_mass_le_half_pow_weightSum
          q qmax lowerWeight r (3 * D) k (lossWeightSum r)
          (lossThreshold r) hq0 hq1 hqmax0 hqmax
          (hlower0 r) (hlower1 r) (hlossWeightSum r)
          (H.conflictNeighbors_card_le_three_mul D hjobDegree hslotDegree)
          (hlossThreshold r) (hlossEnvelope r)).trans
      simpa [extraX, extraSupport, isolatedSharpExtraSupport] using
        hlossProduct r
    · simpa [extraX, extraSupport, extraLocalBad,
        isolatedSharpExtraSupport, isolatedSharpExtraLocalBad] using
        hcollisionNumeric s
  rcases exists_raw_with_extra_increasing_harris_of_incidence
      q lowerWeight upperWeight
      (fun r ↦ target r + lossThreshold r) lowerLambda
      upperThreshold jobLambda extraSupport extraLocalBad hextraIncreasing
      (R + 8 * D) (2 * D)
      ((3 * D + 1) * (R + 8 * D) + 8 * D)
      lowerX upperX cap extraX hq0 hq1 hlower0 hlower1 hupper0 hupper1
      hlowerLambda hjobLambda hlowerX0 hupperX0 hextraX0 hcap0
      hupperXcap hextraXcap hlowerX1 hcap1
      (H.activeSlotLowerWeight_incidence_card_le
        members lambda 0 D R hjobDegree hslotDegree hgroupIncidence)
      (H.residualJobUpperWeight_incidence_card_le_slot lambda D hslotDegree)
      (H.isolatedSharpExtraIncidence_card_le members lambda D R hlambda
        hjobDegree hslotDegree hgroupIncidence)
      hlowerNumeric hupperNumeric hextraNumeric with
    ⟨B, hrawLower, hrawUpper, hgoodExtra⟩
  let A := H.isolatedOptions B
  have hmatching : H.IsPartialMatching A := H.isolatedOptions_isPartialMatching B
  have hgoodLoss : ∀ r,
      (splitEquiv (H.isolatedRowConflictSupport lowerWeight r) B).1 ∉
        H.isolatedRowConflictLocalBad lowerWeight r (lossThreshold r) := by
    intro r
    simpa [extraSupport, extraLocalBad, isolatedSharpExtraSupport,
      isolatedSharpExtraLocalBad] using hgoodExtra (Sum.inl r)
  have hlower : ∀ r, target r < weightedSum (lowerWeight r) A := by
    intro r
    apply H.target_lt_isolated_weightedSum_of_raw_and_not_localBad
      lowerWeight hlower0 r B (target r) (lossThreshold r)
    · rw [← weightedSum_linearRowSupport_eq_global_raw lowerWeight r B]
      exact hrawLower r
    · exact hgoodLoss r
  have hupper : ∀ j, weightedSum (upperWeight j) A < upperThreshold j := by
    intro j
    apply (H.isolated_weightedSum_le_raw (upperWeight j) (hupper0 j) B).trans_lt
    rw [← weightedSum_linearRowSupport_eq_global_raw upperWeight j B]
    exact hrawUpper j
  have hgroup : ∀ g, groupThreshold g <
      ∑ o ∈ A, H.jobGroupCoverageWeight members g o := by
    intro g
    have h := hlower (Sum.inl g)
    simpa [A, lowerWeight, target, sharpFixedSlackLowerThreshold,
      weightedSum] using h
  have hjobLoss : ∀ j, ¬ H.Covers A j →
      ((H.removedResidualFiber ∅ A j).card : ℝ) ≤
        (2 * a * (1 - gamma) + etaJob) * d := by
    intro j huncovered
    have h := hupper j
    change (∑ o ∈ A, H.residualDeleteWeight lambda (Sum.inl j) o) <
      (2 * a * (1 - gamma) + etaJob) * d / (2 * lambda : ℕ) at h
    rw [H.selected_residualDeleteWeight_job lambda A j] at h
    have hden : (0 : ℝ) < (2 * lambda : ℕ) := by positivity
    have hload : (H.externalJobDeletionLoad A j : ℝ) <
        (2 * a * (1 - gamma) + etaJob) * d :=
      (div_lt_div_iff_of_pos_right hden).mp h
    have hremoved := H.removedResidualFiber_empty_card_le_externalJobDeletionLoad
      A j huncovered
    have hremovedR : ((H.removedResidualFiber ∅ A j).card : ℝ) ≤
        H.externalJobDeletionLoad A j := by
      exact_mod_cast hremoved
    exact hremovedR.trans hload.le
  have hslotLoad : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (a * (2 - gamma) * (1 - gamma) - etaLoad) * d ≤
        (H.slotDeletionLoad A s : ℝ) := by
    intro s hunused
    let active : H.ActiveSlot 0 := ⟨s, Nat.zero_le _⟩
    have h := hlower (Sum.inr active)
    change (a * (2 - gamma) * (1 - gamma) - etaLoad) * d /
        (3 * lambda : ℕ) <
      ∑ o ∈ A, H.residualDeleteWeight lambda (Sum.inr s) o at h
    rw [H.selected_residualDeleteWeight_slot lambda A s hunused] at h
    have hden : (0 : ℝ) < (3 * lambda : ℕ) := by positivity
    exact ((div_lt_div_iff_of_pos_right hden).mp h).le
  have hgoodCollision : ∀ s,
      (splitEquiv (H.slotCollisionSupport s) B).1 ∉
        H.slotCollisionLocalBad s (2 * etaCollision * d) := by
    intro s
    simpa [extraSupport, extraLocalBad, isolatedSharpExtraSupport,
      isolatedSharpExtraLocalBad] using hgoodExtra (Sum.inr s)
  have hslotCollision : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (WeightedEdgeColoring.collisionDeficit A (H.slotBlockedBy s) : ℝ) ≤
        etaCollision * d := by
    intro s hunused
    have hBglobal : (pairCollisionStatistic
        (H.avoidingSlotBlockedBy s) B : ℝ) < 2 * etaCollision * d := by
      have hnot := hgoodCollision s
      have hlocal : H.slotCollisionLocalStatistic s
          (splitEquiv (H.slotCollisionSupport s) B).1 <
            2 * etaCollision * d := by
        simpa [slotCollisionLocalBad, upperTail, not_le] using hnot
      unfold slotCollisionLocalStatistic at hlocal
      rw [zeroOutside_inside_eq_inter (H.slotCollisionSupport s) B,
        H.pairCollisionStatistic_inter_slotCollisionSupport B s] at hlocal
      exact hlocal
    have hAB : A ⊆ B := H.isolatedOptions_subset B
    have hmono := pairCollisionStatistic_mono
      (H.avoidingSlotBlockedBy s) hAB
    have htwo := two_mul_collisionDeficit_le_pairCollisionStatistic
      A (H.avoidingSlotBlockedBy s)
    have htwoReal : (2 : ℝ) *
        collisionDeficit A (H.avoidingSlotBlockedBy s) ≤
          pairCollisionStatistic (H.avoidingSlotBlockedBy s) A := by
      exact_mod_cast htwo
    rw [H.collisionDeficit_avoidingSlotBlockedBy_eq A s hunused] at htwoReal
    have hmonoReal : (pairCollisionStatistic
        (H.avoidingSlotBlockedBy s) A : ℝ) ≤
          pairCollisionStatistic (H.avoidingSlotBlockedBy s) B := by
      exact_mod_cast hmono
    nlinarith
  have hbalance := H.separatedFixedSlack_balance A d a gamma etaJob etaLoad
    etaCollision hjobInitial hjobLoss hslotInitial hslotLoad hslotCollision
  exact ⟨A, hmatching, hgroup, hbalance.1, hbalance.2⟩

end WeightedEdgeColoring.RankThreeOptionSystem
