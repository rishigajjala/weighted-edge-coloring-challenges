import WeightedEdgeColoring.RankThreeDirectBernoulliLLL
import WeightedEdgeColoring.RankThreeLinearResidual
import WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided

/-!
# Direct Bernoulli LLL with coverage and deletion rows

The bad events are listed conflicting pairs, lower tails of coverage rows,
and upper tails of deletion rows.  Thus the selected options already form a
partial matching, while all quantitative events remain linear Bernoulli sums.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit
open WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided

universe u v w x y

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  {Cover : Type x} {Delete : Type y}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [Fintype Cover] [Fintype Delete]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  [DecidableEq Cover] [DecidableEq Delete]
  (H : RankThreeOptionSystem Job Slot Option)

variable {Conflict : Type*} [Fintype Conflict] [DecidableEq Conflict]
variable (left right : Conflict → Option)

abbrev MixedBadIndex (Conflict Cover Delete : Type*) :=
  Conflict ⊕ (Cover ⊕ Delete)

noncomputable def weightedRowSupport (weight : Delete → Option → ℝ)
    (r : Delete) : Finset Option :=
  Finset.univ.filter fun o ↦ weight r o ≠ 0

noncomputable def deletionRowLocalBad
    (weight : Delete → Option → ℝ) (threshold : Delete → ℝ)
    (r : Delete) :
    Finset (Finset (Inside (weightedRowSupport weight r))) :=
  upperTail
    (weightedSum (fun o : Inside (weightedRowSupport weight r) ↦ weight r o))
    (threshold r)

noncomputable def mixedBadSupport
    (coverWeight : Cover → Option → ℝ)
    (deleteWeight : Delete → Option → ℝ) :
    MixedBadIndex Conflict Cover Delete → Finset Option
  | Sum.inl c => conflictPairSupport left right c
  | Sum.inr (Sum.inl g) => coverageGroupSupport coverWeight g
  | Sum.inr (Sum.inr r) => weightedRowSupport deleteWeight r

noncomputable def mixedLocalBad
    (coverWeight : Cover → Option → ℝ) (coverThreshold : Cover → ℝ)
    (deleteWeight : Delete → Option → ℝ) (deleteThreshold : Delete → ℝ)
    (hne : ∀ c, left c ≠ right c) :
    (b : MixedBadIndex Conflict Cover Delete) →
      Finset (Finset (Inside
        (mixedBadSupport left right coverWeight deleteWeight b)))
  | Sum.inl c => conflictPairLocalBad left right hne c
  | Sum.inr (Sum.inl g) => coverageGroupLocalBad coverWeight coverThreshold g
  | Sum.inr (Sum.inr r) => deletionRowLocalBad deleteWeight deleteThreshold r

noncomputable def mixedBadNeighbor
    (coverWeight : Cover → Option → ℝ)
    (deleteWeight : Delete → Option → ℝ)
    (b : MixedBadIndex Conflict Cover Delete) :
    Finset (MixedBadIndex Conflict Cover Delete) :=
  Finset.univ.filter fun a ↦ a ≠ b ∧
    ¬Disjoint (mixedBadSupport left right coverWeight deleteWeight b)
      (mixedBadSupport left right coverWeight deleteWeight a)

/-- Pair and deletion upper-tail events are increasing; coverage lower-tail
events are decreasing. -/
def mixedBadPolarity : MixedBadIndex Conflict Cover Delete → Bool
  | Sum.inl _ => true
  | Sum.inr (Sum.inl _) => false
  | Sum.inr (Sum.inr _) => true

/-- Sharp monotone lopsided neighborhood: only overlapping events of the
opposite polarity are adjacent. -/
noncomputable def mixedCrossPolarityNeighbor
    (coverWeight : Cover → Option → ℝ)
    (deleteWeight : Delete → Option → ℝ)
    (b : MixedBadIndex Conflict Cover Delete) :
    Finset (MixedBadIndex Conflict Cover Delete) :=
  Finset.univ.filter fun a ↦ a ≠ b ∧
    mixedBadPolarity a ≠ mixedBadPolarity b ∧
    ¬Disjoint (mixedBadSupport left right coverWeight deleteWeight b)
      (mixedBadSupport left right coverWeight deleteWeight a)

theorem mixedCrossPolarityNeighbor_iff
    (coverWeight : Cover → Option → ℝ)
    (deleteWeight : Delete → Option → ℝ)
    (b a : MixedBadIndex Conflict Cover Delete) (hne : a ≠ b)
    (hpol : mixedBadPolarity a ≠ mixedBadPolarity b) :
    (¬Disjoint (mixedBadSupport left right coverWeight deleteWeight b)
        (mixedBadSupport left right coverWeight deleteWeight a) ↔
      a ∈ mixedCrossPolarityNeighbor left right coverWeight deleteWeight b) := by
  simp [mixedCrossPolarityNeighbor, hne, hpol]

/-- The support-refined mixed-monotone LLL specialized to the three direct
bad-event kinds. The two monotonicity premises are separated so applications
can discharge them with the elementary weighted-sum lemmas appropriate to
their concrete rows. -/
theorem mixed_avoid_positive_cross_polarity
    (q : Option → ℝ)
    (coverWeight : Cover → Option → ℝ) (coverThreshold : Cover → ℝ)
    (deleteWeight : Delete → Option → ℝ) (deleteThreshold : Delete → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (z : MixedBadIndex Conflict Cover Delete → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hz0 : ∀ b, 0 ≤ z b) (hz1 : ∀ b, z b < 1)
    (hmonoLocal : ∀ b, HasPolarity (mixedBadPolarity b)
      (mixedLocalBad left right coverWeight coverThreshold
        deleteWeight deleteThreshold hne b))
    (hmonoGlobal : ∀ b, HasPolarity (mixedBadPolarity b)
      (insideCylinder (mixedBadSupport left right coverWeight deleteWeight b)
        (mixedLocalBad left right coverWeight coverThreshold
          deleteWeight deleteThreshold hne b)))
    (hmass : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass (insideParameter q
          (mixedBadSupport left right coverWeight deleteWeight b)))
        (mixedLocalBad left right coverWeight coverThreshold
          deleteWeight deleteThreshold hne b) ≤
      z b * ∏ a ∈ mixedCrossPolarityNeighbor left right coverWeight
        deleteWeight b, (1 - z a)) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun b ↦ insideCylinder
          (mixedBadSupport left right coverWeight deleteWeight b)
          (mixedLocalBad left right coverWeight coverThreshold
            deleteWeight deleteThreshold hne b)) Finset.univ) := by
  apply asymmetric_lopsided_local_lemma_of_polarity_support
    q (mixedBadSupport left right coverWeight deleteWeight)
    (mixedLocalBad left right coverWeight coverThreshold
      deleteWeight deleteThreshold hne)
    mixedBadPolarity
    (mixedCrossPolarityNeighbor left right coverWeight deleteWeight)
    z hq0 hq1 hz0 hz1 hmonoLocal hmonoGlobal
  · intro b a hne' hpol
    exact mixedCrossPolarityNeighbor_iff left right coverWeight deleteWeight
      b a hne' hpol
  · exact hmass

theorem mixedBadNeighbor_nonneighbor_disjoint
    (coverWeight : Cover → Option → ℝ)
    (deleteWeight : Delete → Option → ℝ)
    (b a : MixedBadIndex Conflict Cover Delete)
    (ha : a ∉ insert b
      (mixedBadNeighbor left right coverWeight deleteWeight b)) :
    Disjoint (mixedBadSupport left right coverWeight deleteWeight b)
      (mixedBadSupport left right coverWeight deleteWeight a) := by
  by_contra hdisj
  have hab : a ≠ b := by
    intro h
    subst a
    exact ha (Finset.mem_insert_self b _)
  apply ha
  apply Finset.mem_insert_of_mem
  simp [mixedBadNeighbor, hab, hdisj]

theorem deletionRowLocalBad_mass_le
    (q : Option → ℝ) (weight : Delete → Option → ℝ)
    (threshold lambda : Delete → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hw0 : ∀ r o, 0 ≤ weight r o) (hw1 : ∀ r o, weight r o ≤ 1)
    (hlambda : ∀ r, 0 ≤ lambda r) (r : Delete) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass (insideParameter q (weightedRowSupport weight r)))
        (deletionRowLocalBad weight threshold r) ≤
      Real.exp (-lambda r * threshold r + (Real.exp (lambda r) - 1) *
        mean (insideParameter q (weightedRowSupport weight r))
          (fun o : Inside (weightedRowSupport weight r) ↦ weight r o)) := by
  exact bernoulli_upperTail_le
    (insideParameter q (weightedRowSupport weight r))
    (fun o : Inside (weightedRowSupport weight r) ↦ weight r o)
    (threshold r) (lambda r)
    (fun o ↦ hq0 o) (fun o ↦ hq1 o)
    (fun o ↦ hw0 r o) (fun o ↦ hw1 r o) (hlambda r)

theorem weightedSum_weightedRowSupport
    (weight : Delete → Option → ℝ) (r : Delete) (S : Finset Option) :
    weightedSum (fun o : Inside (weightedRowSupport weight r) ↦ weight r o)
        (splitEquiv (weightedRowSupport weight r) S).1 =
      ∑ o ∈ S, weight r o := by
  rw [weightedSum_splitEquiv_inside]
  unfold weightedRowSupport
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o ho
  by_cases hz : weight r o = 0 <;> simp [hz]

/-- One direct LLL round with simultaneous coverage lower bounds and deletion
upper bounds. -/
theorem exists_partialMatching_with_coverage_and_deletion_bounds
    (q : Option → ℝ)
    (coverWeight : Cover → Option → ℝ) (coverThreshold coverLambda : Cover → ℝ)
    (deleteWeight : Delete → Option → ℝ) (deleteThreshold deleteLambda : Delete → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨ (left c = p ∧ right c = o))
    (z : MixedBadIndex Conflict Cover Delete → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hcw0 : ∀ g o, 0 ≤ coverWeight g o)
    (hcw1 : ∀ g o, coverWeight g o ≤ 1)
    (hdw0 : ∀ r o, 0 ≤ deleteWeight r o)
    (hdw1 : ∀ r o, deleteWeight r o ≤ 1)
    (hclambda : ∀ g, 0 ≤ coverLambda g)
    (hdlambda : ∀ r, 0 ≤ deleteLambda r)
    (hz0 : ∀ b, 0 ≤ z b) (hz1 : ∀ b, z b < 1)
    (hpair : ∀ c, q (left c) * q (right c) ≤
      z (Sum.inl c) * ∏ b ∈ mixedBadNeighbor left right coverWeight deleteWeight (Sum.inl c),
        (1 - z b))
    (hcover : ∀ g,
      Real.exp (coverLambda g * coverThreshold g +
        (Real.exp (-coverLambda g) - 1) *
          mean (insideParameter q (coverageGroupSupport coverWeight g))
            (fun o : Inside (coverageGroupSupport coverWeight g) ↦ coverWeight g o)) ≤
      z (Sum.inr (Sum.inl g)) *
        ∏ b ∈ mixedBadNeighbor left right coverWeight deleteWeight
          (Sum.inr (Sum.inl g)), (1 - z b))
    (hdelete : ∀ r,
      Real.exp (-deleteLambda r * deleteThreshold r +
        (Real.exp (deleteLambda r) - 1) *
          mean (insideParameter q (weightedRowSupport deleteWeight r))
            (fun o : Inside (weightedRowSupport deleteWeight r) ↦ deleteWeight r o)) ≤
      z (Sum.inr (Sum.inr r)) *
        ∏ b ∈ mixedBadNeighbor left right coverWeight deleteWeight
          (Sum.inr (Sum.inr r)), (1 - z b)) :
    ∃ S : Finset Option, H.IsPartialMatching S ∧
      (∀ g, coverThreshold g < ∑ o ∈ S, coverWeight g o) ∧
      (∀ r, ∑ o ∈ S, deleteWeight r o < deleteThreshold r) := by
  let support := mixedBadSupport left right coverWeight deleteWeight
  let localBad := mixedLocalBad left right coverWeight coverThreshold
    deleteWeight deleteThreshold hne
  let neighbor := mixedBadNeighbor left right coverWeight deleteWeight
  have hlocal : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (support b))) (localBad b) ≤
        z b * ∏ a ∈ neighbor b, (1 - z a) := by
    intro b
    rcases b with c | g_or_r
    · exact (conflictPairLocalBad_mass left right q hne c).le.trans (hpair c)
    · rcases g_or_r with g | r
      · exact (coverageGroupLocalBad_mass_le q coverWeight coverThreshold coverLambda
          hq0 hq1 hcw0 hcw1 hclambda g).trans (hcover g)
      · exact (deletionRowLocalBad_mass_le q deleteWeight deleteThreshold deleteLambda
          hq0 hq1 hdw0 hdw1 hdlambda r).trans (hdelete r)
  have hpositive :=
    asymmetric_lopsided_local_lemma_of_disjoint_supports
      q support localBad neighbor z hq0 hq1 hz0 hz1
      (fun b a ha ↦ mixedBadNeighbor_nonneighbor_disjoint
        left right coverWeight deleteWeight b a ha) hlocal
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid
    (fun b ↦ insideCylinder (support b) (localBad b)) Finset.univ
  have hgood_ne : good ≠ ∅ := by
    intro hzero
    have hm : WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) good = 0 := by
      rw [hzero]
      simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
    rw [hm] at hpositive
    exact lt_irrefl 0 hpositive
  rcases Finset.nonempty_iff_ne_empty.mpr hgood_ne with ⟨S, hS⟩
  have havoid : ∀ b, S ∉ insideCylinder (support b) (localBad b) := by
    simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hS
  refine ⟨S, ?_, ?_, ?_⟩
  · constructor
    · intro o ho p hp hop
      by_contra hcompat
      rcases hcomplete o p hop (Or.inr hcompat) with ⟨c, hc | hc⟩
      · have hb := havoid (Sum.inl c)
        simp [support, localBad, mixedBadSupport, mixedLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hb
        exact hb ho hp
      · have hb := havoid (Sum.inl c)
        simp [support, localBad, mixedBadSupport, mixedLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hb
        exact hb hp ho
    · intro o ho p hp howner
      by_contra hop
      rcases hcomplete o p hop (Or.inl howner) with ⟨c, hc | hc⟩
      · have hb := havoid (Sum.inl c)
        simp [support, localBad, mixedBadSupport, mixedLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hb
        exact hb ho hp
      · have hb := havoid (Sum.inl c)
        simp [support, localBad, mixedBadSupport, mixedLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hb
        exact hb hp ho
  · intro g
    have hg := havoid (Sum.inr (Sum.inl g))
    rw [← weightedSum_coverageGroupSupport coverWeight g S]
    simpa [support, localBad, mixedBadSupport, mixedLocalBad,
      coverageGroupLocalBad, lowerTail, not_le] using hg
  · intro r
    have hr := havoid (Sum.inr (Sum.inr r))
    rw [← weightedSum_weightedRowSupport deleteWeight r S]
    simpa [support, localBad, mixedBadSupport, mixedLocalBad,
      deletionRowLocalBad, upperTail, not_le] using hr

/-! ## Concrete normalized residual-deletion rows -/

abbrev ResidualDeleteRow (Job Slot : Type*) := Job ⊕ Slot

/-- Job losses are normalized by `2*lambda`; slot losses are normalized by
`3*lambda`. Options already using the slot get coefficient zero, which is
exactly what is needed when that slot is unused by the selected matching. -/
noncomputable def residualDeleteWeight (lambda : ℕ) :
    ResidualDeleteRow Job Slot → Option → ℝ
  | Sum.inl j, p => (H.externalBlockedBy j p).card / (2 * lambda : ℕ)
  | Sum.inr s, p =>
      if s ∈ H.slots p then 0
      else (H.slotBlockedBy s p).card / (3 * lambda : ℕ)

noncomputable def residualDeleteThreshold (lambda : ℕ)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ) :
    ResidualDeleteRow Job Slot → ℝ
  | Sum.inl j => jobBudget j / (2 * lambda : ℕ)
  | Sum.inr s => slotBudget s / (3 * lambda : ℕ)

theorem residualDeleteWeight_nonneg (lambda : ℕ) :
    ∀ r p, 0 ≤ H.residualDeleteWeight lambda r p := by
  intro r p
  rcases r with j | s
  · rw [residualDeleteWeight]
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · by_cases hsp : s ∈ H.slots p
    · simp [residualDeleteWeight, hsp]
    · rw [residualDeleteWeight, if_neg hsp]
      exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem residualDeleteWeight_le_one (lambda : ℕ) (hlambda : 0 < lambda)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda) :
    ∀ r p, H.residualDeleteWeight lambda r p ≤ 1 := by
  intro r p
  rcases r with j | s
  · rw [residualDeleteWeight]
    apply (div_le_one (by positivity : (0 : ℝ) < (2 * lambda : ℕ))).2
    exact_mod_cast H.externalBlockedBy_card_le_two_mul j p lambda
      (fun t _ ↦ hjobSlot j t)
  · by_cases hsp : s ∈ H.slots p
    · simp [residualDeleteWeight, hsp]
    · rw [residualDeleteWeight, if_neg hsp]
      apply (div_le_one (by positivity : (0 : ℝ) < (3 * lambda : ℕ))).2
      exact_mod_cast H.slotBlockedBy_card_le_three_mul s p lambda hsp
        (hjobSlot (H.owner p) s) (fun t _ hst ↦ hslotPair s t hst)

theorem selected_residualDeleteWeight_job
    (lambda : ℕ) (S : Finset Option) (j : Job) :
    (∑ p ∈ S, H.residualDeleteWeight lambda (Sum.inl j) p) =
      H.externalJobDeletionLoad S j / (2 * lambda : ℕ) := by
  simp [residualDeleteWeight, externalJobDeletionLoad, Nat.cast_sum,
    Finset.sum_div]

theorem selected_residualDeleteWeight_slot
    (lambda : ℕ) (S : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ S, s ∉ H.slots p) :
    (∑ p ∈ S, H.residualDeleteWeight lambda (Sum.inr s) p) =
      H.slotDeletionLoad S s / (3 * lambda : ℕ) := by
  simp_rw [residualDeleteWeight]
  have hzero : ∀ p ∈ S, (if s ∈ H.slots p then (0 : ℝ)
      else (H.slotBlockedBy s p).card / (3 * lambda : ℕ)) =
      (H.slotBlockedBy s p).card / (3 * lambda : ℕ) := by
    intro p hp
    simp [hunused p hp]
  rw [Finset.sum_congr rfl hzero]
  simp [slotDeletionLoad, Nat.cast_sum, Finset.sum_div]

/-- A concrete one-round result. The upper-tail rows are the normalized
linear job and slot deletion overcounts. -/
theorem exists_oneRound_with_residual_degree_bounds
    (q : Option → ℝ)
    (coverWeight : Cover → Option → ℝ)
    (coverThreshold coverLambda : Cover → ℝ)
    (lambda : ℕ) (hlambdaPos : 0 < lambda)
    (jobBudget : Job → ℕ) (slotBudget : Slot → ℕ)
    (deleteLambda : ResidualDeleteRow Job Slot → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨ (left c = p ∧ right c = o))
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (z : MixedBadIndex Conflict Cover (ResidualDeleteRow Job Slot) → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hcw0 : ∀ g o, 0 ≤ coverWeight g o)
    (hcw1 : ∀ g o, coverWeight g o ≤ 1)
    (hclambda : ∀ g, 0 ≤ coverLambda g)
    (hdlambda : ∀ r, 0 ≤ deleteLambda r)
    (hz0 : ∀ b, 0 ≤ z b) (hz1 : ∀ b, z b < 1)
    (hpair : ∀ c, q (left c) * q (right c) ≤
      z (Sum.inl c) *
        ∏ b ∈ mixedBadNeighbor left right coverWeight
          (H.residualDeleteWeight lambda) (Sum.inl c), (1 - z b))
    (hcover : ∀ g,
      Real.exp (coverLambda g * coverThreshold g +
        (Real.exp (-coverLambda g) - 1) *
          mean (insideParameter q (coverageGroupSupport coverWeight g))
            (fun o : Inside (coverageGroupSupport coverWeight g) ↦ coverWeight g o)) ≤
      z (Sum.inr (Sum.inl g)) *
        ∏ b ∈ mixedBadNeighbor left right coverWeight
          (H.residualDeleteWeight lambda) (Sum.inr (Sum.inl g)), (1 - z b))
    (hdelete : ∀ r,
      Real.exp (-deleteLambda r *
          residualDeleteThreshold lambda jobBudget slotBudget r +
        (Real.exp (deleteLambda r) - 1) *
          mean (insideParameter q
              (weightedRowSupport (H.residualDeleteWeight lambda) r))
            (fun o : Inside
              (weightedRowSupport (H.residualDeleteWeight lambda) r) ↦
                H.residualDeleteWeight lambda r o)) ≤
      z (Sum.inr (Sum.inr r)) *
        ∏ b ∈ mixedBadNeighbor left right coverWeight
          (H.residualDeleteWeight lambda) (Sum.inr (Sum.inr r)), (1 - z b)) :
    ∃ S : Finset Option, H.IsPartialMatching S ∧
      (∀ g, coverThreshold g < ∑ o ∈ S, coverWeight g o) ∧
      (∀ j, ¬H.Covers S j →
        H.residualJobDegree ∅ j ≤ H.residualJobDegree S j + jobBudget j) ∧
      (∀ s, (∀ p ∈ S, s ∉ H.slots p) →
        H.residualSlotDegree ∅ s ≤ H.residualSlotDegree S s + slotBudget s) := by
  rcases H.exists_partialMatching_with_coverage_and_deletion_bounds
      left right q coverWeight coverThreshold coverLambda
      (H.residualDeleteWeight lambda)
      (residualDeleteThreshold lambda jobBudget slotBudget) deleteLambda
      hne hcomplete z hq0 hq1 hcw0 hcw1
      (H.residualDeleteWeight_nonneg lambda)
      (H.residualDeleteWeight_le_one lambda hlambdaPos hjobSlot hslotPair)
      hclambda hdlambda hz0 hz1 hpair hcover hdelete with
    ⟨S, hmatching, hcoverage, hdeletion⟩
  refine ⟨S, hmatching, hcoverage, ?_, ?_⟩
  · intro j huncovered
    have hnorm := hdeletion (Sum.inl j)
    rw [H.selected_residualDeleteWeight_job lambda S j] at hnorm
    have hden : (0 : ℝ) < (2 * lambda : ℕ) := by positivity
    have hcast : (H.externalJobDeletionLoad S j : ℝ) < jobBudget j := by
      apply (div_lt_div_iff_of_pos_right hden).mp
      simpa [residualDeleteThreshold] using hnorm
    have hload : H.externalJobDeletionLoad S j < jobBudget j := by
      exact_mod_cast hcast
    have hremoved :=
      H.removedResidualFiber_empty_card_le_externalJobDeletionLoad S j huncovered
    have hidentity := H.residualJobDegree_union_add_removed ∅ S j
    simp only [Finset.empty_union] at hidentity
    omega
  · intro s hunused
    have hnorm := hdeletion (Sum.inr s)
    rw [H.selected_residualDeleteWeight_slot lambda S s hunused] at hnorm
    have hden : (0 : ℝ) < (3 * lambda : ℕ) := by positivity
    have hcast : (H.slotDeletionLoad S s : ℝ) < slotBudget s := by
      apply (div_lt_div_iff_of_pos_right hden).mp
      simpa [residualDeleteThreshold] using hnorm
    have hload : H.slotDeletionLoad S s < slotBudget s := by
      exact_mod_cast hcast
    have hremoved := H.removedResidualSlot_empty_card_le_slotDeletionLoad S s hunused
    have hidentity := H.residualSlotDegree_union_add_removed ∅ S s
    simp only [Finset.empty_union] at hidentity
    omega

end WeightedEdgeColoring.RankThreeOptionSystem
