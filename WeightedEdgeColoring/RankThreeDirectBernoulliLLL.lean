import WeightedEdgeColoring.FiniteBernoulliCylinderLLL
import WeightedEdgeColoring.RankThreeIsolatedNibble

/-!
# Direct Bernoulli local lemma for conflict pairs and group coverage

Options are retained independently.  We forbid every listed conflicting pair
and every group lower-tail event.  A complete conflict list makes every
outcome avoiding the pair events a partial matching.  Group events are plain
Bernoulli lower tails, so no nonlinear isolation statistic is needed.
-/

namespace WeightedEdgeColoring

open scoped BigOperators
open FiniteBernoulliChernoff
open FiniteBernoulliSupportSplit

namespace FiniteBernoulliSupportSplit

variable {I J : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Asymmetric lopsided LLL for Bernoulli cylinder events whose non-neighbor
supports are disjoint. -/
theorem asymmetric_lopsided_local_lemma_of_disjoint_supports
    (q : I → ℝ)
    (support : J → Finset I)
    (localBad : (j : J) → Finset (Finset (Inside (support j))))
    (neighbor : J → Finset J)
    (x : J → ℝ)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_le_one : ∀ i, q i ≤ 1)
    (hx_nonneg : ∀ j, 0 ≤ x j) (hx_lt_one : ∀ j, x j < 1)
    (hdisjoint : ∀ j i, i ∉ insert j (neighbor j) →
      Disjoint (support j) (support i))
    (hlocal : ∀ j,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (support j))) (localBad j) ≤
        x j * ∏ i ∈ neighbor j, (1 - x i)) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun j ↦ insideCylinder (support j) (localBad j)) Finset.univ) := by
  let bad : J → Finset (Finset I) :=
    fun j ↦ insideCylinder (support j) (localBad j)
  have hlop : ∀ (j : J) (T : Finset J),
      T ⊆ Finset.univ \ insert j (neighbor j) →
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (bad j ∩ WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) ≤
        (x j * ∏ i ∈ neighbor j, (1 - x i)) *
          WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
            (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
    intro j T hT
    let outsideBad : J → Finset (Finset (Outside (support j))) :=
      fun i ↦ outsideView (support j) (support i) (localBad i)
    have havoid :
        WeightedEdgeColoring.FiniteLocalLemma.avoid bad T =
          WeightedEdgeColoring.FiniteLocalLemma.avoid
            (fun i ↦ outsideCylinder (support j) (outsideBad i)) T := by
      ext S
      simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro h i hi
        have hiOutside : i ∉ insert j (neighbor j) :=
          (Finset.mem_sdiff.mp (hT hi)).2
        rw [← insideCylinder_eq_outsideCylinder_of_disjoint
          (support j) (support i) (hdisjoint j i hiOutside) (localBad i)]
        exact h i hi
      · intro h i hi
        have hiOutside : i ∉ insert j (neighbor j) :=
          (Finset.mem_sdiff.mp (hT hi)).2
        change S ∉ insideCylinder (support i) (localBad i)
        rw [insideCylinder_eq_outsideCylinder_of_disjoint
          (support j) (support i) (hdisjoint j i hiOutside) (localBad i)]
        exact h i hi
    rw [havoid]
    exact conditional_le_avoid_outsideCylinders q (support j) (localBad j)
      outsideBad T (x j * ∏ i ∈ neighbor j, (1 - x i))
      hq_nonneg hq_le_one (hlocal j)
  have hres := WeightedEdgeColoring.FiniteLocalLemma.asymmetric_lopsided_local_lemma
    (bernoulliMass q) bad neighbor x
    (bernoulliMass_nonneg q hq_nonneg hq_le_one)
    (sum_bernoulliMass q) hx_nonneg hx_lt_one hlop
  simpa [bad] using hres.2

/-- A weighted sum on the inside projection is the corresponding filtered
global weighted sum. -/
theorem weightedSum_splitEquiv_inside (K S : Finset I) (a : I → ℝ) :
    weightedSum (fun i : Inside K ↦ a i) (splitEquiv K S).1 =
      ∑ i ∈ S.filter (fun i ↦ i ∈ K), a i := by
  let valEmbedding : Inside K ↪ I :=
    ⟨fun i ↦ i.1, Subtype.val_injective⟩
  have hmap : (splitEquiv K S).1.map valEmbedding =
      S.filter fun i ↦ i ∈ K := by
    ext i
    simp [valEmbedding]
  unfold weightedSum
  rw [← hmap]
  simp [valEmbedding]

end FiniteBernoulliSupportSplit

namespace RankThreeOptionSystem

universe u v w z

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type z}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- A listed pair of distinct options that cannot simultaneously belong to a
partial matching. -/
structure ListedConflict where
  left : Option
  right : Option
  ne : left ≠ right
  conflicts : H.owner left = H.owner right ∨ ¬ H.Compatible left right

variable {Conflict : Type*} [Fintype Conflict] [DecidableEq Conflict]
variable (left right : Conflict → Option)

/-- The two Bernoulli coordinates read by one conflict-pair event. -/
def conflictPairSupport (c : Conflict) : Finset Option :=
  {left c, right c}

/-- Coordinates carrying a nonzero coefficient in one group statistic. -/
noncomputable def coverageGroupSupport (weight : Group → Option → ℝ) (g : Group) :
    Finset Option :=
  Finset.univ.filter fun o ↦ weight g o ≠ 0

/-- Indices of the two kinds of bad events. -/
abbrev DirectBadIndex (Conflict Group : Type*) := Conflict ⊕ Group

/-- Coordinate support of one direct bad event. -/
noncomputable def directBadSupport (weight : Group → Option → ℝ) :
    DirectBadIndex Conflict Group → Finset Option
  | Sum.inl c => conflictPairSupport left right c
  | Sum.inr g => coverageGroupSupport weight g

/-- Local conflict-pair event: both listed coordinates are retained. -/
noncomputable def conflictPairLocalBad
    (hne : ∀ c, left c ≠ right c) (c : Conflict) :
    Finset (Finset (Inside (conflictPairSupport left right c))) :=
  Finset.univ.filter fun S ↦
    (⟨left c, by simp [conflictPairSupport]⟩ :
      Inside (conflictPairSupport left right c)) ∈ S ∧
    (⟨right c, by simp [conflictPairSupport]⟩ :
      Inside (conflictPairSupport left right c)) ∈ S

/-- Local lower-tail event for one prescribed coverage group. -/
noncomputable def coverageGroupLocalBad
    (weight : Group → Option → ℝ) (threshold : Group → ℝ) (g : Group) :
    Finset (Finset (Inside (coverageGroupSupport weight g))) :=
  lowerTail
    (weightedSum (fun o : Inside (coverageGroupSupport weight g) ↦ weight g o))
    (threshold g)

/-- Local bad-event family used by the direct Bernoulli LLL. -/
noncomputable def directLocalBad
    (weight : Group → Option → ℝ) (threshold : Group → ℝ)
    (hne : ∀ c, left c ≠ right c) :
    (b : DirectBadIndex Conflict Group) →
      Finset (Finset (Inside (directBadSupport left right weight b)))
  | Sum.inl c => conflictPairLocalBad left right hne c
  | Sum.inr g => coverageGroupLocalBad weight threshold g

/-- The loopless support-intersection neighborhood of direct bad events. -/
noncomputable def directBadNeighbor (weight : Group → Option → ℝ)
    (b : DirectBadIndex Conflict Group) : Finset (DirectBadIndex Conflict Group) :=
  Finset.univ.filter fun a ↦ a ≠ b ∧
    ¬Disjoint (directBadSupport left right weight b)
      (directBadSupport left right weight a)

theorem directBadNeighbor_nonneighbor_disjoint
    (weight : Group → Option → ℝ) (b a : DirectBadIndex Conflict Group)
    (ha : a ∉ insert b (directBadNeighbor left right weight b)) :
    Disjoint (directBadSupport left right weight b)
      (directBadSupport left right weight a) := by
  by_contra hdisj
  have hab : a ≠ b := by
    intro h
    subst a
    exact ha (Finset.mem_insert_self b _)
  apply ha
  apply Finset.mem_insert_of_mem
  simp [directBadNeighbor, hab, hdisj]

/-- Bad-event supports containing one option coordinate. -/
noncomputable def directBadIncidence (weight : Group → Option → ℝ) (o : Option) :
    Finset (DirectBadIndex Conflict Group) :=
  Finset.univ.filter fun b ↦ o ∈ directBadSupport left right weight b

/-- Generic support-overlap degree bound for the direct bad-event family. -/
theorem directBadNeighbor_card_le
    (weight : Group → Option → ℝ) (K D : ℕ)
    (hsupport : ∀ b, (directBadSupport left right weight b).card ≤ K)
    (hincidence : ∀ o, (directBadIncidence left right weight o).card ≤ D)
    (b : DirectBadIndex Conflict Group) :
    (directBadNeighbor left right weight b).card ≤ K * D := by
  have hsub : directBadNeighbor left right weight b ⊆
      (directBadSupport left right weight b).biUnion
        (directBadIncidence left right weight) := by
    intro a ha
    have hnot := (Finset.mem_filter.mp ha).2.2
    rw [Finset.not_disjoint_iff] at hnot
    rcases hnot with ⟨o, hob, hoa⟩
    exact Finset.mem_biUnion.mpr ⟨o, hob,
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hoa⟩⟩
  calc
    (directBadNeighbor left right weight b).card ≤
        ((directBadSupport left right weight b).biUnion
          (directBadIncidence left right weight)).card := Finset.card_le_card hsub
    _ ≤ ∑ o ∈ directBadSupport left right weight b,
        (directBadIncidence left right weight o).card := Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ directBadSupport left right weight b, D := by
      exact Finset.sum_le_sum fun o _ ↦ hincidence o
    _ = (directBadSupport left right weight b).card * D := by simp
    _ ≤ K * D := Nat.mul_le_mul_right D (hsupport b)

/-- Pair supports always have size at most two. -/
theorem conflictPairSupport_card_le_two (c : Conflict) :
    (conflictPairSupport left right c).card ≤ 2 := by
  calc
    (conflictPairSupport left right c).card ≤
        ({right c} : Finset Option).card + 1 := by
      exact Finset.card_insert_le (left c) {right c}
    _ = 2 := by simp

/-- A uniform group-support bound and the two-coordinate pair bound give one
uniform support bound for the whole mixed bad-event family. -/
theorem directBadSupport_card_le_max
    (weight : Group → Option → ℝ) (K : ℕ)
    (hgroup : ∀ g, (coverageGroupSupport weight g).card ≤ K)
    (b : DirectBadIndex Conflict Group) :
    (directBadSupport left right weight b).card ≤ max 2 K := by
  rcases b with c | g
  · exact (conflictPairSupport_card_le_two left right c).trans
      (Nat.le_max_left 2 K)
  · exact (hgroup g).trans (Nat.le_max_right 2 K)

/-- Exact local probability of retaining both ends of one listed pair. -/
theorem conflictPairLocalBad_mass
    (q : Option → ℝ) (hne : ∀ c, left c ≠ right c) (c : Conflict) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (conflictPairSupport left right c)))
        (conflictPairLocalBad left right hne c) =
      q (left c) * q (right c) := by
  let l : Inside (conflictPairSupport left right c) :=
    ⟨left c, by simp [conflictPairSupport]⟩
  let r : Inside (conflictPairSupport left right c) :=
    ⟨right c, by simp [conflictPairSupport]⟩
  have hlr : l ≠ r := by
    intro h
    exact hne c (congrArg Subtype.val h)
  have hp := WeightedEdgeColoring.FiniteBernoulliThinning.sum_bernoulliMass_indicator_pair
    (insideParameter q (conflictPairSupport left right c)) hlr
  simpa [WeightedEdgeColoring.FiniteLocalLemma.eventMass, conflictPairLocalBad,
    l, r, insideParameter, Finset.sum_filter, mul_ite] using hp

/-- Chernoff bound for one local group lower tail. -/
theorem coverageGroupLocalBad_mass_le
    (q : Option → ℝ) (weight : Group → Option → ℝ)
    (threshold lambda : Group → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hw0 : ∀ g o, 0 ≤ weight g o) (hw1 : ∀ g o, weight g o ≤ 1)
    (hlambda : ∀ g, 0 ≤ lambda g) (g : Group) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (coverageGroupSupport weight g)))
        (coverageGroupLocalBad weight threshold g) ≤
      Real.exp (lambda g * threshold g + (Real.exp (-lambda g) - 1) *
        mean (insideParameter q (coverageGroupSupport weight g))
          (fun o : Inside (coverageGroupSupport weight g) ↦ weight g o)) := by
  exact bernoulli_lowerTail_le
    (insideParameter q (coverageGroupSupport weight g))
    (fun o : Inside (coverageGroupSupport weight g) ↦ weight g o)
    (threshold g) (lambda g)
    (fun o ↦ hq0 o) (fun o ↦ hq1 o)
    (fun o ↦ hw0 g o) (fun o ↦ hw1 g o) (hlambda g)

/-- Projection to the nonzero support does not change the selected raw
weighted mass. -/
theorem weightedSum_coverageGroupSupport
    (weight : Group → Option → ℝ) (g : Group) (S : Finset Option) :
    weightedSum
        (fun o : Inside (coverageGroupSupport weight g) ↦ weight g o)
        (splitEquiv (coverageGroupSupport weight g) S).1 =
      ∑ o ∈ S, weight g o := by
  rw [weightedSum_splitEquiv_inside]
  unfold coverageGroupSupport
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o ho
  by_cases hzero : weight g o = 0 <;> simp [hzero]

/-- Direct asymmetric-LLL selection.  The conflict list must contain every
distinct owner or slot conflict; it may contain additional pairs. -/
theorem exists_partialMatching_with_group_projection_lower_bounds
    (q : Option → ℝ)
    (weight : Group → Option → ℝ) (threshold lambda : Group → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (x : DirectBadIndex Conflict Group → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hw0 : ∀ g o, 0 ≤ weight g o) (hw1 : ∀ g o, weight g o ≤ 1)
    (hlambda : ∀ g, 0 ≤ lambda g)
    (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b < 1)
    (hpairNumeric : ∀ c,
      q (left c) * q (right c) ≤
        x (Sum.inl c) *
          ∏ b ∈ directBadNeighbor left right weight (Sum.inl c), (1 - x b))
    (hgroupNumeric : ∀ g,
      Real.exp (lambda g * threshold g + (Real.exp (-lambda g) - 1) *
        mean (insideParameter q (coverageGroupSupport weight g))
          (fun o : Inside (coverageGroupSupport weight g) ↦ weight g o)) ≤
        x (Sum.inr g) *
          ∏ b ∈ directBadNeighbor left right weight (Sum.inr g), (1 - x b)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      ∀ g, threshold g <
        weightedSum
          (fun o : Inside (coverageGroupSupport weight g) ↦ weight g o)
          (splitEquiv (coverageGroupSupport weight g) S).1 := by
  let support := directBadSupport left right weight
  let localBad := directLocalBad left right weight threshold hne
  let neighbor := directBadNeighbor left right weight
  have hlocal : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (support b))) (localBad b) ≤
        x b * ∏ a ∈ neighbor b, (1 - x a) := by
    intro b
    rcases b with c | g
    · exact (conflictPairLocalBad_mass left right q hne c).le.trans
        (hpairNumeric c)
    · exact (coverageGroupLocalBad_mass_le q weight threshold lambda
        hq0 hq1 hw0 hw1 hlambda g).trans (hgroupNumeric g)
  have hpositive :=
    asymmetric_lopsided_local_lemma_of_disjoint_supports
      q support localBad neighbor x hq0 hq1 hx0 hx1
      (fun b a ha ↦ directBadNeighbor_nonneighbor_disjoint
        left right weight b a ha) hlocal
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid
    (fun b ↦ insideCylinder (support b) (localBad b)) Finset.univ
  have hgood_ne : good ≠ ∅ := by
    intro hzero
    have hmasszero : WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) good = 0 := by
      rw [hzero]
      simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
    rw [hmasszero] at hpositive
    exact lt_irrefl 0 hpositive
  rcases Finset.nonempty_iff_ne_empty.mpr hgood_ne with ⟨S, hS⟩
  have havoid : ∀ b, S ∉ insideCylinder (support b) (localBad b) := by
    simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hS
  refine ⟨S, ?_, ?_⟩
  · constructor
    · intro o ho p hp hop
      by_contra hcompat
      rcases hcomplete o p hop (Or.inr hcompat) with ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directBadSupport, directLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directBadSupport, directLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
    · intro o ho p hp howner
      by_contra hop
      rcases hcomplete o p hop (Or.inl howner) with
        ⟨c, hc | hc⟩
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directBadSupport, directLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad ho hp
      · have hbad := havoid (Sum.inl c)
        simp [support, localBad, directBadSupport, directLocalBad,
          conflictPairLocalBad, hc.1, hc.2] at hbad
        exact hbad hp ho
  · intro g
    have hg := havoid (Sum.inr g)
    simpa [support, localBad, directBadSupport, directLocalBad,
      coverageGroupLocalBad, lowerTail, not_le] using hg

/-- Direct asymmetric-LLL selection, stated using the actual raw selected
weighted mass of every group. -/
theorem exists_partialMatching_with_group_lower_bounds
    (q : Option → ℝ)
    (weight : Group → Option → ℝ) (threshold lambda : Group → ℝ)
    (hne : ∀ c, left c ≠ right c)
    (hcomplete : ∀ o p, o ≠ p →
      (H.owner o = H.owner p ∨ ¬H.Compatible o p) →
      ∃ c, (left c = o ∧ right c = p) ∨
        (left c = p ∧ right c = o))
    (x : DirectBadIndex Conflict Group → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hw0 : ∀ g o, 0 ≤ weight g o) (hw1 : ∀ g o, weight g o ≤ 1)
    (hlambda : ∀ g, 0 ≤ lambda g)
    (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b < 1)
    (hpairNumeric : ∀ c,
      q (left c) * q (right c) ≤
        x (Sum.inl c) *
          ∏ b ∈ directBadNeighbor left right weight (Sum.inl c), (1 - x b))
    (hgroupNumeric : ∀ g,
      Real.exp (lambda g * threshold g + (Real.exp (-lambda g) - 1) *
        mean (insideParameter q (coverageGroupSupport weight g))
          (fun o : Inside (coverageGroupSupport weight g) ↦ weight g o)) ≤
        x (Sum.inr g) *
          ∏ b ∈ directBadNeighbor left right weight (Sum.inr g), (1 - x b)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      ∀ g, threshold g < ∑ o ∈ S, weight g o := by
  rcases H.exists_partialMatching_with_group_projection_lower_bounds
      left right q weight threshold lambda hne hcomplete x
      hq0 hq1 hw0 hw1 hlambda hx0 hx1 hpairNumeric hgroupNumeric with
    ⟨S, hmatching, hgroups⟩
  refine ⟨S, hmatching, ?_⟩
  intro g
  rw [← weightedSum_coverageGroupSupport weight g S]
  exact hgroups g

end RankThreeOptionSystem

end WeightedEdgeColoring
