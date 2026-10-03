import WeightedEdgeColoring.RankThreeIsolatedNibble
import WeightedEdgeColoring.FiniteBernoulliCylinderLLL

/-!
# Selecting a conflict-free set with prescribed group coverage

Every conflicting ordered pair gives a two-coordinate bad event.  Every
prescribed group gives a lower-tail bad event on its member coordinates.
Avoiding all pair events makes the selected options a partial matching;
avoiding all group events gives the requested raw coverage.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w z

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type z}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]

/-- Ordered conflicting pairs.  Keeping both coordinates is forbidden. -/
abbrev ConflictIndex (H : RankThreeOptionSystem Job Slot Option) :=
  {op : Option × Option // op.1 ≠ op.2 ∧
    (H.owner op.1 = H.owner op.2 ∨ ¬ H.Compatible op.1 op.2)}

/-- Pair-conflict constraints together with group lower-tail constraints. -/
abbrev GroupSelectionConstraint
    (H : RankThreeOptionSystem Job Slot Option) (Group : Type z) :=
  H.ConflictIndex ⊕ Group

/-- Coordinates read by one pair or group event. -/
def groupSelectionSupport
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option) :
    H.GroupSelectionConstraint Group → Finset Option
  | Sum.inl a => {a.1.1, a.1.2}
  | Sum.inr g => members g

/-- Constraints whose support contains one option coordinate. -/
def groupSelectionConstraintsAt
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option) (o : Option) :
    Finset (H.GroupSelectionConstraint Group) :=
  Finset.univ.filter fun b ↦ o ∈ H.groupSelectionSupport members b

/-- The canonical support-overlap dependency graph. -/
def groupSelectionNeighbors
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option)
    (b : H.GroupSelectionConstraint Group) :
    Finset (H.GroupSelectionConstraint Group) :=
  ((Finset.univ : Finset (H.GroupSelectionConstraint Group)).erase b).filter
    fun c ↦ ¬ Disjoint (H.groupSelectionSupport members b)
      (H.groupSelectionSupport members c)

theorem groupSelectionNeighbors_disjoint_of_not_mem
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option)
    (b c : H.GroupSelectionConstraint Group)
    (hc : c ∉ insert b (H.groupSelectionNeighbors members b)) :
    Disjoint (H.groupSelectionSupport members b)
      (H.groupSelectionSupport members c) := by
  by_contra h
  apply hc
  by_cases hcb : c = b
  · exact Finset.mem_insert.mpr (Or.inl hcb)
  · exact Finset.mem_insert.mpr (Or.inr (by
      simp [groupSelectionNeighbors, h, hcb]))

/-- An overlap neighbour is seen in the incidence list of some coordinate
of the first support. -/
theorem groupSelectionNeighbors_subset_biUnion
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option)
    (b : H.GroupSelectionConstraint Group) :
    H.groupSelectionNeighbors members b ⊆
      (H.groupSelectionSupport members b).biUnion
        (H.groupSelectionConstraintsAt members) := by
  intro c hc
  have hoverlap : ¬ Disjoint (H.groupSelectionSupport members b)
      (H.groupSelectionSupport members c) :=
    (Finset.mem_filter.mp hc).2
  rw [Finset.not_disjoint_iff] at hoverlap
  rcases hoverlap with ⟨o, hob, hoc⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨o, hob, ?_⟩
  simp [groupSelectionConstraintsAt, hoc]

/-- Explicit dependency count: support size at most `K` and coordinate
incidence at most `L` imply dependency degree at most `K*L`. -/
theorem groupSelectionNeighbors_card_le
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option) (K L : ℕ)
    (hsupport : ∀ b, (H.groupSelectionSupport members b).card ≤ K)
    (hincidence : ∀ o, (H.groupSelectionConstraintsAt members o).card ≤ L)
    (b : H.GroupSelectionConstraint Group) :
    (H.groupSelectionNeighbors members b).card ≤ K * L := by
  calc
    (H.groupSelectionNeighbors members b).card ≤
        ((H.groupSelectionSupport members b).biUnion
          (H.groupSelectionConstraintsAt members)).card :=
      Finset.card_le_card (H.groupSelectionNeighbors_subset_biUnion members b)
    _ ≤ ∑ o ∈ H.groupSelectionSupport members b,
        (H.groupSelectionConstraintsAt members o).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ H.groupSelectionSupport members b, L := by
      exact Finset.sum_le_sum fun o _ ↦ hincidence o
    _ = (H.groupSelectionSupport members b).card * L := by simp
    _ ≤ K * L := Nat.mul_le_mul_right L (hsupport b)

/-- Local bad event: both coordinates of a conflict pair are active, or a
group has selected size at most its threshold. -/
noncomputable def groupSelectionLocalBad
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option) (threshold : Group → ℝ) :
    (b : H.GroupSelectionConstraint Group) →
      Finset (Finset (Inside (H.groupSelectionSupport members b)))
  | Sum.inl a => Finset.univ.filter fun S ↦
      (⟨a.1.1, by simp [groupSelectionSupport]⟩ :
        Inside (H.groupSelectionSupport members (Sum.inl a))) ∈ S ∧
      (⟨a.1.2, by simp [groupSelectionSupport]⟩ :
        Inside (H.groupSelectionSupport members (Sum.inl a))) ∈ S
  | Sum.inr g => lowerTail (weightedSum (fun _ ↦ 1)) (threshold g)

/-- Pair-cylinder membership is exactly simultaneous activity of the two
conflicting options. -/
theorem mem_groupSelection_pairCylinder
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option) (threshold : Group → ℝ)
    (a : H.ConflictIndex) (S : Finset Option) :
    S ∈ insideCylinder (H.groupSelectionSupport members (Sum.inl a))
        (H.groupSelectionLocalBad members threshold (Sum.inl a)) ↔
      a.1.1 ∈ S ∧ a.1.2 ∈ S := by
  simp [groupSelectionLocalBad]

/-- Exact local probability of one pair-conflict event. -/
theorem groupSelection_pairLocalBad_mass
    (H : RankThreeOptionSystem Job Slot Option)
    (q : Option → ℝ) (members : Group → Finset Option)
    (threshold : Group → ℝ) (a : H.ConflictIndex) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (bernoulliMass
        (insideParameter q (H.groupSelectionSupport members (Sum.inl a))))
      (H.groupSelectionLocalBad members threshold (Sum.inl a)) =
      q a.1.1 * q a.1.2 := by
  let i : Inside (H.groupSelectionSupport members (Sum.inl a)) :=
    ⟨a.1.1, by simp [groupSelectionSupport]⟩
  let j : Inside (H.groupSelectionSupport members (Sum.inl a)) :=
    ⟨a.1.2, by simp [groupSelectionSupport]⟩
  have hij : i ≠ j := by
    intro h
    exact a.2.1 (congrArg Subtype.val h)
  have hpair := WeightedEdgeColoring.FiniteBernoulliThinning.sum_bernoulliMass_indicator_pair
    (insideParameter q (H.groupSelectionSupport members (Sum.inl a))) hij
  unfold groupSelectionLocalBad
  unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass
  rw [Finset.sum_filter]
  simpa [i, j, insideParameter] using hpair

/-- Chernoff expression for one group lower-tail event. -/
noncomputable def groupSelectionChernoffBound
    (H : RankThreeOptionSystem Job Slot Option)
    (q : Option → ℝ) (members : Group → Finset Option)
    (threshold lambda : Group → ℝ) (g : Group) : ℝ :=
  Real.exp (lambda g * threshold g + (Real.exp (-lambda g) - 1) *
    mean (insideParameter q (H.groupSelectionSupport members (Sum.inr g)))
      (fun _ ↦ 1))

/-- The group local event satisfies its displayed lower-tail Chernoff bound. -/
theorem groupSelection_groupLocalBad_mass_le
    (H : RankThreeOptionSystem Job Slot Option)
    (q : Option → ℝ) (members : Group → Finset Option)
    (threshold lambda : Group → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlambda : ∀ g, 0 ≤ lambda g) (g : Group) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (bernoulliMass
        (insideParameter q (H.groupSelectionSupport members (Sum.inr g))))
      (H.groupSelectionLocalBad members threshold (Sum.inr g)) ≤
      H.groupSelectionChernoffBound q members threshold lambda g := by
  simpa [groupSelectionLocalBad, groupSelectionChernoffBound] using
    (bernoulli_lowerTail_le
      (insideParameter q (H.groupSelectionSupport members (Sum.inr g)))
      (fun _ ↦ 1) (threshold g) (lambda g)
      (fun i ↦ hq0 i) (fun i ↦ hq1 i)
      (fun _ ↦ by positivity) (fun _ ↦ le_rfl) (hlambda g))

/-- The inside projection on a group support counts exactly the selected
members of that group. -/
theorem card_groupSelection_inside
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option) (g : Group) (S : Finset Option) :
    (splitEquiv (H.groupSelectionSupport members (Sum.inr g)) S).1.card =
      (S ∩ members g).card := by
  rw [card_splitEquiv_inside]
  congr 1

/-- Avoiding all pair events gives a partial matching. -/
theorem isPartialMatching_of_avoids_groupSelectionPairs
    (H : RankThreeOptionSystem Job Slot Option)
    (members : Group → Finset Option) (threshold : Group → ℝ)
    (S : Finset Option)
    (havoid : ∀ a : H.ConflictIndex,
      S ∉ insideCylinder (H.groupSelectionSupport members (Sum.inl a))
        (H.groupSelectionLocalBad members threshold (Sum.inl a))) :
    H.IsPartialMatching S := by
  constructor
  · intro o ho p hp hop
    by_contra hcompat
    let a : H.ConflictIndex :=
      ⟨(o, p), fun h ↦ hop h, Or.inr hcompat⟩
    exact havoid a ((H.mem_groupSelection_pairCylinder members threshold a S).2
      ⟨ho, hp⟩)
  · intro o ho p hp howner
    by_contra hop
    let a : H.ConflictIndex :=
      ⟨(o, p), hop, Or.inl howner⟩
    exact havoid a ((H.mem_groupSelection_pairCylinder members threshold a S).2
      ⟨ho, hp⟩)

/-- Asymmetric lopsided LLL for Bernoulli cylinder events whose non-neighbour
supports are disjoint. -/
theorem asymmetric_lopsided_local_lemma_of_disjoint_supports
    {I C : Type*} [Fintype I] [DecidableEq I]
    [Fintype C] [DecidableEq C]
    (q : I → ℝ) (support : C → Finset I)
    (localBad : (c : C) → Finset (Finset (Inside (support c))))
    (neighbor : C → Finset C) (x : C → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hx0 : ∀ c, 0 ≤ x c) (hx1 : ∀ c, x c < 1)
    (hdisjoint : ∀ c d, d ∉ insert c (neighbor c) →
      Disjoint (support c) (support d))
    (hlocal : ∀ c,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass (insideParameter q (support c))) (localBad c) ≤
        x c * ∏ d ∈ neighbor c, (1 - x d)) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun c ↦ insideCylinder (support c) (localBad c)) Finset.univ) := by
  let bad : C → Finset (Finset I) :=
    fun c ↦ insideCylinder (support c) (localBad c)
  let outsideBad : (c : C) → C → Finset (Finset (Outside (support c))) :=
    fun c d ↦ outsideView (support c) (support d) (localBad d)
  refine (WeightedEdgeColoring.FiniteLocalLemma.asymmetric_lopsided_local_lemma
    (bernoulliMass q) bad neighbor x
    (bernoulliMass_nonneg q hq0 hq1) (sum_bernoulliMass q) hx0 hx1 ?_).2
  intro c T hT
  have havoid : WeightedEdgeColoring.FiniteLocalLemma.avoid bad T =
      WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun d ↦ outsideCylinder (support c) (outsideBad c d)) T := by
    ext S
    simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h d hd
      have hdout : d ∉ insert c (neighbor c) :=
        (Finset.mem_sdiff.mp (hT hd)).2
      rw [← insideCylinder_eq_outsideCylinder_of_disjoint
        (support c) (support d) (hdisjoint c d hdout) (localBad d)]
      exact h d hd
    · intro h d hd
      have hdout : d ∉ insert c (neighbor c) :=
        (Finset.mem_sdiff.mp (hT hd)).2
      change S ∉ insideCylinder (support d) (localBad d)
      rw [insideCylinder_eq_outsideCylinder_of_disjoint
        (support c) (support d) (hdisjoint c d hdout) (localBad d)]
      exact h d hd
  change WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (insideCylinder (support c) (localBad c) ∩
        WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) ≤ _
  rw [havoid]
  exact conditional_le_avoid_outsideCylinders q (support c) (localBad c)
    (outsideBad c) T
    (x c * ∏ d ∈ neighbor c, (1 - x d)) hq0 hq1 (hlocal c)

/-- Generic symmetric-LLL group selection theorem.  Local event probability
bounds are left explicit so pair events and Chernoff group events can be
estimated separately. -/
theorem exists_partialMatching_with_groupCoverage_of_localLemma
    (H : RankThreeOptionSystem Job Slot Option)
    (q : Option → ℝ) (members : Group → Finset Option)
    (threshold : Group → ℝ)
    (K L : ℕ) (p x : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hsupport : ∀ b, (H.groupSelectionSupport members b).card ≤ K)
    (hincidence : ∀ o, (H.groupSelectionConstraintsAt members o).card ≤ L)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ (K * L))
    (hlocal : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.groupSelectionSupport members b)))
        (H.groupSelectionLocalBad members threshold b) ≤ p) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      ∀ g, threshold g < ((S ∩ members g).card : ℝ) := by
  have hpositive := symmetric_lopsided_local_lemma_of_disjoint_supports
    q (H.groupSelectionSupport members)
    (H.groupSelectionLocalBad members threshold)
    (H.groupSelectionNeighbors members) p x (K * L)
    hq0 hq1
    (H.groupSelectionNeighbors_card_le members K L hsupport hincidence)
    hx0 hx1 hnumeric
    (H.groupSelectionNeighbors_disjoint_of_not_mem members) hlocal
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid
    (fun b ↦ insideCylinder (H.groupSelectionSupport members b)
      (H.groupSelectionLocalBad members threshold b)) Finset.univ
  have hgood : good.Nonempty := by
    by_contra hempty
    have hz : WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) good = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
    rw [hz] at hpositive
    exact lt_irrefl 0 hpositive
  rcases hgood with ⟨S, hS⟩
  have havoid : ∀ b,
      S ∉ insideCylinder (H.groupSelectionSupport members b)
        (H.groupSelectionLocalBad members threshold b) := by
    simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hS
  refine ⟨S,
    H.isPartialMatching_of_avoids_groupSelectionPairs members threshold S
      (fun a ↦ havoid (Sum.inl a)), ?_⟩
  intro g
  have hg := havoid (Sum.inr g)
  have hg' : threshold g <
      ((splitEquiv (H.groupSelectionSupport members (Sum.inr g)) S).1.card : ℝ) := by
    simpa [groupSelectionLocalBad, lowerTail, weightedSum, not_le] using hg
  rw [show
    ((splitEquiv (H.groupSelectionSupport members (Sum.inr g)) S).1.card : ℝ) =
      ((S ∩ members g).card : ℝ) by
        exact_mod_cast H.card_groupSelection_inside members g S] at hg'
  exact hg'

/-- Concrete LLL criterion using exact pair probabilities and ordinary
Bernoulli Chernoff bounds for the groups. -/
theorem exists_partialMatching_with_groupCoverage
    (H : RankThreeOptionSystem Job Slot Option)
    (q : Option → ℝ) (members : Group → Finset Option)
    (threshold lambda : Group → ℝ)
    (K L : ℕ) (p x : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlambda : ∀ g, 0 ≤ lambda g)
    (hsupport : ∀ b, (H.groupSelectionSupport members b).card ≤ K)
    (hincidence : ∀ o, (H.groupSelectionConstraintsAt members o).card ≤ L)
    (hpair : ∀ a : H.ConflictIndex, q a.1.1 * q a.1.2 ≤ p)
    (hgroup : ∀ g,
      H.groupSelectionChernoffBound q members threshold lambda g ≤ p)
    (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hnumeric : p ≤ x * (1 - x) ^ (K * L)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      ∀ g, threshold g < ((S ∩ members g).card : ℝ) := by
  apply H.exists_partialMatching_with_groupCoverage_of_localLemma
    q members threshold K L p x hq0 hq1 hsupport hincidence hx0 hx1 hnumeric
  intro b
  rcases b with a | g
  · rw [H.groupSelection_pairLocalBad_mass q members threshold a]
    exact hpair a
  · exact (H.groupSelection_groupLocalBad_mass_le q members threshold lambda
      hq0 hq1 hlambda g).trans (hgroup g)

/-- Asymmetric criterion, retaining the very different scales of pair and
group bad events. -/
theorem exists_partialMatching_with_groupCoverage_asymmetric
    (H : RankThreeOptionSystem Job Slot Option)
    (q : Option → ℝ) (members : Group → Finset Option)
    (threshold lambda : Group → ℝ)
    (x : H.GroupSelectionConstraint Group → ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hlambda : ∀ g, 0 ≤ lambda g)
    (hx0 : ∀ b, 0 ≤ x b) (hx1 : ∀ b, x b < 1)
    (hpair : ∀ a : H.ConflictIndex,
      q a.1.1 * q a.1.2 ≤
        x (Sum.inl a) *
          ∏ b ∈ H.groupSelectionNeighbors members (Sum.inl a), (1 - x b))
    (hgroup : ∀ g,
      H.groupSelectionChernoffBound q members threshold lambda g ≤
        x (Sum.inr g) *
          ∏ b ∈ H.groupSelectionNeighbors members (Sum.inr g), (1 - x b)) :
    ∃ S : Finset Option,
      H.IsPartialMatching S ∧
      ∀ g, threshold g < ((S ∩ members g).card : ℝ) := by
  have hlocal : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.groupSelectionSupport members b)))
        (H.groupSelectionLocalBad members threshold b) ≤
        x b * ∏ d ∈ H.groupSelectionNeighbors members b, (1 - x d) := by
    intro b
    rcases b with a | g
    · rw [H.groupSelection_pairLocalBad_mass q members threshold a]
      exact hpair a
    · exact (H.groupSelection_groupLocalBad_mass_le q members threshold lambda
        hq0 hq1 hlambda g).trans (hgroup g)
  have hpositive := asymmetric_lopsided_local_lemma_of_disjoint_supports
    q (H.groupSelectionSupport members)
    (H.groupSelectionLocalBad members threshold)
    (H.groupSelectionNeighbors members) x hq0 hq1 hx0 hx1
    (H.groupSelectionNeighbors_disjoint_of_not_mem members) hlocal
  let good := WeightedEdgeColoring.FiniteLocalLemma.avoid
    (fun b ↦ insideCylinder (H.groupSelectionSupport members b)
      (H.groupSelectionLocalBad members threshold b)) Finset.univ
  have hgood : good.Nonempty := by
    by_contra hempty
    have hz : WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) good = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass]
    rw [hz] at hpositive
    exact lt_irrefl 0 hpositive
  rcases hgood with ⟨S, hS⟩
  have havoid : ∀ b,
      S ∉ insideCylinder (H.groupSelectionSupport members b)
        (H.groupSelectionLocalBad members threshold b) := by
    simpa [good, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hS
  refine ⟨S,
    H.isPartialMatching_of_avoids_groupSelectionPairs members threshold S
      (fun a ↦ havoid (Sum.inl a)), ?_⟩
  intro g
  have hg := havoid (Sum.inr g)
  have hg' : threshold g <
      ((splitEquiv (H.groupSelectionSupport members (Sum.inr g)) S).1.card : ℝ) := by
    simpa [groupSelectionLocalBad, lowerTail, weightedSum, not_le] using hg
  rw [show
    ((splitEquiv (H.groupSelectionSupport members (Sum.inr g)) S).1.card : ℝ) =
      ((S ∩ members g).card : ℝ) by
        exact_mod_cast H.card_groupSelection_inside members g S] at hg'
  exact hg'

end WeightedEdgeColoring.RankThreeOptionSystem
