import WeightedEdgeColoring.RankThreeIsolatedNibble
import WeightedEdgeColoring.FiniteBernoulliQuadraticCollision
import WeightedEdgeColoring.FiniteBernoulliReadKCoverage
import WeightedEdgeColoring.FiniteBernoulliSupportSplit
import WeightedEdgeColoring.RankThreeDirectNibbleLLL

/-!
# Linear rows after deleting sampled conflicts

One can sample options without forbidding every conflicting pair and then
keep only the isolated sampled options.  This file gives the deterministic
accounting needed for that approach.  A nonnegative linear row loses at
most its oriented quadratic conflict charge.  The isolated set is always a
partial matching, so pair-conflict events need not occur in the local lemma.
-/

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliQuadraticMoment
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Total row weight charged to active conflicting neighbors, oriented from
the row coordinate to its blocker. -/
noncomputable def isolatedRowConflictCharge
    (weight : Option → ℝ) (S : Finset Option) : ℝ :=
  ∑ o ∈ S, weight o * (H.activeConflictCount S o : ℝ)

/-- Coefficient of one ordered conflict pair.  Only the left coordinate
carries row weight. -/
noncomputable def isolatedRowConflictPairWeight
    (weight : Option → ℝ) (e : OrderedPair Option) : ℝ :=
  if e.right ∈ H.conflictNeighbors e.left then weight e.left else 0

theorem isolatedOptions_subset (S : Finset Option) :
    H.isolatedOptions S ⊆ S := by
  intro o ho
  exact (H.mem_isolatedOptions.mp ho).1

/-- Every sampled option removed by isolation has at least one active
conflicting neighbor. -/
theorem one_le_activeConflictCount_of_mem_sdiff_isolated
    (S : Finset Option) {o : Option}
    (ho : o ∈ S \ H.isolatedOptions S) :
    1 ≤ H.activeConflictCount S o := by
  have hoS := (Finset.mem_sdiff.mp ho).1
  have hnot := (Finset.mem_sdiff.mp ho).2
  have hne : H.activeConflictCount S o ≠ 0 := by
    intro hz
    exact hnot ((H.mem_isolatedOptions_iff_activeConflictCount_zero S o).2
      ⟨hoS, hz⟩)
  exact Nat.one_le_iff_ne_zero.mpr hne

/-- The weight discarded by isolation is at most the oriented conflict
charge. -/
theorem weightedSum_sdiff_isolated_le_conflictCharge
    (weight : Option → ℝ) (hweight : ∀ o, 0 ≤ weight o)
    (S : Finset Option) :
    weightedSum weight (S \ H.isolatedOptions S) ≤
      H.isolatedRowConflictCharge weight S := by
  unfold weightedSum isolatedRowConflictCharge
  calc
    (∑ o ∈ S \ H.isolatedOptions S, weight o) ≤
        ∑ o ∈ S \ H.isolatedOptions S,
          weight o * (H.activeConflictCount S o : ℝ) := by
      apply Finset.sum_le_sum
      intro o ho
      have hone : (1 : ℝ) ≤ H.activeConflictCount S o := by
        exact_mod_cast H.one_le_activeConflictCount_of_mem_sdiff_isolated S ho
      nlinarith [mul_le_mul_of_nonneg_left hone (hweight o)]
    _ ≤ ∑ o ∈ S, weight o * (H.activeConflictCount S o : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro o _ho _hnot
      exact mul_nonneg (hweight o) (Nat.cast_nonneg _)

/-- Raw row weight is at most isolated row weight plus the conflict charge. -/
theorem weightedSum_le_isolated_add_conflictCharge
    (weight : Option → ℝ) (hweight : ∀ o, 0 ≤ weight o)
    (S : Finset Option) :
    weightedSum weight S ≤
      weightedSum weight (H.isolatedOptions S) +
        H.isolatedRowConflictCharge weight S := by
  have hpart := Finset.sum_sdiff
    (f := weight) (s₁ := H.isolatedOptions S) (s₂ := S)
    (H.isolatedOptions_subset S)
  have hloss := H.weightedSum_sdiff_isolated_le_conflictCharge
    weight hweight S
  unfold weightedSum at *
  linarith

/-- Equivalently, subtracting the conflict charge from a raw lower bound
leaves a valid lower bound after isolation. -/
theorem weightedSum_sub_conflictCharge_le_isolated
    (weight : Option → ℝ) (hweight : ∀ o, 0 ≤ weight o)
    (S : Finset Option) :
    weightedSum weight S - H.isolatedRowConflictCharge weight S ≤
      weightedSum weight (H.isolatedOptions S) := by
  linarith [H.weightedSum_le_isolated_add_conflictCharge weight hweight S]

/-- The oriented charge is exactly a nonnegative quadratic Bernoulli
statistic.  This is the bridge to the existing high-moment tail theorem. -/
theorem quadraticStatistic_isolatedRowConflictPairWeight
    (weight : Option → ℝ) (S : Finset Option) :
    quadraticStatistic (H.isolatedRowConflictPairWeight weight) S =
      H.isolatedRowConflictCharge weight S := by
  classical
  unfold quadraticStatistic monomialStatistic
  unfold isolatedRowConflictPairWeight isolatedRowConflictCharge
  simp only [OrderedPair.support, OrderedPair.left, OrderedPair.right]
  rw [sum_orderedPair_eq (g := fun a b ↦
    if ({a, b} : Finset Option) ⊆ S then
      if b ∈ H.conflictNeighbors a then weight a else 0
    else 0)]
  have hcharge :
      (∑ a ∈ S, weight a * (H.activeConflictCount S a : ℝ)) =
        ∑ a : Option, if a ∈ S then
          weight a * (H.activeConflictCount S a : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hcharge]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases haS : a ∈ S
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, haS,
      true_and]
    rw [show H.activeConflictCount S a =
        (S ∩ H.conflictNeighbors a).card by rfl]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
    have hfilter :
        (((Finset.univ : Finset Option).filter (fun b ↦ b ≠ a)).filter
            (fun b ↦ b ∈ S)).filter
              (fun b ↦ b ∈ H.conflictNeighbors a) =
          S ∩ H.conflictNeighbors a := by
      ext b
      constructor
      · intro hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        exact Finset.mem_inter.mpr ⟨hb.1.2, hb.2⟩
      · intro hb
        have hb' := Finset.mem_inter.mp hb
        have hbne : b ≠ a := (H.mem_conflictNeighbors.mp hb'.2).1
        exact Finset.mem_filter.mpr ⟨
          Finset.mem_filter.mpr ⟨
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbne⟩, hb'.1⟩,
          hb'.2⟩
    rw [← Finset.sum_filter, ← Finset.sum_filter, hfilter]
    simp
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, haS,
      false_and, if_false]
    simp [haS]

theorem isolatedRowConflictPairWeight_nonneg
    (weight : Option → ℝ) (hweight : ∀ o, 0 ≤ weight o)
    (e : OrderedPair Option) :
    0 ≤ H.isolatedRowConflictPairWeight weight e := by
  unfold isolatedRowConflictPairWeight
  split
  · exact hweight _
  · exact le_rfl

theorem isolatedRowConflictPairWeight_le
    (weight : Option → ℝ) (hweight : ∀ o, weight o ≤ 1)
    (e : OrderedPair Option) :
    H.isolatedRowConflictPairWeight weight e ≤ 1 := by
  unfold isolatedRowConflictPairWeight
  split
  · exact hweight _
  · norm_num

/-! ## Local support of one isolation-loss row -/

/-- The isolation loss of a row only reads a row coordinate and the
conflicting neighbours of row coordinates. -/
noncomputable def isolatedRowConflictSupport
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row) : Finset Option :=
  linearRowSupport weight r ∪
    (linearRowSupport weight r).biUnion H.conflictNeighbors

@[simp] theorem mem_isolatedRowConflictSupport_iff
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row) (o : Option) :
    o ∈ H.isolatedRowConflictSupport weight r ↔
      weight r o ≠ 0 ∨
        ∃ p, weight r p ≠ 0 ∧ o ∈ H.conflictNeighbors p := by
  simp [isolatedRowConflictSupport, linearRowSupport]

/-- Conflict-neighbourhood membership is symmetric. -/
theorem mem_conflictNeighbors_comm {o p : Option} :
    p ∈ H.conflictNeighbors o ↔ o ∈ H.conflictNeighbors p := by
  constructor
  · intro hp
    rcases H.mem_conflictNeighbors.mp hp with ⟨hpo, howner | hbad⟩
    · exact H.mem_conflictNeighbors.mpr
        ⟨hpo.symm, Or.inl howner.symm⟩
    · exact H.mem_conflictNeighbors.mpr
        ⟨hpo.symm, Or.inr (fun hcompat ↦
          hbad (H.compatible_symm.mpr hcompat))⟩
  · intro hp
    rcases H.mem_conflictNeighbors.mp hp with ⟨hop, howner | hbad⟩
    · exact H.mem_conflictNeighbors.mpr
        ⟨hop.symm, Or.inl howner.symm⟩
    · exact H.mem_conflictNeighbors.mpr
        ⟨hop.symm, Or.inr (fun hcompat ↦
          hbad (H.compatible_symm.mp hcompat))⟩

/-- The local support has the expected row-support times conflict-degree
bound. -/
theorem isolatedRowConflictSupport_card_le
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row) (L C : ℕ)
    (hrow : (linearRowSupport weight r).card ≤ L)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C) :
    (H.isolatedRowConflictSupport weight r).card ≤ L * (C + 1) := by
  unfold isolatedRowConflictSupport
  calc
    (linearRowSupport weight r ∪
        (linearRowSupport weight r).biUnion H.conflictNeighbors).card ≤
      (linearRowSupport weight r).card +
        ((linearRowSupport weight r).biUnion H.conflictNeighbors).card :=
      Finset.card_union_le _ _
    _ ≤ (linearRowSupport weight r).card +
        ∑ o ∈ linearRowSupport weight r,
          (H.conflictNeighbors o).card := by
      gcongr
      exact Finset.card_biUnion_le
    _ ≤ (linearRowSupport weight r).card +
        ∑ _o ∈ linearRowSupport weight r, C := by
      gcongr with o ho
      exact hconflict o
    _ = (linearRowSupport weight r).card * (C + 1) := by
      simp
      ring
    _ ≤ L * (C + 1) := Nat.mul_le_mul_right (C + 1) hrow

/-- Isolation-loss rows whose enlarged support contains one coordinate. -/
noncomputable def isolatedRowConflictIncidence
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (o : Option) : Finset Row :=
  Finset.univ.filter fun r ↦ o ∈ H.isolatedRowConflictSupport weight r

/-- Enlarging every row by all conflict neighbours multiplies its
per-coordinate incidence by at most `C+1`. -/
theorem isolatedRowConflictIncidence_card_le
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (R C : ℕ)
    (hrowIncidence : ∀ o, (linearRowIncidence weight o).card ≤ R)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (o : Option) :
    (H.isolatedRowConflictIncidence weight o).card ≤ (C + 1) * R := by
  let P : Finset Option := insert o (H.conflictNeighbors o)
  have hsub : H.isolatedRowConflictIncidence weight o ⊆
      P.biUnion (linearRowIncidence weight) := by
    intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    rw [H.mem_isolatedRowConflictSupport_iff] at hr'
    rcases hr' with hro | ⟨p, hrp, hop⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨o, Finset.mem_insert_self o _, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ r, by simpa [linearRowSupport] using hro⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨p, Finset.mem_insert_of_mem
        ((H.mem_conflictNeighbors_comm).mpr hop), ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ r, by simpa [linearRowSupport] using hrp⟩
  calc
    (H.isolatedRowConflictIncidence weight o).card ≤
        (P.biUnion (linearRowIncidence weight)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (linearRowIncidence weight p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, R := by
      exact Finset.sum_le_sum fun p _ ↦ hrowIncidence p
    _ = P.card * R := by simp
    _ ≤ (C + 1) * R := by
      gcongr
      calc
        P.card ≤ (H.conflictNeighbors o).card + 1 :=
          Finset.card_insert_le o _
        _ ≤ C + 1 := Nat.add_le_add_right (hconflict o) 1

/-- Every nonzero oriented conflict coefficient has both endpoints in the
enlarged row support. -/
theorem isolatedRowConflictPairWeight_support
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row)
    (e : OrderedPair Option)
    (he : H.isolatedRowConflictPairWeight (weight r) e ≠ 0) :
    e.support ⊆ H.isolatedRowConflictSupport weight r := by
  have hright : e.right ∈ H.conflictNeighbors e.left := by
    by_contra hnot
    simp [isolatedRowConflictPairWeight, hnot] at he
  have hleftWeight : weight r e.left ≠ 0 := by
    simpa [isolatedRowConflictPairWeight, hright] using he
  intro o ho
  simp only [OrderedPair.support, Finset.mem_insert,
    Finset.mem_singleton] at ho
  rcases ho with rfl | rfl
  · exact (H.mem_isolatedRowConflictSupport_iff weight r e.left).2
      (Or.inl hleftWeight)
  · exact (H.mem_isolatedRowConflictSupport_iff weight r e.right).2
      (Or.inr ⟨e.left, hleftWeight, hright⟩)

/-- Coordinates outside the enlarged support do not affect the quadratic
isolation-loss statistic. -/
theorem quadraticStatistic_inter_isolatedRowConflictSupport
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row) (S : Finset Option) :
    quadraticStatistic (H.isolatedRowConflictPairWeight (weight r))
        (S ∩ H.isolatedRowConflictSupport weight r) =
      quadraticStatistic (H.isolatedRowConflictPairWeight (weight r)) S := by
  classical
  unfold quadraticStatistic monomialStatistic
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hw : H.isolatedRowConflictPairWeight (weight r) e = 0
  · simp [hw]
  · have hsupp := H.isolatedRowConflictPairWeight_support weight r e hw
    by_cases heS : e.support ⊆ S
    · have hinter : e.support ⊆
          S ∩ H.isolatedRowConflictSupport weight r := fun o ho ↦
        Finset.mem_inter.mpr ⟨heS ho, hsupp ho⟩
      simp [heS, hinter]
    · have hnotInter : ¬ e.support ⊆
          S ∩ H.isolatedRowConflictSupport weight r := fun h ↦
        heS (fun o ho ↦ (Finset.mem_inter.mp (h ho)).1)
      simp [heS, hnotInter]

/-- Local statistic obtained by setting all coordinates outside the
enlarged row support to zero. -/
noncomputable def isolatedRowConflictLocalStatistic
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row)
    (A : Finset (Inside (H.isolatedRowConflictSupport weight r))) : ℝ :=
  quadraticStatistic (H.isolatedRowConflictPairWeight (weight r))
    ((splitEquiv (H.isolatedRowConflictSupport weight r)).symm (A, ∅))

/-- Local increasing bad event saying that isolation destroys more than
`T` units of row weight. -/
noncomputable def isolatedRowConflictLocalBad
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row) (T : ℝ) :
    Finset (Finset (Inside (H.isolatedRowConflictSupport weight r))) :=
  upperTail (H.isolatedRowConflictLocalStatistic weight r) T

private theorem zeroOutside_isolatedRow_inside_eq_inter
    (K S : Finset Option) :
    (splitEquiv K).symm ((splitEquiv K S).1, ∅) = S ∩ K := by
  classical
  ext p
  by_cases hpK : p ∈ K
  · let pi : Inside K := ⟨p, hpK⟩
    calc
      p ∈ (splitEquiv K).symm ((splitEquiv K S).1, ∅) ↔
          pi ∈ (splitEquiv K S).1 := by
            simpa [pi] using
              (mem_splitEquiv_symm_inside K (splitEquiv K S).1 ∅ pi)
      _ ↔ p ∈ S := by simpa [pi] using mem_splitEquiv_inside K S pi
      _ ↔ p ∈ S ∩ K := by simp [hpK]
  · let po : Outside K := ⟨p, hpK⟩
    calc
      p ∈ (splitEquiv K).symm ((splitEquiv K S).1, ∅) ↔
          po ∈ (∅ : Finset (Outside K)) := by
            simpa [po] using
              (mem_splitEquiv_symm_outside K (splitEquiv K S).1 ∅ po)
      _ ↔ p ∈ S ∩ K := by simp [hpK]

/-- The local cylinder is exactly the global isolation-loss upper tail. -/
theorem insideCylinder_isolatedRowConflictLocalBad
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row) (T : ℝ) :
    insideCylinder (H.isolatedRowConflictSupport weight r)
        (H.isolatedRowConflictLocalBad weight r T) =
      upperTail (quadraticStatistic
        (H.isolatedRowConflictPairWeight (weight r))) T := by
  classical
  ext S
  simp only [mem_insideCylinder, isolatedRowConflictLocalBad, upperTail,
    Finset.mem_filter, Finset.mem_univ, true_and,
    isolatedRowConflictLocalStatistic]
  rw [zeroOutside_isolatedRow_inside_eq_inter
    (H.isolatedRowConflictSupport weight r) S]
  rw [H.quadraticStatistic_inter_isolatedRowConflictSupport weight r S]

/-- The local and global isolation-loss tails have equal Bernoulli mass. -/
theorem isolatedRowConflictLocalBad_mass_eq_global
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (weight : Row → Option → ℝ)
    (r : Row) (T : ℝ) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.isolatedRowConflictSupport weight r)))
        (H.isolatedRowConflictLocalBad weight r T) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (upperTail (quadraticStatistic
          (H.isolatedRowConflictPairWeight (weight r))) T) := by
  rw [← H.insideCylinder_isolatedRowConflictLocalBad weight r T]
  exact (WeightedEdgeColoring.FiniteBernoulliReadKCoverage.eventMass_insideCylinder
    q (H.isolatedRowConflictSupport weight r)
      (H.isolatedRowConflictLocalBad weight r T)).symm

/-- Evaluating the local statistic on the inside part of a global outcome
recovers the global isolation-loss statistic. -/
theorem isolatedRowConflictLocalStatistic_split_eq_global
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row) (S : Finset Option) :
    H.isolatedRowConflictLocalStatistic weight r
        (splitEquiv (H.isolatedRowConflictSupport weight r) S).1 =
      quadraticStatistic
        (H.isolatedRowConflictPairWeight (weight r)) S := by
  unfold isolatedRowConflictLocalStatistic
  rw [zeroOutside_isolatedRow_inside_eq_inter
    (H.isolatedRowConflictSupport weight r) S]
  exact H.quadraticStatistic_inter_isolatedRowConflictSupport weight r S

/-- Avoiding the local bad event gives the promised deterministic upper
bound on the row weight destroyed by isolation. -/
theorem isolatedRowConflictCharge_le_of_not_localBad
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row)
    (S : Finset Option) (T : ℝ)
    (hgood : (splitEquiv (H.isolatedRowConflictSupport weight r) S).1 ∉
      H.isolatedRowConflictLocalBad weight r T) :
    H.isolatedRowConflictCharge (weight r) S ≤ T := by
  have hlocal : H.isolatedRowConflictLocalStatistic weight r
      (splitEquiv (H.isolatedRowConflictSupport weight r) S).1 ≤ T := by
    have hlt : H.isolatedRowConflictLocalStatistic weight r
        (splitEquiv (H.isolatedRowConflictSupport weight r) S).1 < T := by
      simpa [isolatedRowConflictLocalBad, upperTail] using hgood
    exact hlt.le
  rw [← H.quadraticStatistic_isolatedRowConflictPairWeight (weight r) S]
  rw [← H.isolatedRowConflictLocalStatistic_split_eq_global weight r S]
  exact hlocal

/-- A raw lower bound with an added isolation-loss margin remains a strict
lower bound after taking isolated options. -/
theorem target_lt_isolated_weightedSum_of_raw_and_not_localBad
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ)
    (hweight : ∀ r o, 0 ≤ weight r o)
    (r : Row) (S : Finset Option) (target T : ℝ)
    (hraw : target + T < weightedSum (weight r) S)
    (hgood : (splitEquiv (H.isolatedRowConflictSupport weight r) S).1 ∉
      H.isolatedRowConflictLocalBad weight r T) :
    target < weightedSum (weight r) (H.isolatedOptions S) := by
  have hloss := H.isolatedRowConflictCharge_le_of_not_localBad
    weight r S T hgood
  have htransfer := H.weightedSum_sub_conflictCharge_le_isolated
    (weight r) (hweight r) S
  linarith

/-- Isolation can only decrease a nonnegative upper row. -/
theorem isolated_weightedSum_le_raw
    (weight : Option → ℝ) (hweight : ∀ o, 0 ≤ weight o)
    (S : Finset Option) :
    weightedSum weight (H.isolatedOptions S) ≤ weightedSum weight S := by
  unfold weightedSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (H.isolatedOptions_subset S)
  intro o _ho _hnot
  exact hweight o

/-- A nonnegative quadratic statistic increases when coordinates are added. -/
theorem quadraticStatistic_isolatedRowConflictPairWeight_mono
    (weight : Option → ℝ) (hweight : ∀ o, 0 ≤ weight o) :
    Monotone (quadraticStatistic
      (H.isolatedRowConflictPairWeight weight)) := by
  intro S T hST
  unfold quadraticStatistic monomialStatistic
  apply Finset.sum_le_sum
  intro e _he
  have hw0 := H.isolatedRowConflictPairWeight_nonneg weight hweight e
  by_cases heS : e.support ⊆ S
  · have heT : e.support ⊆ T := fun o ho ↦ hST (heS ho)
    simp [heS, heT]
  · simp [heS]
    split
    · exact hw0
    · exact le_rfl

/-- Isolation-loss local bad events are increasing. -/
theorem isolatedRowConflictLocalBad_isIncreasing
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ)
    (hweight : ∀ r o, 0 ≤ weight r o) (r : Row) (T : ℝ) :
    WeightedEdgeColoring.FiniteBernoulliHarris.IsIncreasing
      (H.isolatedRowConflictLocalBad weight r T) := by
  intro A hA B hAB
  simp only [isolatedRowConflictLocalBad, upperTail, Finset.mem_filter,
    Finset.mem_univ, true_and, isolatedRowConflictLocalStatistic] at hA ⊢
  apply hA.trans
  apply H.quadraticStatistic_isolatedRowConflictPairWeight_mono
    (weight r) (hweight r)
  intro p hp
  by_cases hpK : p ∈ H.isolatedRowConflictSupport weight r
  · let pi : Inside (H.isolatedRowConflictSupport weight r) := ⟨p, hpK⟩
    have hpiA : pi ∈ A := by
      simpa [pi] using
        (mem_splitEquiv_symm_inside
          (H.isolatedRowConflictSupport weight r) A ∅ pi).mp hp
    have hpiB := hAB hpiA
    simpa [pi] using
      (mem_splitEquiv_symm_inside
        (H.isolatedRowConflictSupport weight r) B ∅ pi).mpr hpiB
  · let po : Outside (H.isolatedRowConflictSupport weight r) := ⟨p, hpK⟩
    have : po ∈ (∅ : Finset
        (Outside (H.isolatedRowConflictSupport weight r))) := by
      simpa [po] using
        (mem_splitEquiv_symm_outside
          (H.isolatedRowConflictSupport weight r) A ∅ po).mp hp
    simp at this

/-! ## Moment bounds for one isolation-loss row -/

/-- Uniform proposal probabilities and a conflict-degree bound control one
option's conflict load. -/
theorem conflictLoad_le_qmax_mul
    (q : Option → ℝ) (qmax : ℝ) (C : ℕ)
    (hq : ∀ o, q o ≤ qmax) (hqmax0 : 0 ≤ qmax)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (o : Option) :
    H.conflictLoad q o ≤ qmax * C := by
  unfold conflictLoad
  calc
    (∑ p ∈ H.conflictNeighbors o, q p) ≤
        ∑ _p ∈ H.conflictNeighbors o, qmax := by
      exact Finset.sum_le_sum fun p _ ↦ hq p
    _ = (H.conflictNeighbors o).card * qmax := by simp
    _ ≤ C * qmax := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast hconflict o) hqmax0
    _ = qmax * C := by ring

/-- A row bounded by one has total weight at most the size of its support. -/
theorem sum_weight_le_linearRowSupport_card
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (weight : Row → Option → ℝ) (r : Row)
    (hweight0 : ∀ o, 0 ≤ weight r o)
    (hweight1 : ∀ o, weight r o ≤ 1) :
    (∑ o : Option, weight r o) ≤
      (linearRowSupport weight r).card := by
  calc
    (∑ o : Option, weight r o) =
        ∑ o ∈ linearRowSupport weight r, weight r o := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro o _ho hnot
      have : weight r o = 0 := by
        simpa [linearRowSupport] using hnot
      simp [this]
    _ ≤ ∑ _o ∈ linearRowSupport weight r, (1 : ℝ) := by
      exact Finset.sum_le_sum fun o _ ↦ hweight1 o
    _ = (linearRowSupport weight r).card := by simp

/-- Exact first-moment identity for the oriented isolation-loss statistic. -/
theorem quadraticMean_isolatedRowConflictPairWeight
    (q weight : Option → ℝ) :
    quadraticMean q (H.isolatedRowConflictPairWeight weight) =
      ∑ o : Option, weight o * q o * H.conflictLoad q o := by
  classical
  unfold quadraticMean isolatedRowConflictPairWeight
  simp only [OrderedPair.left, OrderedPair.right]
  rw [sum_orderedPair_eq (g := fun a b ↦
    (if b ∈ H.conflictNeighbors a then weight a else 0) * q a * q b)]
  apply Finset.sum_congr rfl
  intro o _ho
  unfold conflictLoad
  rw [Finset.mul_sum]
  have hfilter :
      ((Finset.univ : Finset Option).filter (fun p ↦ p ≠ o)).filter
          (fun p ↦ p ∈ H.conflictNeighbors o) =
        H.conflictNeighbors o := by
    ext p
    constructor
    · intro hp
      exact (Finset.mem_filter.mp hp).2
    · intro hp
      have hpo : p ≠ o := (H.mem_conflictNeighbors.mp hp).1
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpo⟩, hp⟩
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter, hfilter]

/-- Closed first-moment bound in terms of row support and conflict degree. -/
theorem quadraticMean_isolatedRowConflictPairWeight_le
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (qmax : ℝ)
    (weight : Row → Option → ℝ) (r : Row) (L C : ℕ)
    (hq0 : ∀ o, 0 ≤ q o) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight r o)
    (hweight1 : ∀ o, weight r o ≤ 1)
    (hrow : (linearRowSupport weight r).card ≤ L)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C) :
    quadraticMean q (H.isolatedRowConflictPairWeight (weight r)) ≤
      qmax ^ 2 * (L * C : ℕ) := by
  rw [H.quadraticMean_isolatedRowConflictPairWeight q (weight r)]
  have hload : ∀ o, H.conflictLoad q o ≤ qmax * C :=
    H.conflictLoad_le_qmax_mul q qmax C hqmax hqmax0 hconflict
  calc
    (∑ o : Option, weight r o * q o * H.conflictLoad q o) ≤
        ∑ o : Option, weight r o * qmax * (qmax * C) := by
      apply Finset.sum_le_sum
      intro o _ho
      have hload0 : 0 ≤ H.conflictLoad q o :=
        Finset.sum_nonneg fun p _ ↦ hq0 p
      calc
        weight r o * q o * H.conflictLoad q o ≤
            weight r o * qmax * H.conflictLoad q o := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hqmax o) (hweight0 o)) hload0
        _ ≤ weight r o * qmax * (qmax * C) := by
          exact mul_le_mul_of_nonneg_left (hload o)
            (mul_nonneg (hweight0 o) hqmax0)
    _ = ∑ o : Option, qmax ^ 2 * C * weight r o := by
      apply Finset.sum_congr rfl
      intro o _ho
      ring
    _ = qmax ^ 2 * C * ∑ o : Option, weight r o := by
      rw [Finset.mul_sum]
    _ ≤ qmax ^ 2 * C * (linearRowSupport weight r).card := by
      gcongr
      exact sum_weight_le_linearRowSupport_card weight r hweight0 hweight1
    _ ≤ qmax ^ 2 * C * L := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hrow
      · positivity
    _ = qmax ^ 2 * (L * C : ℕ) := by
      push_cast
      ring

/-- Sharper first-moment bound using the total row weight instead of the
cardinality of its support.  This retains normalization factors such as the
`1/(3*lambda)` in a slot-deletion row. -/
theorem quadraticMean_isolatedRowConflictPairWeight_le_weightSum
    (q : Option → ℝ) (qmax : ℝ) (weight : Option → ℝ)
    (C : ℕ) (W : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight o)
    (hweightSum : (∑ o : Option, weight o) ≤ W)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C) :
    quadraticMean q (H.isolatedRowConflictPairWeight weight) ≤
      qmax ^ 2 * C * W := by
  rw [H.quadraticMean_isolatedRowConflictPairWeight q weight]
  have hload : ∀ o, H.conflictLoad q o ≤ qmax * C :=
    H.conflictLoad_le_qmax_mul q qmax C hqmax hqmax0 hconflict
  calc
    (∑ o : Option, weight o * q o * H.conflictLoad q o) ≤
        ∑ o : Option, weight o * qmax * (qmax * C) := by
      apply Finset.sum_le_sum
      intro o _ho
      have hload0 : 0 ≤ H.conflictLoad q o :=
        Finset.sum_nonneg fun p _ ↦ hq0 p
      calc
        weight o * q o * H.conflictLoad q o ≤
            weight o * qmax * H.conflictLoad q o := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hqmax o) (hweight0 o)) hload0
        _ ≤ weight o * qmax * (qmax * C) := by
          exact mul_le_mul_of_nonneg_left (hload o)
            (mul_nonneg (hweight0 o) hqmax0)
    _ = ∑ o : Option, qmax ^ 2 * C * weight o := by
      apply Finset.sum_congr rfl
      intro o _ho
      ring
    _ = qmax ^ 2 * C * ∑ o : Option, weight o := by
      rw [Finset.mul_sum]
    _ ≤ qmax ^ 2 * C * W := by
      exact mul_le_mul_of_nonneg_left hweightSum (by positivity)

/-- The outgoing half of the incident load is one row weight times the
conflict load. -/
theorem isolatedRowConflict_leftIncident_eq
    (q weight : Option → ℝ) (i : Option) :
    (∑ e : OrderedPair Option,
      if e.left = i then
        H.isolatedRowConflictPairWeight weight e * q e.right else 0) =
      weight i * H.conflictLoad q i := by
  classical
  unfold isolatedRowConflictPairWeight
  simp only [OrderedPair.left, OrderedPair.right]
  rw [sum_orderedPair_eq (g := fun a b ↦
    if a = i then
      (if b ∈ H.conflictNeighbors a then weight a else 0) * q b else 0)]
  rw [Finset.sum_eq_single i]
  · unfold conflictLoad
    have hfilter :
        ((Finset.univ : Finset Option).filter (fun p ↦ p ≠ i)).filter
            (fun p ↦ p ∈ H.conflictNeighbors i) =
          H.conflictNeighbors i := by
      ext p
      constructor
      · intro hp
        exact (Finset.mem_filter.mp hp).2
      · intro hp
        have hpi : p ≠ i := (H.mem_conflictNeighbors.mp hp).1
        exact Finset.mem_filter.mpr ⟨
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩, hp⟩
    rw [Finset.mul_sum]
    simp only [if_true, Finset.filter_true]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter, hfilter]
  · intro a _ha hai
    simp [hai]
  · simp

/-- By symmetry of conflicts, the incoming half is the weighted proposal
mass of the same conflict neighbourhood. -/
theorem isolatedRowConflict_rightIncident_eq
    (q weight : Option → ℝ) (i : Option) :
    (∑ e : OrderedPair Option,
      if e.right = i then
        H.isolatedRowConflictPairWeight weight e * q e.left else 0) =
      ∑ o ∈ H.conflictNeighbors i, weight o * q o := by
  classical
  unfold isolatedRowConflictPairWeight
  simp only [OrderedPair.left, OrderedPair.right]
  rw [sum_orderedPair_eq (g := fun a b ↦
    if b = i then
      (if b ∈ H.conflictNeighbors a then weight a else 0) * q a else 0)]
  calc
    (∑ a : Option, ∑ b ∈ (Finset.univ : Finset Option).filter (fun b ↦ b ≠ a),
        if b = i then
          (if b ∈ H.conflictNeighbors a then weight a else 0) * q a else 0) =
        ∑ a : Option,
          if a ∈ H.conflictNeighbors i then weight a * q a else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hai : a = i
      · subst a
        simp
      · have hfilter : i ∈
            (Finset.univ : Finset Option).filter (fun b ↦ b ≠ a) := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h ↦ hai h.symm⟩
        rw [Finset.sum_eq_single i]
        · by_cases haN : a ∈ H.conflictNeighbors i
          · have hiN : i ∈ H.conflictNeighbors a :=
              (H.mem_conflictNeighbors_comm).mpr haN
            simp [haN, hiN]
          · have hiN : i ∉ H.conflictNeighbors a := by
              intro h
              exact haN ((H.mem_conflictNeighbors_comm).mp h)
            simp [haN, hiN]
        · intro b hb hbi
          simp [hbi]
        · intro hnot
          exact False.elim (hnot hfilter)
    _ = ∑ o ∈ H.conflictNeighbors i, weight o * q o := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ : Finset Option).filter
              (fun o ↦ o ∈ H.conflictNeighbors i) =
            H.conflictNeighbors i := by
        ext o
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hfilter]

/-- Full incident-load bound for an isolation-loss row. -/
theorem incidentLoad_isolatedRowConflictPairWeight_le
    (q weight : Option → ℝ) (qmax : ℝ) (C : ℕ)
    (hq0 : ∀ o, 0 ≤ q o) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight o)
    (hweight1 : ∀ o, weight o ≤ 1)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (i : Option) :
    incidentLoad q (H.isolatedRowConflictPairWeight weight) i ≤
      2 * qmax * C := by
  unfold incidentLoad
  rw [H.isolatedRowConflict_leftIncident_eq,
    H.isolatedRowConflict_rightIncident_eq]
  have hload0 : 0 ≤ H.conflictLoad q i := by
    exact Finset.sum_nonneg fun p _ ↦ hq0 p
  have hout : weight i * H.conflictLoad q i ≤ qmax * C := by
    calc
      weight i * H.conflictLoad q i ≤
          1 * H.conflictLoad q i :=
        mul_le_mul_of_nonneg_right (hweight1 i) hload0
      _ ≤ qmax * C := by
        simpa using H.conflictLoad_le_qmax_mul
          q qmax C hqmax hqmax0 hconflict i
  have hin : (∑ o ∈ H.conflictNeighbors i, weight o * q o) ≤
      qmax * C := by
    calc
      (∑ o ∈ H.conflictNeighbors i, weight o * q o) ≤
          ∑ _o ∈ H.conflictNeighbors i, qmax := by
        apply Finset.sum_le_sum
        intro o _ho
        calc
          weight o * q o ≤ 1 * q o :=
            mul_le_mul_of_nonneg_right (hweight1 o) (hq0 o)
          _ ≤ qmax := by simpa using hqmax o
      _ = (H.conflictNeighbors i).card * qmax := by simp
      _ ≤ C * qmax := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hconflict i) hqmax0
      _ = qmax * C := by ring
  linarith

/-- Explicit moment envelope for the isolation loss of a row with support
at most `L` and conflict degree at most `C`. -/
noncomputable def isolatedRowConflictMomentEnvelope
    (qmax : ℝ) (L C k : ℕ) : ℝ :=
  qmax ^ 2 * (L * C : ℕ) +
    2 * k * (2 * qmax * C) + 4 * k ^ 2

/-- Weight-sensitive envelope, sharper for normalized deletion rows. -/
noncomputable def isolatedRowConflictWeightedMomentEnvelope
    (qmax W : ℝ) (C k : ℕ) : ℝ :=
  qmax ^ 2 * C * W + 2 * k * (2 * qmax * C) + 4 * k ^ 2

theorem isolatedRowConflictMomentEnvelope_nonneg
    (qmax : ℝ) (L C k : ℕ) (hqmax0 : 0 ≤ qmax) :
    0 ≤ isolatedRowConflictMomentEnvelope qmax L C k := by
  unfold isolatedRowConflictMomentEnvelope
  positivity

theorem isolatedRowConflictWeightedMomentEnvelope_nonneg
    (qmax W : ℝ) (C k : ℕ) (hqmax0 : 0 ≤ qmax) (hW0 : 0 ≤ W) :
    0 ≤ isolatedRowConflictWeightedMomentEnvelope qmax W C k := by
  unfold isolatedRowConflictWeightedMomentEnvelope
  positivity

/-- Global high-moment tail for the row weight lost to isolation. -/
theorem isolatedRowConflict_tail_mul_le
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (qmax : ℝ)
    (weight : Row → Option → ℝ) (r : Row)
    (L C k : ℕ) (T : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight r o)
    (hweight1 : ∀ o, weight r o ≤ 1)
    (hrow : (linearRowSupport weight r).card ≤ L)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (hT : 0 ≤ T) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (upperTail (quadraticStatistic
          (H.isolatedRowConflictPairWeight (weight r))) T) ≤
      (isolatedRowConflictMomentEnvelope qmax L C k) ^ k := by
  have htail := quadratic_tail_mul_le_explicit q
    (H.isolatedRowConflictPairWeight (weight r)) k T
    (qmax ^ 2 * (L * C : ℕ)) (2 * qmax * C) 1
    hq0 hq1
    (H.isolatedRowConflictPairWeight_nonneg (weight r) hweight0)
    (H.isolatedRowConflictPairWeight_le (weight r) hweight1)
    (H.quadraticMean_isolatedRowConflictPairWeight_le
      q qmax weight r L C hq0 hqmax0 hqmax hweight0 hweight1 hrow hconflict)
    (H.incidentLoad_isolatedRowConflictPairWeight_le
      q (weight r) qmax C hq0 hqmax0 hqmax hweight0 hweight1 hconflict)
    hT (by positivity) (by positivity) (by norm_num)
  simpa [isolatedRowConflictMomentEnvelope] using htail

/-- The same high-moment tail for the local cylinder event used by Harris. -/
theorem isolatedRowConflictLocalBad_tail_mul_le
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (qmax : ℝ)
    (weight : Row → Option → ℝ) (r : Row)
    (L C k : ℕ) (T : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight r o)
    (hweight1 : ∀ o, weight r o ≤ 1)
    (hrow : (linearRowSupport weight r).card ≤ L)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (hT : 0 ≤ T) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.isolatedRowConflictSupport weight r)))
        (H.isolatedRowConflictLocalBad weight r T) ≤
      (isolatedRowConflictMomentEnvelope qmax L C k) ^ k := by
  rw [H.isolatedRowConflictLocalBad_mass_eq_global q weight r T]
  exact H.isolatedRowConflict_tail_mul_le q qmax weight r L C k T
    hq0 hq1 hqmax0 hqmax hweight0 hweight1 hrow hconflict hT

/-- A convenient exponentially small bound when the moment envelope is at
most half the allowed isolation loss. -/
theorem isolatedRowConflictLocalBad_mass_le_half_pow
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (qmax : ℝ)
    (weight : Row → Option → ℝ) (r : Row)
    (L C k : ℕ) (T : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight r o)
    (hweight1 : ∀ o, weight r o ≤ 1)
    (hrow : (linearRowSupport weight r).card ≤ L)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (hT : 0 < T)
    (henvelope : isolatedRowConflictMomentEnvelope qmax L C k ≤ T / 2) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.isolatedRowConflictSupport weight r)))
        (H.isolatedRowConflictLocalBad weight r T) ≤
      (1 / 2 : ℝ) ^ k := by
  have hraw := H.isolatedRowConflictLocalBad_tail_mul_le
    q qmax weight r L C k T hq0 hq1 hqmax0 hqmax
    hweight0 hweight1 hrow hconflict hT.le
  have henv0 := isolatedRowConflictMomentEnvelope_nonneg
    qmax L C k hqmax0
  have hpow : isolatedRowConflictMomentEnvelope qmax L C k ^ k ≤
      (T / 2) ^ k := pow_le_pow_left₀ henv0 henvelope k
  have hmul :
      T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass
            (insideParameter q (H.isolatedRowConflictSupport weight r)))
          (H.isolatedRowConflictLocalBad weight r T) ≤
        T ^ k * (1 / 2 : ℝ) ^ k := by
    calc
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.isolatedRowConflictSupport weight r)))
        (H.isolatedRowConflictLocalBad weight r T) ≤
      isolatedRowConflictMomentEnvelope qmax L C k ^ k := hraw
    _ ≤ (T / 2) ^ k := hpow
    _ = T ^ k * (1 / 2 : ℝ) ^ k := by ring
  exact le_of_mul_le_mul_left hmul (pow_pos hT k)

/-- Weight-sensitive local tail.  Unlike the support-cardinality version,
its first-moment term keeps any normalization present in the row. -/
theorem isolatedRowConflictLocalBad_tail_mul_le_weightSum
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (qmax : ℝ)
    (weight : Row → Option → ℝ) (r : Row)
    (C k : ℕ) (W T : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight r o)
    (hweight1 : ∀ o, weight r o ≤ 1)
    (hweightSum : (∑ o : Option, weight r o) ≤ W)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (hT : 0 ≤ T) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.isolatedRowConflictSupport weight r)))
        (H.isolatedRowConflictLocalBad weight r T) ≤
      (isolatedRowConflictWeightedMomentEnvelope qmax W C k) ^ k := by
  rw [H.isolatedRowConflictLocalBad_mass_eq_global q weight r T]
  have htail := quadratic_tail_mul_le_explicit q
    (H.isolatedRowConflictPairWeight (weight r)) k T
    (qmax ^ 2 * C * W) (2 * qmax * C) 1
    hq0 hq1
    (H.isolatedRowConflictPairWeight_nonneg (weight r) hweight0)
    (H.isolatedRowConflictPairWeight_le (weight r) hweight1)
    (H.quadraticMean_isolatedRowConflictPairWeight_le_weightSum
      q qmax (weight r) C W hq0 hqmax0 hqmax hweight0 hweightSum hconflict)
    (H.incidentLoad_isolatedRowConflictPairWeight_le
      q (weight r) qmax C hq0 hqmax0 hqmax hweight0 hweight1 hconflict)
    hT
    (by
      have hsum0 : 0 ≤ ∑ o : Option, weight r o :=
        Finset.sum_nonneg fun o _ ↦ hweight0 o
      have hW0 : 0 ≤ W := hsum0.trans hweightSum
      positivity)
    (by positivity) (by norm_num)
  simpa [isolatedRowConflictWeightedMomentEnvelope] using htail

/-- Half-power corollary of the weight-sensitive envelope. -/
theorem isolatedRowConflictLocalBad_mass_le_half_pow_weightSum
    {Row : Type x} [Fintype Row] [DecidableEq Row]
    (q : Option → ℝ) (qmax : ℝ)
    (weight : Row → Option → ℝ) (r : Row)
    (C k : ℕ) (W T : ℝ)
    (hq0 : ∀ o, 0 ≤ q o) (hq1 : ∀ o, q o ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ o, q o ≤ qmax)
    (hweight0 : ∀ o, 0 ≤ weight r o)
    (hweight1 : ∀ o, weight r o ≤ 1)
    (hweightSum : (∑ o : Option, weight r o) ≤ W)
    (hconflict : ∀ o, (H.conflictNeighbors o).card ≤ C)
    (hT : 0 < T)
    (henvelope :
      isolatedRowConflictWeightedMomentEnvelope qmax W C k ≤ T / 2) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.isolatedRowConflictSupport weight r)))
        (H.isolatedRowConflictLocalBad weight r T) ≤
      (1 / 2 : ℝ) ^ k := by
  have hraw := H.isolatedRowConflictLocalBad_tail_mul_le_weightSum
    q qmax weight r C k W T hq0 hq1 hqmax0 hqmax
      hweight0 hweight1 hweightSum hconflict hT.le
  have hsum0 : 0 ≤ ∑ o : Option, weight r o :=
    Finset.sum_nonneg fun o _ ↦ hweight0 o
  have hW0 : 0 ≤ W := hsum0.trans hweightSum
  have henv0 := isolatedRowConflictWeightedMomentEnvelope_nonneg
    qmax W C k hqmax0 hW0
  have hpow : isolatedRowConflictWeightedMomentEnvelope qmax W C k ^ k ≤
      (T / 2) ^ k := pow_le_pow_left₀ henv0 henvelope k
  have hmul :
      T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass
            (insideParameter q (H.isolatedRowConflictSupport weight r)))
          (H.isolatedRowConflictLocalBad weight r T) ≤
        T ^ k * (1 / 2 : ℝ) ^ k := by
    calc
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass
          (insideParameter q (H.isolatedRowConflictSupport weight r)))
        (H.isolatedRowConflictLocalBad weight r T) ≤
      isolatedRowConflictWeightedMomentEnvelope qmax W C k ^ k := hraw
    _ ≤ (T / 2) ^ k := hpow
    _ = T ^ k * (1 / 2 : ℝ) ^ k := by ring
  exact le_of_mul_le_mul_left hmul (pow_pos hT k)

end RankThreeOptionSystem
end WeightedEdgeColoring
