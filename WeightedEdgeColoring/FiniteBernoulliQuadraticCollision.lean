import WeightedEdgeColoring.FiniteBernoulliQuadraticMoment
import WeightedEdgeColoring.RankThreeResidualCollisionBounds

/-!
# Ordered quadratic moments for pair intersections

This file identifies the generic ordered quadratic statistic with the
ordered pair-collision statistic and supplies its mean, incident-load, and
maximum-coefficient bounds.
-/

namespace WeightedEdgeColoring.FiniteBernoulliQuadraticMoment

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff

variable {I X : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

/-- Intersection size attached to an ordered pair of distinct indices. -/
noncomputable def pairIntersectionWeight (F : I → Finset X)
    (e : OrderedPair I) : ℝ :=
  ((F e.left ∩ F e.right).card : ℝ)

/-- Reindex a sum over ordered distinct pairs as two ordinary finite sums. -/
theorem sum_orderedPair_eq (g : I → I → ℝ) :
    (∑ e : OrderedPair I, g e.1.1 e.1.2) =
      ∑ a : I, ∑ b ∈ (Finset.univ : Finset I).filter (fun b ↦ b ≠ a),
        g a b := by
  classical
  let s : Finset (I × I) :=
    (Finset.univ : Finset (I × I)).filter fun ab ↦ ab.1 ≠ ab.2
  calc
    (∑ e : OrderedPair I, g e.left e.right) =
        ∑ ab ∈ s, g ab.1 ab.2 := by
      symm
      exact Finset.sum_subtype s (fun ab ↦ by simp [s])
        (fun ab ↦ g ab.1 ab.2)
    _ = ∑ a : I, ∑ b ∈
        (Finset.univ : Finset I).filter (fun b ↦ b ≠ a), g a b := by
      dsimp [s]
      rw [Finset.sum_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : b = a
      · subst b
        simp
      · have hba : a ≠ b := Ne.symm hab
        simp [hab, hba]

/-- The generic ordered quadratic polynomial is exactly the cast of the
pair-collision statistic used by the residual nibble. -/
theorem quadraticStatistic_pairIntersectionWeight
    (F : I → Finset X) (S : Finset I) :
    quadraticStatistic (pairIntersectionWeight F) S =
      (WeightedEdgeColoring.pairCollisionStatistic F S : ℝ) := by
  classical
  unfold quadraticStatistic monomialStatistic pairIntersectionWeight
  unfold WeightedEdgeColoring.pairCollisionStatistic
  push_cast
  simp only [OrderedPair.support, OrderedPair.left, OrderedPair.right]
  rw [sum_orderedPair_eq (g := fun a b ↦
    if ({a, b} : Finset I) ⊆ S then ((F a ∩ F b).card : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b hb
  have hab : b ≠ a := (Finset.mem_filter.mp hb).2
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff]

/-- The abstract quadratic mean is the exact first moment of the collision
statistic. -/
theorem quadraticMean_pairIntersectionWeight
    (q : I → ℝ) (F : I → Finset X) :
    quadraticMean q (pairIntersectionWeight F) =
      ∑ S : Finset I, bernoulliMass q S *
        (WeightedEdgeColoring.pairCollisionStatistic F S : ℝ) := by
  classical
  rw [expected_pairCollisionStatistic]
  unfold quadraticMean pairIntersectionWeight
  simp only [OrderedPair.left, OrderedPair.right]
  rw [sum_orderedPair_eq (g := fun a b ↦
    ((F a ∩ F b).card : ℝ) * q a * q b)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The collision mean bound can be used directly as the `mu` input of the
generic high-moment theorem. -/
theorem quadraticMean_pairIntersectionWeight_le
    (q : I → ℝ) (F : I → Finset X) (mu : ℝ)
    (hmean : (∑ S : Finset I, bernoulliMass q S *
      (WeightedEdgeColoring.pairCollisionStatistic F S : ℝ)) ≤ mu) :
    quadraticMean q (pairIntersectionWeight F) ≤ mu := by
  rwa [quadraticMean_pairIntersectionWeight]

/-- Weighted one-sided overlap row. -/
noncomputable def pairIntersectionRow
    (q : I → ℝ) (F : I → Finset X) (a : I) : ℝ :=
  ∑ b ∈ (Finset.univ : Finset I).filter (fun b ↦ b ≠ a),
    q b * ((F a ∩ F b).card : ℝ)

/-- A weighted row is at most `qmax` times its unweighted overlap row. -/
theorem pairIntersectionRow_le
    (q : I → ℝ) (qmax : ℝ) (F : I → Finset X) (a : I)
    (hq0 : ∀ i, 0 ≤ q i) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ i, q i ≤ qmax)
    (B : ℕ)
    (hmult : ∀ x,
      WeightedEdgeColoring.blockerMultiplicity (Finset.univ : Finset I) F x ≤ B) :
    pairIntersectionRow q F a ≤ qmax * ((F a).card * B : ℕ) := by
  unfold pairIntersectionRow
  calc
    (∑ b ∈ (Finset.univ : Finset I).filter (fun b ↦ b ≠ a),
        q b * ((F a ∩ F b).card : ℝ)) ≤
      ∑ b ∈ (Finset.univ : Finset I).filter (fun b ↦ b ≠ a),
        qmax * ((F a ∩ F b).card : ℝ) := by
      exact Finset.sum_le_sum fun b _ ↦
        mul_le_mul_of_nonneg_right (hqmax b) (Nat.cast_nonneg _)
    _ = qmax * (∑ b ∈
        (Finset.univ : Finset I).filter (fun b ↦ b ≠ a),
          (F a ∩ F b).card : ℕ) := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ qmax * ((F a).card * B : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ hqmax0
      exact_mod_cast WeightedEdgeColoring.sum_pair_inter_card_le_card_mul_multiplicity
        F a B hmult

/-- For symmetric intersection weights the full incident load is twice the
one-sided row. -/
theorem incidentLoad_pairIntersectionWeight_eq
    (q : I → ℝ) (F : I → Finset X) (a : I) :
    incidentLoad q (pairIntersectionWeight F) a =
      2 * pairIntersectionRow q F a := by
  classical
  unfold incidentLoad pairIntersectionWeight pairIntersectionRow
  have hleft :
      (∑ e : OrderedPair I,
          if e.left = a then
            ((F e.left ∩ F e.right).card : ℝ) * q e.right else 0) =
        ∑ b ∈ (Finset.univ : Finset I).filter (fun b ↦ b ≠ a),
          q b * ((F a ∩ F b).card : ℝ) := by
    simp only [OrderedPair.left, OrderedPair.right]
    rw [sum_orderedPair_eq (g := fun x y ↦
      if x = a then ((F x ∩ F y).card : ℝ) * q y else 0)]
    simp [mul_comm]
  have hright :
      (∑ e : OrderedPair I,
          if e.right = a then
            ((F e.left ∩ F e.right).card : ℝ) * q e.left else 0) =
        ∑ b ∈ (Finset.univ : Finset I).filter (fun b ↦ b ≠ a),
          q b * ((F a ∩ F b).card : ℝ) := by
    simp only [OrderedPair.left, OrderedPair.right]
    rw [sum_orderedPair_eq (g := fun x y ↦
      if y = a then ((F x ∩ F y).card : ℝ) * q x else 0)]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hba : b = a
    · subst b
      simp
    · have hab : a ≠ b := Ne.symm hba
      simp [hba, hab, Finset.inter_comm, mul_comm]
  rw [hleft, hright]
  ring

/-- Local degree and multiplicity give the full incident-load bound required
by the high-moment estimate. -/
theorem incidentLoad_pairIntersectionWeight_le
    (q : I → ℝ) (qmax : ℝ) (F : I → Finset X)
    (L B : ℕ)
    (hq0 : ∀ i, 0 ≤ q i) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ i, q i ≤ qmax)
    (hcard : ∀ i, (F i).card ≤ L)
    (hmult : ∀ x,
      WeightedEdgeColoring.blockerMultiplicity (Finset.univ : Finset I) F x ≤ B)
    (a : I) :
    incidentLoad q (pairIntersectionWeight F) a ≤
      2 * qmax * (L * B : ℕ) := by
  rw [incidentLoad_pairIntersectionWeight_eq]
  have hrow := pairIntersectionRow_le q qmax F a hq0 hqmax0 hqmax B hmult
  have hcardReal : ((F a).card * B : ℕ) ≤ L * B :=
    Nat.mul_le_mul_right B (hcard a)
  calc
    2 * pairIntersectionRow q F a ≤
      2 * (qmax * ((F a).card * B : ℕ)) := by gcongr
    _ ≤ 2 * (qmax * (L * B : ℕ)) := by
      gcongr
    _ = 2 * qmax * (L * B : ℕ) := by ring

/-- Every pair-intersection coefficient is at most the local set-size bound. -/
theorem pairIntersectionWeight_le
    (F : I → Finset X) (L : ℕ) (hcard : ∀ i, (F i).card ≤ L)
    (e : OrderedPair I) :
    pairIntersectionWeight F e ≤ L := by
  unfold pairIntersectionWeight
  exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left)).trans (hcard e.left)

theorem pairIntersectionWeight_nonneg (F : I → Finset X)
    (e : OrderedPair I) : 0 ≤ pairIntersectionWeight F e := by
  exact Nat.cast_nonneg _

/-- Direct high-moment tail for a pair-collision statistic.  It uses only a
mean bound, the largest set size, and the largest point multiplicity. -/
theorem pairCollision_tail_mul_le
    (q : I → ℝ) (qmax : ℝ) (F : I → Finset X)
    (L B k : ℕ) (T mu : ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ i, q i ≤ qmax)
    (hcard : ∀ i, (F i).card ≤ L)
    (hmult : ∀ x,
      WeightedEdgeColoring.blockerMultiplicity (Finset.univ : Finset I) F x ≤ B)
    (hmean : (∑ S : Finset I, bernoulliMass q S *
      (WeightedEdgeColoring.pairCollisionStatistic F S : ℝ)) ≤ mu)
    (hT : 0 ≤ T) (hmu0 : 0 ≤ mu) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (upperTail (fun S ↦ (WeightedEdgeColoring.pairCollisionStatistic F S : ℝ)) T) ≤
      (mu + 2 * k * (2 * qmax * (L * B : ℕ)) +
        4 * k ^ 2 * L) ^ k := by
  have htail := quadratic_tail_mul_le_explicit q
    (pairIntersectionWeight F) k T mu
    (2 * qmax * (L * B : ℕ)) L
    hq0 hq1 (pairIntersectionWeight_nonneg F)
    (pairIntersectionWeight_le F L hcard)
    (quadraticMean_pairIntersectionWeight_le q F mu hmean)
    (incidentLoad_pairIntersectionWeight_le q qmax F L B
      hq0 hqmax0 hqmax hcard hmult)
    hT hmu0 (by positivity) (by positivity)
  have hevent :
      upperTail (quadraticStatistic (pairIntersectionWeight F)) T =
        upperTail
          (fun S ↦ (WeightedEdgeColoring.pairCollisionStatistic F S : ℝ)) T := by
    ext S
    simp [upperTail, quadraticStatistic_pairIntersectionWeight]
  rw [← hevent]
  exact htail

end WeightedEdgeColoring.FiniteBernoulliQuadraticMoment
