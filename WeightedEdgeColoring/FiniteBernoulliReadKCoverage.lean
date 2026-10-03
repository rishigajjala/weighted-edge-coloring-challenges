import WeightedEdgeColoring.FiniteBernoulliSupportSplit

/-!
# Finite Bernoulli coverage systems with bounded reads

Coordinates are retained independently. Coordinate `i` covers the finite set
`F i`; hence an uncovered-point indicator reads exactly the coordinates whose
sets contain that point. This file proves exact one-point and joint uncovered
probabilities and the resulting exact expected uncovered weight.
-/

namespace WeightedEdgeColoring.FiniteBernoulliReadKCoverage

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

variable {I X : Type*}
  [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

/-- Points covered by at least one selected coordinate. -/
def covered (F : I → Finset X) (S : Finset I) : Finset X :=
  S.biUnion F

/-- Points not covered by any selected coordinate. -/
def uncovered (F : I → Finset X) (S : Finset I) : Finset X :=
  Finset.univ \ covered F S

/-- Coordinates that can cover one point. -/
def blockers (F : I → Finset X) (x : X) : Finset I :=
  Finset.univ.filter fun i ↦ x ∈ F i

/-- Coordinates read by at least one uncovered indicator in `A`. -/
def blockersOf (F : I → Finset X) (A : Finset X) : Finset I :=
  A.biUnion (blockers F)

@[simp] theorem mem_covered_iff (F : I → Finset X) (S : Finset I) (x : X) :
    x ∈ covered F S ↔ ∃ i ∈ S, x ∈ F i := by
  simp [covered]

@[simp] theorem mem_uncovered_iff (F : I → Finset X) (S : Finset I) (x : X) :
    x ∈ uncovered F S ↔ ∀ i ∈ S, x ∉ F i := by
  simp [uncovered, covered]

theorem disjoint_blockers_iff_uncovered
    (F : I → Finset X) (S : Finset I) (x : X) :
    Disjoint S (blockers F x) ↔ x ∈ uncovered F S := by
  rw [Finset.disjoint_left]
  simp [blockers, mem_uncovered_iff]

theorem disjoint_blockersOf_iff
    (F : I → Finset X) (S : Finset I) (A : Finset X) :
    Disjoint S (blockersOf F A) ↔ A ⊆ uncovered F S := by
  rw [Finset.disjoint_left]
  constructor
  · intro h x hx
    rw [mem_uncovered_iff]
    intro i hi
    intro hxi
    exact h hi (by
      simp only [blockersOf, Finset.mem_biUnion]
      exact ⟨x, hx, by simp [blockers, hxi]⟩)
  · intro h i hi hiU
    rcases Finset.mem_biUnion.mp hiU with ⟨x, hxA, hix⟩
    have hxu := h hxA
    rw [mem_uncovered_iff] at hxu
    exact (hxu i hi) (by simpa [blockers] using hix)

/-- A Bernoulli cylinder has the same mass as its local event. -/
theorem eventMass_insideCylinder
    (q : I → ℝ) (K : Finset I)
    (E : Finset (Finset (Inside K))) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (insideCylinder K E) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass (insideParameter q K)) E := by
  rw [show insideCylinder K E =
      insideCylinder K E ∩
        outsideCylinder K (Finset.univ : Finset (Finset (Outside K))) by
    ext S
    simp]
  rw [eventMass_inside_inter_outside]
  simp [WeightedEdgeColoring.FiniteLocalLemma.eventMass, sum_bernoulliMass]

/-- Exact probability that no coordinate in `K` is selected. -/
theorem eventMass_disjoint
    (q : I → ℝ) (K : Finset I) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (Finset.univ.filter fun S : Finset I ↦ Disjoint S K) =
      ∏ i ∈ K, (1 - q i) := by
  have hevent : (Finset.univ.filter fun S : Finset I ↦ Disjoint S K) =
      insideCylinder K {∅} := by
    ext S
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, mem_insideCylinder,
      Finset.mem_singleton]
    rw [Finset.disjoint_left]
    constructor
    · intro hdisj
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hiS : (i : I) ∈ S := (mem_splitEquiv_inside K S i).mp hi
      exact hdisj hiS i.2
    · intro hempty i hiS hiK
      let ii : Inside K := ⟨i, hiK⟩
      have hii : ii ∈ (splitEquiv K S).1 :=
        (mem_splitEquiv_inside K S ii).mpr hiS
      rw [hempty] at hii
      simp at hii
  rw [hevent, eventMass_insideCylinder]
  simp only [WeightedEdgeColoring.FiniteLocalLemma.eventMass, Finset.sum_singleton,
    bernoulliMass, Finset.prod_empty, one_mul,
    insideParameter]
  simp only [Finset.sdiff_empty]
  have huniv : (Finset.univ : Finset (Inside K)) = K.attach := by
    ext i
    simp
  rw [huniv]
  let emb : Inside K ↪ I := ⟨fun i ↦ i.1, Subtype.val_injective⟩
  have hmap : K.attach.map emb = K := by
    ext i
    simp [emb]
  calc
    (∏ x ∈ K.attach, (1 - q (x : I))) =
        ∏ i ∈ K.attach.map emb, (1 - q i) := by
      rw [Finset.prod_map]
      simp [emb]
    _ = ∏ i ∈ K, (1 - q i) := by rw [hmap]

/-- Exact probability that one specified point is uncovered. -/
theorem eventMass_point_uncovered
    (q : I → ℝ) (F : I → Finset X) (x : X) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (Finset.univ.filter fun S : Finset I ↦ x ∈ uncovered F S) =
      ∏ i ∈ blockers F x, (1 - q i) := by
  have hevent : (Finset.univ.filter fun S : Finset I ↦ x ∈ uncovered F S) =
      Finset.univ.filter fun S : Finset I ↦ Disjoint S (blockers F x) := by
    ext S
    simp [disjoint_blockers_iff_uncovered]
  rw [hevent, eventMass_disjoint]

/-- Exact joint probability that every point in `A` is uncovered. -/
theorem eventMass_all_uncovered
    (q : I → ℝ) (F : I → Finset X) (A : Finset X) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (Finset.univ.filter fun S : Finset I ↦ A ⊆ uncovered F S) =
      ∏ i ∈ blockersOf F A, (1 - q i) := by
  have hevent : (Finset.univ.filter fun S : Finset I ↦ A ⊆ uncovered F S) =
      Finset.univ.filter fun S : Finset I ↦ Disjoint S (blockersOf F A) := by
    ext S
    simp [disjoint_blockersOf_iff]
  rw [hevent, eventMass_disjoint]

/-- Weighted number of uncovered points. -/
def uncoveredWeight (weight : X → ℝ) (F : I → Finset X)
    (S : Finset I) : ℝ :=
  ∑ x ∈ uncovered F S, weight x

/-- Exact expectation of the weighted uncovered count. -/
theorem expected_uncoveredWeight
    (q : I → ℝ) (weight : X → ℝ) (F : I → Finset X) :
    (∑ S : Finset I, bernoulliMass q S * uncoveredWeight weight F S) =
      ∑ x : X, weight x * ∏ i ∈ blockers F x, (1 - q i) := by
  classical
  unfold uncoveredWeight
  simp_rw [Finset.mul_sum]
  have hexpand : (∑ S : Finset I,
      ∑ x ∈ uncovered F S, bernoulliMass q S * weight x) =
      ∑ S : Finset I, ∑ x : X,
        if x ∈ uncovered F S then bernoulliMass q S * weight x else 0 := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext x
      simp [mem_uncovered_iff]
    · intro x hx
      rfl
  rw [hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hp := eventMass_point_uncovered q F x
  unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass at hp
  calc
    (∑ S : Finset I,
        if x ∈ uncovered F S then bernoulliMass q S * weight x else 0) =
        weight x * ∑ S : Finset I,
          if x ∈ uncovered F S then bernoulliMass q S else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases h : x ∈ uncovered F S <;> simp [h, mul_comm]
    _ = weight x * ∏ i ∈ blockers F x, (1 - q i) := by
      congr 1
      calc
        (∑ S : Finset I,
            if x ∈ uncovered F S then bernoulliMass q S else 0) =
            ∑ S ∈ (Finset.univ.filter fun S : Finset I ↦
              x ∈ uncovered F S), bernoulliMass q S := by
          rw [Finset.sum_filter]
        _ = ∏ i ∈ blockers F x, (1 - q i) := hp

/-- Weighted number of covered points. -/
def coveredWeight (weight : X → ℝ) (F : I → Finset X)
    (S : Finset I) : ℝ :=
  ∑ x ∈ covered F S, weight x

/-- Exact expected covered weight, obtained by subtracting the exact
uncovered expectation from the total weight. -/
theorem expected_coveredWeight
    (q : I → ℝ) (weight : X → ℝ) (F : I → Finset X) :
    (∑ S : Finset I, bernoulliMass q S * coveredWeight weight F S) =
      ∑ x : X, weight x *
        (1 - ∏ i ∈ blockers F x, (1 - q i)) := by
  have hpart (S : Finset I) :
      uncoveredWeight weight F S + coveredWeight weight F S = ∑ x : X, weight x := by
    unfold uncoveredWeight coveredWeight uncovered
    have hs := Finset.sum_sdiff (f := weight)
      (s₁ := covered F S) (s₂ := (Finset.univ : Finset X))
      (Finset.subset_univ _)
    simpa [add_comm] using hs
  have hsum :
      (∑ S : Finset I, bernoulliMass q S * coveredWeight weight F S) +
        (∑ S : Finset I, bernoulliMass q S * uncoveredWeight weight F S) =
      ∑ x : X, weight x := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ S : Finset I,
          (bernoulliMass q S * coveredWeight weight F S +
            bernoulliMass q S * uncoveredWeight weight F S)) =
          ∑ S : Finset I, bernoulliMass q S * (∑ x : X, weight x) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [← mul_add, add_comm, hpart]
      _ = (∑ x : X, weight x) * ∑ S : Finset I, bernoulliMass q S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      _ = ∑ x : X, weight x := by rw [sum_bernoulliMass, mul_one]
  rw [expected_uncoveredWeight q weight F] at hsum
  have hrhs :
      (∑ x : X, weight x *
          (1 - ∏ i ∈ blockers F x, (1 - q i))) +
        (∑ x : X, weight x * ∏ i ∈ blockers F x, (1 - q i)) =
      ∑ x : X, weight x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  linarith

/-- The incidence count formulation of the read bound: every coordinate is
read by at most `L` uncovered-point indicators. -/
theorem coordinate_read_card_le
    (F : I → Finset X) (L : ℕ) (hread : ∀ i, (F i).card ≤ L) (i : I) :
    ((Finset.univ : Finset X).filter fun x ↦ i ∈ blockers F x).card ≤ L := by
  have heq : ((Finset.univ : Finset X).filter fun x ↦ i ∈ blockers F x) = F i := by
    ext x
    simp [blockers]
  rw [heq]
  exact hread i

/-! ## The finite read-`L` joint-probability kernel -/

/-- Number of point indicators in `A` that read coordinate `i`. -/
def readMultiplicity (F : I → Finset X) (A : Finset X) (i : I) : ℕ :=
  (A.filter fun x ↦ i ∈ blockers F x).card

theorem readMultiplicity_le
    (F : I → Finset X) (A : Finset X) (L : ℕ)
    (hread : ∀ i, (F i).card ≤ L) (i : I) :
    readMultiplicity F A i ≤ L := by
  apply (Finset.card_le_card ?_).trans (hread i)
  intro x hx
  have hmem := (Finset.mem_filter.mp hx).2
  simpa [blockers] using hmem

theorem mem_blockersOf_iff_readMultiplicity_pos
    (F : I → Finset X) (A : Finset X) (i : I) :
    i ∈ blockersOf F A ↔ 0 < readMultiplicity F A i := by
  rw [blockersOf, Finset.mem_biUnion, readMultiplicity, Finset.card_pos]
  constructor
  · rintro ⟨x, hxA, hix⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨hxA, hix⟩⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

private theorem pow_antitone_of_mem_unit
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    p ^ n ≤ p ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, pow_succ]
      have hpnonneg : 0 ≤ p ^ (m + k) := pow_nonneg hp0 _
      calc
        p ^ (m + k) * p ≤ p ^ (m + k) * 1 :=
          mul_le_mul_of_nonneg_left hp1 hpnonneg
        _ = p ^ (m + k) := by ring
        _ ≤ p ^ m := ih (Nat.le_add_right m k)

private theorem prod_point_blocker_products
    (p : I → ℝ) (F : I → Finset X) (A : Finset X) :
    (∏ x ∈ A, ∏ i ∈ blockers F x, p i) =
      ∏ i : I, p i ^ readMultiplicity F A i := by
  calc
    (∏ x ∈ A, ∏ i ∈ blockers F x, p i) =
        ∏ x ∈ A, ∏ i : I, if i ∈ blockers F x then p i else 1 := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [← Finset.prod_filter]
      simp
    _ = ∏ i : I, ∏ x ∈ A, if i ∈ blockers F x then p i else 1 := by
      rw [Finset.prod_comm]
    _ = ∏ i : I, p i ^ readMultiplicity F A i := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [← Finset.prod_filter]
      simp [readMultiplicity]

/-- Finite read-`L` Finner kernel for uncovered indicators. The `L`th power
of a joint uncovered probability is bounded by the product of its one-point
uncovered probabilities. -/
theorem joint_uncovered_pow_le_prod_marginals
    (q : I → ℝ) (F : I → Finset X) (A : Finset X) (L : ℕ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hread : ∀ i, (F i).card ≤ L) :
    (∏ i ∈ blockersOf F A, (1 - q i)) ^ L ≤
      ∏ x ∈ A, ∏ i ∈ blockers F x, (1 - q i) := by
  rw [prod_point_blocker_products]
  rw [← Finset.prod_pow]
  have hpoint : ∀ i ∈ blockersOf F A,
      (1 - q i) ^ L ≤ (1 - q i) ^ readMultiplicity F A i := by
    intro i hi
    apply pow_antitone_of_mem_unit
    · linarith [hq1 i]
    · linarith [hq0 i]
    · exact readMultiplicity_le F A L hread i
  calc
    (∏ i ∈ blockersOf F A, (1 - q i) ^ L) ≤
        ∏ i ∈ blockersOf F A, (1 - q i) ^ readMultiplicity F A i := by
      exact Finset.prod_le_prod (fun i _ ↦ pow_nonneg (by linarith [hq1 i]) _)
        hpoint
    _ = ∏ i : I, (1 - q i) ^ readMultiplicity F A i := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro i hiuniv hinot
      have hzero : readMultiplicity F A i = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        exact hinot ((mem_blockersOf_iff_readMultiplicity_pos F A i).2 hpos)
      simp [hzero]

theorem eventMass_all_uncovered_pow_le_prod_point_masses
    (q : I → ℝ) (F : I → Finset X) (A : Finset X) (L : ℕ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hread : ∀ i, (F i).card ≤ L) :
    (WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (Finset.univ.filter fun S : Finset I ↦ A ⊆ uncovered F S)) ^ L ≤
      ∏ x ∈ A,
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (Finset.univ.filter fun S : Finset I ↦ x ∈ uncovered F S) := by
  rw [eventMass_all_uncovered]
  simpa only [eventMass_point_uncovered] using
    joint_uncovered_pow_le_prod_marginals q F A L hq0 hq1 hread

end WeightedEdgeColoring.FiniteBernoulliReadKCoverage
