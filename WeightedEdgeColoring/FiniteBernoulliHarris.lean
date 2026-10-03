import WeightedEdgeColoring.FiniteBernoulliChernoff
import Mathlib.Combinatorics.SetFamily.FourFunctions

/-!
# Harris inequalities for the finite Bernoulli product

This file records positive correlation of increasing events and negative
correlation of an increasing and a decreasing event.  The proof is the FKG
inequality applied to the product Bernoulli mass.
-/

namespace WeightedEdgeColoring.FiniteBernoulliHarris

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- An event is increasing when adding active coordinates preserves it. -/
def IsIncreasing (E : Finset (Finset I)) : Prop :=
  ∀ ⦃S⦄, S ∈ E → ∀ ⦃T⦄, S ⊆ T → T ∈ E

/-- An event is decreasing when deleting active coordinates preserves it. -/
def IsDecreasing (E : Finset (Finset I)) : Prop :=
  ∀ ⦃T⦄, T ∈ E → ∀ ⦃S⦄, S ⊆ T → S ∈ E

private theorem bernoulliMass_eq_prod_ite (q : I → ℝ) (S : Finset I) :
    bernoulliMass q S = ∏ i, if i ∈ S then q i else 1 - q i := by
  classical
  rw [bernoulliMass, Finset.prod_ite]
  congr 1 <;> apply Finset.prod_congr
  · ext i
    simp
  · intro i hi
    rfl
  · ext i
    simp
  · intro i hi
    rfl

/-- Product Bernoulli mass is exactly log-modular on the powerset lattice. -/
theorem bernoulliMass_inter_union_eq (q : I → ℝ) (S T : Finset I) :
    bernoulliMass q S * bernoulliMass q T =
      bernoulliMass q (S ∩ T) * bernoulliMass q (S ∪ T) := by
  repeat' rw [bernoulliMass_eq_prod_ite]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T <;>
    simp [hiS, hiT] <;> ring

/-- Product Bernoulli mass is log-modular on the powerset lattice. -/
theorem bernoulliMass_mul_le_inf_sup (q : I → ℝ) (S T : Finset I) :
    bernoulliMass q S * bernoulliMass q T ≤
      bernoulliMass q (S ∩ T) * bernoulliMass q (S ∪ T) := by
  exact (bernoulliMass_inter_union_eq q S T).le

private def indicator (E : Finset (Finset I)) (S : Finset I) : ℝ :=
  if S ∈ E then 1 else 0

private theorem indicator_nonneg (E : Finset (Finset I)) :
    0 ≤ indicator E := by
  intro S
  by_cases hS : S ∈ E <;> simp [indicator, hS]

private theorem indicator_monotone_of_increasing
    {E : Finset (Finset I)} (hE : IsIncreasing E) :
    Monotone (indicator E) := by
  intro S T hST
  by_cases hS : S ∈ E
  · have hT := hE hS hST
    simp [indicator, hS, hT]
  · by_cases hT : T ∈ E <;> simp [indicator, hS, hT]

private theorem sum_mass_mul_indicator (q : I → ℝ)
    (E : Finset (Finset I)) :
    (∑ S, bernoulliMass q S * indicator E S) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E := by
  simp [indicator, WeightedEdgeColoring.FiniteLocalLemma.eventMass, Finset.sum_ite_irrel]

private theorem sum_mass_mul_indicators (q : I → ℝ)
    (E F : Finset (Finset I)) :
    (∑ S, bernoulliMass q S * (indicator E S * indicator F S)) =
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) (E ∩ F) := by
  simpa [indicator, WeightedEdgeColoring.FiniteLocalLemma.eventMass, Finset.inter_comm]

/-- Increasing events in a finite Bernoulli product are positively
correlated. -/
theorem increasing_events_positive_correlation
    (q : I → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (E F : Finset (Finset I)) (hE : IsIncreasing E) (hF : IsIncreasing F) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) F ≤
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) (E ∩ F) := by
  have h := fkg (μ := bernoulliMass q) (f := indicator E) (g := indicator F)
    (fun S ↦ bernoulliMass_nonneg q hq0 hq1 S)
    (indicator_nonneg E) (indicator_nonneg F)
    (indicator_monotone_of_increasing hE)
    (indicator_monotone_of_increasing hF)
    (bernoulliMass_mul_le_inf_sup q)
  rw [sum_mass_mul_indicator, sum_mass_mul_indicator,
    sum_bernoulliMass, one_mul, sum_mass_mul_indicators] at h
  exact h

/-- The complement of a decreasing event is increasing. -/
theorem increasing_complement_of_decreasing
    {D : Finset (Finset I)} (hD : IsDecreasing D) :
    IsIncreasing (Finset.univ \ D) := by
  intro S hS T hST
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hS ⊢
  intro hTD
  exact hS (hD hTD hST)

/-- An increasing and a decreasing event are negatively correlated. -/
theorem increasing_decreasing_negative_correlation
    (q : I → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (E D : Finset (Finset I)) (hE : IsIncreasing E) (hD : IsDecreasing D) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) (E ∩ D) ≤
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) D := by
  have hpos := increasing_events_positive_correlation q hq0 hq1 E
    (Finset.univ \ D) hE (increasing_complement_of_decreasing hD)
  have hEsplit :
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) (E ∩ D) +
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (E ∩ (Finset.univ \ D)) =
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E := by
    have hsum := Finset.sum_sdiff
      (f := bernoulliMass q) (s₁ := E ∩ D) (s₂ := E)
      Finset.inter_subset_left
    have hset : E \ (E ∩ D) = E ∩ (Finset.univ \ D) := by
      ext S
      simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and]
      tauto
    unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass
    rw [hset] at hsum
    linarith
  have hmassD :
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) D +
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (Finset.univ \ D) = 1 := by
    have hsum := Finset.sum_sdiff
      (f := bernoulliMass q) (s₁ := D)
      (s₂ := (Finset.univ : Finset (Finset I))) (Finset.subset_univ D)
    unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass
    have htotal := sum_bernoulliMass q
    linarith
  have hscaled :
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E *
          WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) D +
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E *
          WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
            (Finset.univ \ D) =
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E := by
    rw [← mul_add, hmassD, mul_one]
  linarith

/-- The symmetric negative-correlation orientation. -/
theorem decreasing_increasing_negative_correlation
    (q : I → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (D E : Finset (Finset I)) (hD : IsDecreasing D) (hE : IsIncreasing E) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) (D ∩ E) ≤
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) D *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E := by
  simpa [Finset.inter_comm, mul_comm] using
    increasing_decreasing_negative_correlation q hq0 hq1 E D hE hD

/-- A nonnegative weighted sum increases when active coordinates are added. -/
theorem weightedSum_mono {a : I → ℝ} (ha : ∀ i, 0 ≤ a i) :
    Monotone (weightedSum a) := by
  intro S T hST
  exact Finset.sum_le_sum_of_subset_of_nonneg hST fun i _ _ ↦ ha i

/-- An upper tail of a nonnegative weighted sum is increasing. -/
theorem upperTail_weightedSum_increasing (a : I → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    IsIncreasing (upperTail (weightedSum a) r) := by
  intro S hS T hST
  simp only [upperTail, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact hS.trans (weightedSum_mono ha hST)

/-- A lower tail of a nonnegative weighted sum is decreasing. -/
theorem lowerTail_weightedSum_decreasing (a : I → ℝ) (r : ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    IsDecreasing (lowerTail (weightedSum a) r) := by
  intro T hT S hST
  simp only [lowerTail, Finset.mem_filter, Finset.mem_univ, true_and] at hT ⊢
  exact (weightedSum_mono ha hST).trans hT

section Avoidance

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Avoiding a finite family of increasing events is a decreasing event. -/
theorem avoid_increasing_is_decreasing
    (bad : J → Finset (Finset I)) (T : Finset J)
    (hbad : ∀ j ∈ T, IsIncreasing (bad j)) :
    IsDecreasing (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  intro U hU S hSU
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and] at hU ⊢
  intro j hj hSbad
  exact hU j hj (hbad j hj hSbad hSU)

/-- Avoiding a finite family of decreasing events is an increasing event. -/
theorem avoid_decreasing_is_increasing
    (bad : J → Finset (Finset I)) (T : Finset J)
    (hbad : ∀ j ∈ T, IsDecreasing (bad j)) :
    IsIncreasing (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  intro S hS U hSU
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and] at hS ⊢
  intro j hj hUbad
  exact hS j hj (hbad j hj hUbad hSU)

/-- Division-free Harris bound: avoiding any family of increasing bad
events cannot make an increasing bad event more likely. -/
theorem increasing_inter_avoid_increasing_le
    (q : I → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (E : Finset (Finset I)) (hE : IsIncreasing E)
    (bad : J → Finset (Finset I)) (T : Finset J)
    (hbad : ∀ j ∈ T, IsIncreasing (bad j)) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (E ∩ WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) ≤
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) E *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  exact increasing_decreasing_negative_correlation q hq0 hq1 E
    (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) hE
    (avoid_increasing_is_decreasing bad T hbad)

/-- Dual division-free Harris bound for a decreasing bad event and a family
of decreasing bad events. -/
theorem decreasing_inter_avoid_decreasing_le
    (q : I → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (D : Finset (Finset I)) (hD : IsDecreasing D)
    (bad : J → Finset (Finset I)) (T : Finset J)
    (hbad : ∀ j ∈ T, IsDecreasing (bad j)) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (D ∩ WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) ≤
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) D *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  exact decreasing_increasing_negative_correlation q hq0 hq1 D
    (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) hD
    (avoid_decreasing_is_increasing bad T hbad)

end Avoidance

end WeightedEdgeColoring.FiniteBernoulliHarris
