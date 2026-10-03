import WeightedEdgeColoring.FiniteBernoulliHarris
import WeightedEdgeColoring.FiniteBernoulliSupportedLLL
import WeightedEdgeColoring.FiniteBernoulliSupportSplit
import WeightedEdgeColoring.FiniteBernoulliCylinderLLL

/-!
# A monotone lopsided local lemma for finite Bernoulli products

Events of the same polarity need no dependency edges.  This foundational
version puts every event of the opposite polarity in the neighborhood.  The
support-refined version can further omit disjoint opposite-polarity events.
-/

namespace WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided

open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliHarris
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

variable {I J : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- `true` denotes increasing events and `false` decreasing events. -/
def HasPolarity (increasing : Bool) (E : Finset (Finset I)) : Prop :=
  if increasing then IsIncreasing E else IsDecreasing E

theorem avoid_decreasing_of_increasing
    (bad : J → Finset (Finset I)) (T : Finset J)
    (hbad : ∀ j ∈ T, IsIncreasing (bad j)) :
    IsDecreasing (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  intro U hU S hSU
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and] at hU ⊢
  intro j hj hSj
  exact hU j hj (hbad j hj hSj hSU)

theorem avoid_increasing_of_decreasing
    (bad : J → Finset (Finset I)) (T : Finset J)
    (hbad : ∀ j ∈ T, IsDecreasing (bad j)) :
    IsIncreasing (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  intro S hS U hSU
  simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
    Finset.mem_univ, true_and] at hS ⊢
  intro j hj hUj
  exact hS j hj (hbad j hj hUj hSU)

/-- Avoiding arbitrary same-polarity events cannot increase the probability
of a bad event. -/
theorem same_polarity_conditional_le
    (q : I → ℝ) (bad : J → Finset (Finset I))
    (polarity : J → Bool) (j : J) (T : Finset J)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hmono : ∀ i, HasPolarity (polarity i) (bad i))
    (hsame : ∀ i ∈ T, polarity i = polarity j) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
        (bad j ∩ WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) ≤
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) (bad j) *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
  cases hj : polarity j
  · apply decreasing_increasing_negative_correlation q hq0 hq1
    · simpa [HasPolarity, hj] using hmono j
    · apply avoid_increasing_of_decreasing bad T
      intro i hi
      have hip : polarity i = false := by simpa [hj] using hsame i hi
      simpa [HasPolarity, hip] using hmono i
  · apply increasing_decreasing_negative_correlation q hq0 hq1
    · simpa [HasPolarity, hj] using hmono j
    · apply avoid_decreasing_of_increasing bad T
      intro i hi
      have hip : polarity i = true := by simpa [hj] using hsame i hi
      simpa [HasPolarity, hip] using hmono i

/-- Asymmetric lopsided LLL in which all opposite-polarity events are declared
neighbors, while no same-polarity dependency edges are required. -/
theorem asymmetric_lopsided_local_lemma_of_polarity
    (q : I → ℝ) (bad : J → Finset (Finset I))
    (polarity : J → Bool) (neighbor : J → Finset J) (x : J → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j < 1)
    (hmono : ∀ j, HasPolarity (polarity j) (bad j))
    (hopposite : ∀ j i, polarity i ≠ polarity j → i ∈ neighbor j)
    (hmass : ∀ j, WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q) (bad j) ≤
      x j * ∏ i ∈ neighbor j, (1 - x i)) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid bad Finset.univ) := by
  have hlop : ∀ (j : J) (T : Finset J),
      T ⊆ Finset.univ \ insert j (neighbor j) →
      WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
          (bad j ∩ WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) ≤
        (x j * ∏ i ∈ neighbor j, (1 - x i)) *
          WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
            (WeightedEdgeColoring.FiniteLocalLemma.avoid bad T) := by
    intro j T hT
    apply (same_polarity_conditional_le q bad polarity j T hq0 hq1 hmono ?_).trans
    · exact mul_le_mul_of_nonneg_right (hmass j)
        (WeightedEdgeColoring.FiniteLocalLemma.eventMass_nonneg
          (bernoulliMass_nonneg q hq0 hq1) _)
    · intro i hi
      by_contra hne
      have hin := hopposite j i hne
      exact (Finset.mem_sdiff.mp (hT hi)).2
        (Finset.mem_insert_of_mem hin)
  exact (WeightedEdgeColoring.FiniteLocalLemma.asymmetric_lopsided_local_lemma
    (bernoulliMass q) bad neighbor x
    (bernoulliMass_nonneg q hq0 hq1) (sum_bernoulliMass q)
    hx0 hx1 hlop).2

section Fibers

variable {A B : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The first-coordinate fiber of a product-space event. -/
noncomputable def firstFiber (D : Finset (A × B)) (b : B) : Finset A :=
  Finset.univ.filter fun a ↦ (a, b) ∈ D

theorem eventMass_product_fibers
    (massA : A → ℝ) (massB : B → ℝ)
    (E : Finset A) (D : Finset (A × B)) (O : Finset B) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteProductCylinder.productMass massA massB)
        (WeightedEdgeColoring.FiniteProductCylinder.firstCylinder E ∩ D ∩
          WeightedEdgeColoring.FiniteProductCylinder.secondCylinder O) =
      ∑ b ∈ O, massB b *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass massA (E ∩ firstFiber D b) := by
  classical
  unfold WeightedEdgeColoring.FiniteLocalLemma.eventMass
    WeightedEdgeColoring.FiniteProductCylinder.productMass firstFiber
  rw [Finset.sum_finset_product_right
    (WeightedEdgeColoring.FiniteProductCylinder.firstCylinder E ∩ D ∩
      WeightedEdgeColoring.FiniteProductCylinder.secondCylinder O)
    O (fun b ↦ E ∩ (Finset.univ.filter fun a ↦ (a, b) ∈ D)) (by
      intro ab
      simp only [WeightedEdgeColoring.FiniteProductCylinder.mem_firstCylinder,
        WeightedEdgeColoring.FiniteProductCylinder.mem_secondCylinder, Finset.mem_inter,
        Finset.mem_filter, Finset.mem_univ, true_and]
      tauto)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp [mul_comm]

/-- Fiberwise negative correlation can be summed over an arbitrary outside
filter. -/
theorem conditional_le_of_fiberwise_negative_correlation
    (massA : A → ℝ) (massB : B → ℝ)
    (E : Finset A) (D : Finset (A × B)) (O : Finset B) (p : ℝ)
    (hmassB : ∀ b, 0 ≤ massB b)
    (hfiber : ∀ b,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass massA (E ∩ firstFiber D b) ≤
        p * WeightedEdgeColoring.FiniteLocalLemma.eventMass massA (firstFiber D b)) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteProductCylinder.productMass massA massB)
        (WeightedEdgeColoring.FiniteProductCylinder.firstCylinder E ∩ D ∩
          WeightedEdgeColoring.FiniteProductCylinder.secondCylinder O) ≤
      p * WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (WeightedEdgeColoring.FiniteProductCylinder.productMass massA massB)
        (D ∩ WeightedEdgeColoring.FiniteProductCylinder.secondCylinder O) := by
  rw [eventMass_product_fibers massA massB E D O]
  have hright := eventMass_product_fibers massA massB
    (Finset.univ : Finset A) D O
  have hfirst : WeightedEdgeColoring.FiniteProductCylinder.firstCylinder
      (B := B) (Finset.univ : Finset A) = Finset.univ := by
    ext ab
    simp
  rw [hfirst, Finset.univ_inter] at hright
  rw [hright, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  simp only [Finset.univ_inter]
  calc
    massB b * WeightedEdgeColoring.FiniteLocalLemma.eventMass massA (E ∩ firstFiber D b) ≤
        massB b * (p * WeightedEdgeColoring.FiniteLocalLemma.eventMass massA (firstFiber D b)) :=
      mul_le_mul_of_nonneg_left (hfiber b) (hmassB b)
    _ = p * (massB b *
        WeightedEdgeColoring.FiniteLocalLemma.eventMass massA (firstFiber D b)) := by ring

end Fibers

theorem splitEquiv_symm_mono_inside (K : Finset I)
    (B : Finset (Outside K)) : Monotone (fun A : Finset (Inside K) ↦
      (splitEquiv K).symm (A, B)) := by
  intro A A' hAA' i hi
  by_cases hiK : i ∈ K
  · let ii : Inside K := ⟨i, hiK⟩
    have hiA : ii ∈ A := (mem_splitEquiv_symm_inside K A B ii).mp hi
    exact (mem_splitEquiv_symm_inside K A' B ii).mpr (hAA' hiA)
  · let ii : Outside K := ⟨i, hiK⟩
    have hiB : ii ∈ B := (mem_splitEquiv_symm_outside K A B ii).mp hi
    exact (mem_splitEquiv_symm_outside K A' B ii).mpr hiB

/-- Support-refined mixed-monotone lopsided LLL. Same-polarity events never
need edges. Opposite-polarity events are neighbors exactly when their supports
overlap. -/
theorem asymmetric_lopsided_local_lemma_of_polarity_support
    (q : I → ℝ)
    (support : J → Finset I)
    (localBad : (j : J) → Finset (Finset (Inside (support j))))
    (polarity : J → Bool)
    (neighbor : J → Finset J) (x : J → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j < 1)
    (hmonoLocal : ∀ j, HasPolarity (polarity j) (localBad j))
    (hmono : ∀ j, HasPolarity (polarity j)
      (insideCylinder (support j) (localBad j)))
    (hneighbor : ∀ j i, i ≠ j → polarity i ≠ polarity j →
      (¬Disjoint (support j) (support i) ↔ i ∈ neighbor j))
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
    let Ts : Finset J := T.filter fun i ↦ polarity i = polarity j
    let To : Finset J := T.filter fun i ↦ polarity i ≠ polarity j
    let sameAvoid := WeightedEdgeColoring.FiniteLocalLemma.avoid bad Ts
    let outsideBad : J → Finset (Finset (Outside (support j))) :=
      fun i ↦ outsideView (support j) (support i) (localBad i)
    let outsideAvoid := WeightedEdgeColoring.FiniteLocalLemma.avoid outsideBad To
    let D : Finset (Finset (Inside (support j)) ×
        Finset (Outside (support j))) :=
      Finset.univ.filter fun P ↦ (splitEquiv (support j)).symm P ∈ sameAvoid
    have hopen : ∀ i ∈ To, Disjoint (support j) (support i) := by
      intro i hi
      have hiT : i ∈ T := (Finset.mem_filter.mp hi).1
      have hip : polarity i ≠ polarity j := (Finset.mem_filter.mp hi).2
      have hine : i ≠ j := by intro h; subst i; exact hip rfl
      by_contra hoverlap
      have hin := (hneighbor j i hine hip).mp hoverlap
      exact (Finset.mem_sdiff.mp (hT hiT)).2 (Finset.mem_insert_of_mem hin)
    have havoidEq : WeightedEdgeColoring.FiniteLocalLemma.avoid bad T =
        sameAvoid ∩ outsideCylinder (support j) outsideAvoid := by
      ext S
      simp only [WeightedEdgeColoring.FiniteLocalLemma.avoid, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_inter, mem_outsideCylinder]
      constructor
      · intro h
        constructor
        · have hs : ∀ i ∈ Ts, S ∉ bad i := by
            intro i hi
            exact h i (Finset.mem_filter.mp hi).1
          simpa [sameAvoid, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hs
        · have ho : ∀ i ∈ To,
              (splitEquiv (support j) S).2 ∉ outsideBad i := by
            intro i hi
            have hiTo : i ∈ To := hi
            have hiT : i ∈ T := (Finset.mem_filter.mp hiTo).1
            have hout := h i hiT
            intro houtside
            apply hout
            change S ∈ insideCylinder (support i) (localBad i)
            rw [insideCylinder_eq_outsideCylinder_of_disjoint
              (support j) (support i) (hopen i hiTo) (localBad i)]
            exact (mem_outsideCylinder (support j) (outsideBad i) S).2 houtside
          simpa [outsideAvoid, WeightedEdgeColoring.FiniteLocalLemma.avoid] using ho
      · rintro ⟨hs, ho⟩
        change ∀ i ∈ T, S ∉ bad i
        intro i hiT
        by_cases hip : polarity i = polarity j
        · have hs' : ∀ k ∈ Ts, S ∉ bad k := by
            simpa [sameAvoid, WeightedEdgeColoring.FiniteLocalLemma.avoid] using hs
          exact hs' i (Finset.mem_filter.mpr ⟨hiT, hip⟩)
        · have hiTo : i ∈ To := Finset.mem_filter.mpr ⟨hiT, hip⟩
          have ho' : ∀ k ∈ To,
              (splitEquiv (support j) S).2 ∉ outsideBad k := by
            simpa [outsideAvoid, WeightedEdgeColoring.FiniteLocalLemma.avoid] using ho
          have hout := ho' i hiTo
          change S ∉ insideCylinder (support i) (localBad i)
          intro hinside
          apply hout
          apply (mem_outsideCylinder (support j) (outsideBad i) S).1
          rw [← insideCylinder_eq_outsideCylinder_of_disjoint
            (support j) (support i) (hopen i hiTo) (localBad i)]
          exact hinside
    have hsamePolarity : HasPolarity (!polarity j) sameAvoid := by
      cases hjp : polarity j
      · change IsIncreasing sameAvoid
        apply avoid_increasing_of_decreasing bad Ts
        intro i hi
        have hip : polarity i = false := by
          simpa [Ts, hjp] using (Finset.mem_filter.mp hi).2
        simpa [HasPolarity, hip, bad] using hmono i
      · change IsDecreasing sameAvoid
        apply avoid_decreasing_of_increasing bad Ts
        intro i hi
        have hip : polarity i = true := by
          simpa [Ts, hjp] using (Finset.mem_filter.mp hi).2
        simpa [HasPolarity, hip, bad] using hmono i
    have hfiber : ∀ B, HasPolarity (!polarity j) (firstFiber D B) := by
      intro B
      cases hjp : polarity j
      · change IsIncreasing (firstFiber D B)
        intro A hA A' hAA'
        have hm : (splitEquiv (support j)).symm (A, B) ∈ sameAvoid := by
          simpa [firstFiber, D] using hA
        have hm' := (by simpa [HasPolarity, hjp] using hsamePolarity :
          IsIncreasing sameAvoid) hm
          (splitEquiv_symm_mono_inside (support j) B hAA')
        simpa [firstFiber, D] using hm'
      · change IsDecreasing (firstFiber D B)
        intro A' hA' A hAA'
        have hm : (splitEquiv (support j)).symm (A', B) ∈ sameAvoid := by
          simpa [firstFiber, D] using hA'
        have hm' := (by simpa [HasPolarity, hjp] using hsamePolarity :
          IsDecreasing sameAvoid) hm
          (splitEquiv_symm_mono_inside (support j) B hAA')
        simpa [firstFiber, D] using hm'
    have hfiberCorr : ∀ B,
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
            (bernoulliMass (insideParameter q (support j)))
            (localBad j ∩ firstFiber D B) ≤
          (x j * ∏ i ∈ neighbor j, (1 - x i)) *
            WeightedEdgeColoring.FiniteLocalLemma.eventMass
              (bernoulliMass (insideParameter q (support j)))
              (firstFiber D B) := by
      intro B
      have hq0' : ∀ i, 0 ≤ insideParameter q (support j) i := fun i ↦ hq0 i
      have hq1' : ∀ i, insideParameter q (support j) i ≤ 1 := fun i ↦ hq1 i
      have hc : WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (support j)))
          (localBad j ∩ firstFiber D B) ≤
        WeightedEdgeColoring.FiniteLocalLemma.eventMass
            (bernoulliMass (insideParameter q (support j))) (localBad j) *
          WeightedEdgeColoring.FiniteLocalLemma.eventMass
            (bernoulliMass (insideParameter q (support j))) (firstFiber D B) := by
        cases hjp : polarity j
        · exact decreasing_increasing_negative_correlation
            (insideParameter q (support j)) hq0' hq1'
            (localBad j) (firstFiber D B)
            (by simpa [HasPolarity, hjp] using hmonoLocal j)
            (by simpa [HasPolarity, hjp] using hfiber B)
        · exact increasing_decreasing_negative_correlation
            (insideParameter q (support j)) hq0' hq1'
            (localBad j) (firstFiber D B)
            (by simpa [HasPolarity, hjp] using hmonoLocal j)
            (by simpa [HasPolarity, hjp] using hfiber B)
      exact hc.trans (mul_le_mul_of_nonneg_right (hlocal j)
        (WeightedEdgeColoring.FiniteLocalLemma.eventMass_nonneg
          (bernoulliMass_nonneg _ hq0' hq1') _))
    rw [havoidEq]
    have hleftSet : bad j ∩ (sameAvoid ∩ outsideCylinder (support j) outsideAvoid) =
        splitEvent (support j)
          (WeightedEdgeColoring.FiniteProductCylinder.firstCylinder (localBad j) ∩ D ∩
            WeightedEdgeColoring.FiniteProductCylinder.secondCylinder outsideAvoid) := by
      ext S
      simp [bad, D, sameAvoid]
    have hrightSet : sameAvoid ∩ outsideCylinder (support j) outsideAvoid =
        splitEvent (support j)
          (D ∩ WeightedEdgeColoring.FiniteProductCylinder.secondCylinder outsideAvoid) := by
      ext S
      simp [D, sameAvoid]
    rw [hleftSet, eventMass_splitEvent, hrightSet, eventMass_splitEvent]
    exact conditional_le_of_fiberwise_negative_correlation
      (bernoulliMass (insideParameter q (support j)))
      (bernoulliMass (outsideParameter q (support j)))
      (localBad j) D outsideAvoid
      (x j * ∏ i ∈ neighbor j, (1 - x i))
      (fun b ↦ bernoulliMass_nonneg (outsideParameter q (support j))
        (fun i ↦ hq0 i) (fun i ↦ hq1 i) b)
      hfiberCorr
  exact (WeightedEdgeColoring.FiniteLocalLemma.asymmetric_lopsided_local_lemma
    (bernoulliMass q) bad neighbor x
    (bernoulliMass_nonneg q hq0 hq1) (sum_bernoulliMass q)
    hx0 hx1 hlop).2

/-- Canonical support-refined neighborhood: the opposite-polarity events with
overlapping coordinate support. -/
noncomputable def polaritySupportNeighbor
    (support : J → Finset I) (polarity : J → Bool) (j : J) : Finset J :=
  Finset.univ.filter fun i ↦ i ≠ j ∧ polarity i ≠ polarity j ∧
    ¬Disjoint (support j) (support i)

/-- Canonical corollary in which applications only supply local/global
monotonicity and the numerical product bound. -/
theorem asymmetric_lopsided_local_lemma_of_polarity_support_canonical
    (q : I → ℝ)
    (support : J → Finset I)
    (localBad : (j : J) → Finset (Finset (Inside (support j))))
    (polarity : J → Bool) (x : J → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (hx0 : ∀ j, 0 ≤ x j) (hx1 : ∀ j, x j < 1)
    (hmonoLocal : ∀ j, HasPolarity (polarity j) (localBad j))
    (hmonoGlobal : ∀ j, HasPolarity (polarity j)
      (insideCylinder (support j) (localBad j)))
    (hlocal : ∀ j,
      WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (support j))) (localBad j) ≤
        x j * ∏ i ∈ polaritySupportNeighbor support polarity j, (1 - x i)) :
    0 < WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (WeightedEdgeColoring.FiniteLocalLemma.avoid
        (fun j ↦ insideCylinder (support j) (localBad j)) Finset.univ) := by
  apply asymmetric_lopsided_local_lemma_of_polarity_support
    q support localBad polarity (polaritySupportNeighbor support polarity)
    x hq0 hq1 hx0 hx1 hmonoLocal hmonoGlobal
  · intro j i hine hpol
    simp [polaritySupportNeighbor, hine, hpol]
  · exact hlocal

end WeightedEdgeColoring.FiniteBernoulliMonotoneLopsided
