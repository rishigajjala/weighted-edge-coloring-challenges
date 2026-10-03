import WeightedEdgeColoring.RankThreeResidualCollision
import WeightedEdgeColoring.RankThreeSupportExpansion
import WeightedEdgeColoring.FiniteBernoulliHarris

/-!
# Quantitative bounds for residual collision terms

The exact collision statistic is quadratic in the retained coordinates.  A
uniform blocker-multiplicity bound turns its expectation into a first moment
times one further local-degree factor.
-/

namespace WeightedEdgeColoring

open scoped BigOperators
open FiniteBernoulliChernoff

section Generic

variable {α β Ω : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- For one fixed index, the sum of its intersections with all other sets is
bounded by its size times the maximum point multiplicity. -/
theorem sum_pair_inter_card_le_card_mul_multiplicity
    (F : α → Finset β) (p : α) (B : ℕ)
    (hmult : ∀ x, blockerMultiplicity (Finset.univ : Finset α) F x ≤ B) :
    (∑ r ∈ (Finset.univ : Finset α).filter (fun r ↦ r ≠ p),
      (F p ∩ F r).card) ≤ (F p).card * B := by
  let R := (Finset.univ : Finset α).filter (fun r ↦ r ≠ p)
  let G : α → Finset β := fun r ↦ F p ∩ F r
  rw [sum_card_eq_sum_blockerMultiplicity R G]
  calc
    (∑ x ∈ R.biUnion G, blockerMultiplicity R G x) ≤
        ∑ _x ∈ R.biUnion G, B := by
      apply Finset.sum_le_sum
      intro x hx
      unfold blockerMultiplicity
      calc
        (R.filter fun r ↦ x ∈ G r).card ≤
            ((Finset.univ : Finset α).filter fun r ↦ x ∈ F r).card := by
          apply Finset.card_le_card
          intro r hr
          have hrdata := Finset.mem_filter.mp hr
          have hxG := Finset.mem_inter.mp hrdata.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, hxG.2⟩
        _ = blockerMultiplicity (Finset.univ : Finset α) F x := rfl
        _ ≤ B := hmult x
    _ = (R.biUnion G).card * B := by simp
    _ ≤ (F p).card * B := by
      apply Nat.mul_le_mul_right B
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨r, hr, hxG⟩
      exact (Finset.mem_inter.mp hxG).1

/-- Raw ordered pair overlap is at most maximum multiplicity times the total
singleton mass. -/
theorem orderedPairOverlap_univ_le_mul_sum_card
    (F : α → Finset β) (B : ℕ)
    (hmult : ∀ x, blockerMultiplicity (Finset.univ : Finset α) F x ≤ B) :
    orderedPairOverlap (Finset.univ : Finset α) F ≤
      B * ∑ p : α, (F p).card := by
  unfold orderedPairOverlap
  calc
    (∑ p ∈ (Finset.univ : Finset α),
        ∑ r ∈ (Finset.univ : Finset α).filter (fun r ↦ r ≠ p),
          (F p ∩ F r).card) ≤
        ∑ p : α, (F p).card * B := by
      exact Finset.sum_le_sum fun p _ ↦
        sum_pair_inter_card_le_card_mul_multiplicity F p B hmult
    _ = B * ∑ p : α, (F p).card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      simp [Nat.mul_comm]

/-- Generic quadratic moment bound. -/
theorem expected_pairCollisionStatistic_le
    (q : α → ℝ) (F : α → Finset β) (qmax : ℝ) (A B : ℕ)
    (hq0 : ∀ p, 0 ≤ q p) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ p, q p ≤ qmax)
    (hmult : ∀ x, blockerMultiplicity (Finset.univ : Finset α) F x ≤ B)
    (hsum : (∑ p : α, (F p).card) ≤ A) :
    (∑ S : Finset α, bernoulliMass q S *
      (pairCollisionStatistic F S : ℝ)) ≤
      qmax ^ 2 * (B * A : ℕ) := by
  rw [expected_pairCollisionStatistic]
  have hraw := orderedPairOverlap_univ_le_mul_sum_card F B hmult
  have hrawA : orderedPairOverlap (Finset.univ : Finset α) F ≤ B * A := by
    exact hraw.trans (Nat.mul_le_mul_left B hsum)
  calc
    (∑ p : α, ∑ r ∈ (Finset.univ : Finset α).filter (fun r ↦ r ≠ p),
        q p * q r * ((F p ∩ F r).card : ℝ)) ≤
        ∑ p : α, ∑ r ∈ (Finset.univ : Finset α).filter (fun r ↦ r ≠ p),
          qmax ^ 2 * ((F p ∩ F r).card : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro r _
      have hp : q p * q r ≤ qmax ^ 2 := by
        calc
          q p * q r ≤ qmax * qmax :=
            mul_le_mul (hqmax p) (hqmax r) (hq0 r) hqmax0
          _ = qmax ^ 2 := by ring
      exact mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
    _ = qmax ^ 2 * (orderedPairOverlap (Finset.univ : Finset α) F : ℕ) := by
      unfold orderedPairOverlap
      simp_rw [Nat.cast_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    _ ≤ qmax ^ 2 * (B * A : ℕ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrawA) (sq_nonneg qmax)

/-- Finite weighted Markov inequality in division-free form. -/
theorem weighted_markov [Fintype Ω] [DecidableEq Ω]
    (mass : Ω → ℝ) (X : Ω → ℝ) (t : ℝ)
    (hmass : ∀ ω, 0 ≤ mass ω) (hX : ∀ ω, 0 ≤ X ω) :
    t * WeightedEdgeColoring.FiniteLocalLemma.eventMass mass (upperTail X t) ≤
      ∑ ω, mass ω * X ω := by
  rw [WeightedEdgeColoring.FiniteLocalLemma.eventMass, Finset.mul_sum]
  calc
    (∑ ω ∈ upperTail X t, t * mass ω) ≤
        ∑ ω ∈ upperTail X t, mass ω * X ω := by
      apply Finset.sum_le_sum
      intro ω hω
      have ht := (Finset.mem_filter.mp hω).2
      nlinarith [hmass ω]
    _ ≤ ∑ ω, mass ω * X ω := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro ω _ _
      exact mul_nonneg (hmass ω) (hX ω)

/-- Activating more coordinates cannot decrease the pair-collision count. -/
theorem pairCollisionStatistic_mono (F : α → Finset β) :
    Monotone (pairCollisionStatistic F) := by
  intro S T hST
  unfold pairCollisionStatistic
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro r _
  by_cases hS : p ∈ S ∧ r ∈ S
  · have hT : p ∈ T ∧ r ∈ T := ⟨hST hS.1, hST hS.2⟩
    simp [hS, hT]
  · simp [hS]

/-- The upper tail of the collision statistic is an increasing event. -/
theorem pairCollisionUpperTail_isIncreasing
    (F : α → Finset β) (t : ℝ) :
    FiniteBernoulliHarris.IsIncreasing
      (upperTail (fun S ↦ (pairCollisionStatistic F S : ℝ)) t) := by
  intro S hS T hST
  simp only [upperTail, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact hS.trans (Nat.cast_le.mpr (pairCollisionStatistic_mono F hST))

end Generic

namespace RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Under slot degree `D`, an arbitrary option lies in at most `2D`
external-blocker sets for a fixed job. -/
theorem externalBlockerMultiplicity_univ_le_two_mul
    (j : Job) (o : Option) (D : ℕ)
    (hslot : ∀ s, H.slotDegree s ≤ D) :
    blockerMultiplicity (Finset.univ : Finset Option)
      (H.externalBlockedBy j) o ≤ 2 * D := by
  unfold blockerMultiplicity
  let B := (Finset.univ : Finset Option).filter fun p ↦
    o ∈ H.externalBlockedBy j p
  have hsub : B ⊆ H.optionsTouchingSlots (H.slots o) := by
    intro p hp
    have hop := (Finset.mem_filter.mp hp).2
    by_cases hpj : H.owner p = j
    · simp [externalBlockedBy, hpj] at hop
    have hop' : o ∈ H.blockedBy j p := by
      simpa [externalBlockedBy, hpj] using hop
    have hn := (H.mem_blockedBy.mp hop').2
    rw [Compatible, Finset.not_disjoint_iff] at hn
    rcases hn with ⟨s, hso, hsp⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p,
      ⟨s, Finset.mem_inter.mpr ⟨hsp, hso⟩⟩⟩
  change B.card ≤ 2 * D
  calc
    B.card ≤ (H.optionsTouchingSlots (H.slots o)).card :=
      Finset.card_le_card hsub
    _ ≤ (H.slots o).card * D :=
      H.card_optionsTouchingSlots_le (H.slots o) D (fun s _ ↦ hslot s)
    _ ≤ 2 * D := Nat.mul_le_mul_right D (H.slots_card_le_two o)

/-- Total external-blocker size is at most `2D²` when there are at most `D`
options and every job-slot codegree is at most `D`. -/
theorem sum_externalBlockedBy_card_le_two_mul_sq
    (j : Job) (D : ℕ)
    (hoption : Fintype.card Option ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ D) :
    (∑ p : Option, (H.externalBlockedBy j p).card) ≤ 2 * D ^ 2 := by
  calc
    (∑ p : Option, (H.externalBlockedBy j p).card) ≤
        ∑ _p : Option, 2 * D := by
      exact Finset.sum_le_sum fun p _ ↦
        H.externalBlockedBy_card_le_two_mul j p D
          (fun s _ ↦ hjobSlot j s)
    _ = Fintype.card Option * (2 * D) := by simp
    _ ≤ D * (2 * D) := Nat.mul_le_mul_right (2 * D) hoption
    _ = 2 * D ^ 2 := by ring

/-- Explicit `4 qmax² D³` external-collision moment bound. -/
theorem expected_externalPairCollision_le_four_mul_cube
    (q : Option → ℝ) (qmax : ℝ) (j : Job) (D : ℕ)
    (hq0 : ∀ p, 0 ≤ q p) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ p, q p ≤ qmax)
    (hoption : Fintype.card Option ≤ D)
    (hslot : ∀ s, H.slotDegree s ≤ D)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ D) :
    (∑ S : Finset Option, bernoulliMass q S *
      (pairCollisionStatistic (H.externalBlockedBy j) S : ℝ)) ≤
      qmax ^ 2 * (4 * D ^ 3 : ℕ) := by
  have h := expected_pairCollisionStatistic_le q
    (H.externalBlockedBy j) qmax (2 * D ^ 2) (2 * D)
    hq0 hqmax0 hqmax
    (fun o ↦ H.externalBlockerMultiplicity_univ_le_two_mul j o D hslot)
    (H.sum_externalBlockedBy_card_le_two_mul_sq j D hoption hjobSlot)
  convert h using 1 <;> ring

/-- Under job and slot degree `D`, an option lies in at most `3D`
slot-blocker sets, without assuming the retained set is already a matching. -/
theorem slotBlockerMultiplicity_univ_le_three_mul
    (s : Slot) (o : Option) (D : ℕ)
    (hfiber : ∀ j, (H.fiber j).card ≤ D)
    (hslot : ∀ t, H.slotDegree t ≤ D) :
    blockerMultiplicity (Finset.univ : Finset Option)
      (H.slotBlockedBy s) o ≤ 3 * D := by
  unfold blockerMultiplicity
  let B := (Finset.univ : Finset Option).filter fun p ↦
    o ∈ H.slotBlockedBy s p
  have hsub : B ⊆ H.fiber (H.owner o) ∪
      H.optionsTouchingSlots (H.slots o) := by
    intro p hp
    have hop := (Finset.mem_filter.mp hp).2
    have hbad := (Finset.mem_filter.mp hop).2
    rcases hbad with howner | hincompat
    · exact Finset.mem_union_left _ (H.mem_fiber.mpr howner.symm)
    · apply Finset.mem_union_right
      rw [Compatible, Finset.not_disjoint_iff] at hincompat
      rcases hincompat with ⟨t, hto, htp⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p,
        ⟨t, Finset.mem_inter.mpr ⟨htp, hto⟩⟩⟩
  change B.card ≤ 3 * D
  calc
    B.card ≤ (H.fiber (H.owner o) ∪
        H.optionsTouchingSlots (H.slots o)).card := Finset.card_le_card hsub
    _ ≤ (H.fiber (H.owner o)).card +
        (H.optionsTouchingSlots (H.slots o)).card := Finset.card_union_le _ _
    _ ≤ D + (H.slots o).card * D := by
      exact Nat.add_le_add (hfiber (H.owner o))
        (H.card_optionsTouchingSlots_le (H.slots o) D
          (fun t _ ↦ hslot t))
    _ ≤ D + 2 * D := by
      gcongr
      exact H.slots_card_le_two o
    _ = 3 * D := by omega

/-- Every single slot-blocker set has size at most `3D` under the three
natural degree/codegree bounds. -/
theorem slotBlockedBy_card_le_three_mul_uniform
    (s : Slot) (p : Option) (D : ℕ)
    (hslot : ∀ t, H.slotDegree t ≤ D)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ D)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ D) :
    (H.slotBlockedBy s p).card ≤ 3 * D := by
  by_cases hsp : s ∈ H.slots p
  · have hsub : H.slotBlockedBy s p ⊆
        (Finset.univ : Finset Option).filter fun o ↦ s ∈ H.slots o := by
      intro o ho
      exact (Finset.mem_filter.mp ho).1
    exact (Finset.card_le_card hsub).trans ((hslot s).trans (by omega))
  · exact H.slotBlockedBy_card_le_three_mul s p D hsp
      (hjobSlot (H.owner p) s)
      (fun t ht hst ↦ hpair s t hst)

/-- Total slot-blocker size is at most `3D²`. -/
theorem sum_slotBlockedBy_card_le_three_mul_sq
    (s : Slot) (D : ℕ)
    (hoption : Fintype.card Option ≤ D)
    (hslot : ∀ t, H.slotDegree t ≤ D)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ D)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ D) :
    (∑ p : Option, (H.slotBlockedBy s p).card) ≤ 3 * D ^ 2 := by
  calc
    (∑ p : Option, (H.slotBlockedBy s p).card) ≤
        ∑ _p : Option, 3 * D := by
      exact Finset.sum_le_sum fun p _ ↦
        H.slotBlockedBy_card_le_three_mul_uniform s p D hslot hjobSlot hpair
    _ = Fintype.card Option * (3 * D) := by simp
    _ ≤ D * (3 * D) := Nat.mul_le_mul_right (3 * D) hoption
    _ = 3 * D ^ 2 := by ring

/-- Explicit `9 qmax² D³` slot-collision moment bound. -/
theorem expected_slotPairCollision_le_nine_mul_cube
    (q : Option → ℝ) (qmax : ℝ) (s : Slot) (D : ℕ)
    (hq0 : ∀ p, 0 ≤ q p) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ p, q p ≤ qmax)
    (hoption : Fintype.card Option ≤ D)
    (hfiber : ∀ j, (H.fiber j).card ≤ D)
    (hslot : ∀ t, H.slotDegree t ≤ D)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ D)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ D) :
    (∑ S : Finset Option, bernoulliMass q S *
      (pairCollisionStatistic (H.slotBlockedBy s) S : ℝ)) ≤
      qmax ^ 2 * (9 * D ^ 3 : ℕ) := by
  have h := expected_pairCollisionStatistic_le q
    (H.slotBlockedBy s) qmax (3 * D ^ 2) (3 * D)
    hq0 hqmax0 hqmax
    (fun o ↦ H.slotBlockerMultiplicity_univ_le_three_mul
      s o D hfiber hslot)
    (H.sum_slotBlockedBy_card_le_three_mul_sq
      s D hoption hslot hjobSlot hpair)
  convert h using 1 <;> ring

end RankThreeOptionSystem

end WeightedEdgeColoring
