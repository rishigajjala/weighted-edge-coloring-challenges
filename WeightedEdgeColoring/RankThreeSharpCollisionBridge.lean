import WeightedEdgeColoring.RankThreeFixedSlackRoundBridge
import WeightedEdgeColoring.RankThreeResidualCollisionBounds
import WeightedEdgeColoring.RankThreeResidualDegreeMean

/-!
# Removing the collision loss from a regular slot row

The linear slot-deletion load equals genuine deletion plus the collision
deficit.  Twice that deficit is bounded by the ordered pair-collision
statistic.  Hence a separate upper bound on the quadratic statistic recovers
the full first-order deletion, with only the declared additive collision
budget lost.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open WeightedEdgeColoring.FiniteBernoulliChernoff

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- For concentration at an unused slot, coordinates which themselves use
the slot are irrelevant and are replaced by the empty blocker set. -/
def avoidingSlotBlockedBy (s : Slot) (p : Option) : Finset Option :=
  if s ∈ H.slots p then ∅ else H.slotBlockedBy s p

theorem avoidingSlotBlockedBy_eq_of_not_mem
    (s : Slot) (p : Option) (hps : s ∉ H.slots p) :
    H.avoidingSlotBlockedBy s p = H.slotBlockedBy s p := by
  simp [avoidingSlotBlockedBy, hps]

/-- Every coordinate in the concentration statistic has local influence set
of size at most `3*lambda`. -/
theorem avoidingSlotBlockedBy_card_le_three_mul
    (s : Slot) (p : Option) (lambda : ℕ)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda) :
    (H.avoidingSlotBlockedBy s p).card ≤ 3 * lambda := by
  by_cases hps : s ∈ H.slots p
  · simp [avoidingSlotBlockedBy, hps]
  · simpa [avoidingSlotBlockedBy, hps] using
      H.slotBlockedBy_card_le_three_mul s p lambda hps
        (hjobSlot (H.owner p) s)
        (fun t ht hst ↦ hpair s t hst)

private theorem collisionDeficit_congr_on
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (F G : α → Finset β)
    (hFG : ∀ p ∈ A, F p = G p) :
    collisionDeficit A F = collisionDeficit A G := by
  have hunion : A.biUnion F = A.biUnion G := by
    exact Finset.biUnion_congr rfl hFG
  unfold collisionDeficit
  rw [hunion]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  unfold blockerMultiplicity
  apply congrArg Finset.card
  ext p
  by_cases hp : p ∈ A
  · simp [hp, hFG p hp]
  · simp [hp]

/-- On an outcome which leaves `s` unused, replacing irrelevant coordinates
by empty sets does not change the collision deficit. -/
theorem collisionDeficit_avoidingSlotBlockedBy_eq
    (A : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ A, s ∉ H.slots p) :
    collisionDeficit A (H.avoidingSlotBlockedBy s) =
      collisionDeficit A (H.slotBlockedBy s) := by
  apply collisionDeficit_congr_on A
  intro p hp
  exact H.avoidingSlotBlockedBy_eq_of_not_mem s p (hunused p hp)

private theorem collisionDeficit_insert_le_add_card
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (A : Finset α) (F : α → Finset β) (p : α) :
    collisionDeficit (insert p A) F ≤
      collisionDeficit A F + (F p).card := by
  by_cases hp : p ∈ A
  · simpa [Finset.insert_eq_of_mem hp]
  · have hnew := sum_card_eq_card_biUnion_add_collisionDeficit
      (insert p A) F
    have hold := sum_card_eq_card_biUnion_add_collisionDeficit A F
    have hunion : (A.biUnion F).card ≤ ((insert p A).biUnion F).card := by
      apply Finset.card_le_card
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨a, ha, hxa⟩
      exact Finset.mem_biUnion.mpr
        ⟨a, Finset.mem_insert_of_mem ha, hxa⟩
    rw [Finset.sum_insert hp] at hnew
    omega

/-- Adding one Bernoulli coordinate changes the avoiding-slot collision
deficit by at most `3*lambda`.  This is the bounded-influence input for a
certifiable-function tail inequality. -/
theorem collisionDeficit_insert_le_add_three_mul
    (A : Finset Option) (s : Slot) (p : Option) (lambda : ℕ)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda) :
    collisionDeficit (insert p A) (H.avoidingSlotBlockedBy s) ≤
      collisionDeficit A (H.avoidingSlotBlockedBy s) + 3 * lambda := by
  exact (collisionDeficit_insert_le_add_card
    A (H.avoidingSlotBlockedBy s) p).trans
      (Nat.add_le_add_left
        (H.avoidingSlotBlockedBy_card_le_three_mul
          s p lambda hjobSlot hpair) _)

/-- Integer form: if the linear load pays for `L` genuine deletions plus a
collision allowance `C`, and the ordered collision statistic is at most
`2C`, then at least `L` options really disappear from the unused slot. -/
theorem residualSlotDegree_add_le_of_linearLoad_pairCollision
    (A : Finset Option) (s : Slot)
    (hunused : ∀ p ∈ A, s ∉ H.slots p)
    (L C : ℕ)
    (hload : L + C ≤ H.slotDeletionLoad A s)
    (hcollision : pairCollisionStatistic (H.slotBlockedBy s) A ≤ 2 * C) :
    H.residualSlotDegree A s + L ≤ H.residualSlotDegree ∅ s := by
  have hdeficit2 := two_mul_collisionDeficit_le_pairCollisionStatistic
    A (H.slotBlockedBy s)
  have hdeficit : collisionDeficit A (H.slotBlockedBy s) ≤ C := by omega
  have hexact := H.slotDeletionLoad_eq_removed_add_collisionDeficit
    A s hunused
  have hremoved : L ≤ (H.removedResidualSlot ∅ A s).card := by omega
  have hid := H.residualSlotDegree_union_add_removed ∅ A s
  simp only [Finset.empty_union] at hid
  omega

/-- Real-valued fixed-slack bridge with the collision hypothesis stated in
terms of the quadratic statistic naturally controlled by a degree-two tail
bound. -/
theorem fixedSlack_balance_of_jobLoss_slotLoad_pairCollision
    (A : Finset Option) (d : ℕ) (a gamma xi : ℝ)
    (hjobInitial : ∀ j, d ≤ H.residualJobDegree ∅ j)
    (hjobLoss : ∀ j, ¬ H.Covers A j →
      ((H.removedResidualFiber ∅ A j).card : ℝ) ≤
        (2 * a * (1 - gamma) + xi) * d)
    (hslotInitial : ∀ s,
      (H.residualSlotDegree ∅ s : ℝ) ≤ (1 - gamma) * d)
    (hslotLoad : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      a * (2 - gamma) * (1 - gamma) * d ≤
        (H.slotDeletionLoad A s : ℝ))
    (hslotPairCollision : ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (pairCollisionStatistic (H.slotBlockedBy s) A : ℝ) ≤
        2 * xi * d) :
    (∀ j, ¬ H.Covers A j →
      (WeightedEdgeColoring.fixedSlackJobRetention a gamma - xi) * d ≤
        H.residualJobDegree A j) ∧
    (∀ s, (∀ p ∈ A, s ∉ H.slots p) →
      (H.residualSlotDegree A s : ℝ) ≤
        (WeightedEdgeColoring.fixedSlackSlotRetention a gamma * (1 - gamma) + xi) * d) := by
  apply H.fixedSlack_balance_of_jobLoss_slotLoad_collision A d a gamma xi
    hjobInitial hjobLoss hslotInitial hslotLoad
  intro s hunused
  have htwo := two_mul_collisionDeficit_le_pairCollisionStatistic
    A (H.slotBlockedBy s)
  have htwoReal :
      (2 : ℝ) * collisionDeficit A (H.slotBlockedBy s) ≤
        pairCollisionStatistic (H.slotBlockedBy s) A := by
    exact_mod_cast htwo
  have hpair := hslotPairCollision s hunused
  push_cast at hpair
  nlinarith

/-- Degree-local quadratic moment for a regular slot row.  Unlike the older
coarse bound, this estimate does not contain the total number of options. -/
theorem expected_slotPairCollision_le_job_slot
    (q : Option → ℝ) (qmax : ℝ) (s : Slot) (J S : ℕ)
    (hq0 : ∀ p, 0 ≤ q p) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ p, q p ≤ qmax)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    (∑ A : Finset Option, bernoulliMass q A *
      (pairCollisionStatistic (H.slotBlockedBy s) A : ℝ)) ≤
      qmax ^ 2 * ((J + 2 * S) * (H.slotDegree s * (J + 2 * S)) : ℕ) := by
  exact expected_pairCollisionStatistic_le q (H.slotBlockedBy s)
    qmax (H.slotDegree s * (J + 2 * S)) (J + 2 * S)
    hq0 hqmax0 hqmax
    (fun o ↦ H.slotBlockerMultiplicity_univ_le_job_slot
      s o J S hjobDegree hslotDegree)
    (H.sum_slotBlockedBy_card_le_slotDegree_mul_add
      s J S hjobDegree hslotDegree)

end WeightedEdgeColoring.RankThreeOptionSystem
