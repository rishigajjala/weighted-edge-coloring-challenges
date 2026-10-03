import WeightedEdgeColoring.FiniteBernoulliQuadraticCollision
import WeightedEdgeColoring.RankThreeCollisionSupport

/-!
# High-moment tail for one rank-three slot-collision row

The quadratic moment bound is applied to `avoidingSlotBlockedBy`.  All
parameters are local: the largest blocker set is `3*lambda`, the largest
blocker multiplicity is `J+2*S`, and the total blocker-set size is at most
`S*(J+2*S)`.  The last theorem transfers the global estimate to the local
cylinder event used by the finite local lemma.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring.FiniteBernoulliChernoff
open WeightedEdgeColoring.FiniteBernoulliQuadraticMoment
open WeightedEdgeColoring.FiniteBernoulliSupportSplit

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Explicit upper envelope for the `k`-th collision moment at a regular
slot row. -/
noncomputable def slotCollisionMomentEnvelope
    (qmax : ℝ) (J S lambda k : ℕ) : ℝ :=
  qmax ^ 2 * ((J + 2 * S) * (S * (J + 2 * S)) : ℕ) +
    2 * k * (2 * qmax * ((3 * lambda) * (J + 2 * S) : ℕ)) +
    4 * k ^ 2 * (3 * lambda)

theorem slotCollisionMomentEnvelope_nonneg
    (qmax : ℝ) (J S lambda k : ℕ) (hqmax0 : 0 ≤ qmax) :
    0 ≤ slotCollisionMomentEnvelope qmax J S lambda k := by
  unfold slotCollisionMomentEnvelope
  positivity

/-- Degree-local mean bound for the avoiding-slot collision statistic. -/
theorem expected_avoidingSlotPairCollision_le
    (q : Option → ℝ) (qmax : ℝ) (s : Slot) (J S : ℕ)
    (hq0 : ∀ p, 0 ≤ q p) (hqmax0 : 0 ≤ qmax)
    (hqmax : ∀ p, q p ≤ qmax)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S) :
    (∑ A : Finset Option, bernoulliMass q A *
      (pairCollisionStatistic (H.avoidingSlotBlockedBy s) A : ℝ)) ≤
      qmax ^ 2 * ((J + 2 * S) * (S * (J + 2 * S)) : ℕ) := by
  apply expected_pairCollisionStatistic_le q
    (H.avoidingSlotBlockedBy s) qmax (S * (J + 2 * S)) (J + 2 * S)
    hq0 hqmax0 hqmax
  · exact fun o ↦ H.avoidingSlotBlockerMultiplicity_univ_le_job_slot
      s o J S hjobDegree hslotDegree
  · exact (H.sum_avoidingSlotBlockedBy_card_le_slotDegree_mul_add
      s J S hjobDegree hslotDegree).trans
        (Nat.mul_le_mul_right (J + 2 * S) (hslotDegree s))

/-- Raw global high-moment bound for the avoiding-slot collision count. -/
theorem avoidingSlotPairCollision_tail_mul_le
    (q : Option → ℝ) (qmax : ℝ) (s : Slot)
    (J S lambda k : ℕ) (T : ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq1 : ∀ p, q p ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ p, q p ≤ qmax)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda)
    (hT : 0 ≤ T) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass (bernoulliMass q)
      (upperTail (fun A : Finset Option ↦
        (pairCollisionStatistic (H.avoidingSlotBlockedBy s) A : ℝ)) T) ≤
      (slotCollisionMomentEnvelope qmax J S lambda k) ^ k := by
  have hmean := H.expected_avoidingSlotPairCollision_le
    q qmax s J S hq0 hqmax0 hqmax hjobDegree hslotDegree
  have htail := pairCollision_tail_mul_le q qmax
    (H.avoidingSlotBlockedBy s) (3 * lambda) (J + 2 * S) k T
    (qmax ^ 2 * ((J + 2 * S) * (S * (J + 2 * S)) : ℕ))
    hq0 hq1 hqmax0 hqmax
    (fun p ↦ H.avoidingSlotBlockedBy_card_le_three_mul
      s p lambda hjobSlot hpair)
    (fun o ↦ H.avoidingSlotBlockerMultiplicity_univ_le_job_slot
      s o J S hjobDegree hslotDegree)
    hmean hT (by positivity)
  simpa [slotCollisionMomentEnvelope] using htail

/-- The same raw bound for the local event which appears in the cylinder
local lemma. -/
theorem slotCollisionLocalBad_tail_mul_le
    (q : Option → ℝ) (qmax : ℝ) (s : Slot)
    (J S lambda k : ℕ) (T : ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq1 : ∀ p, q p ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ p, q p ≤ qmax)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda)
    (hT : 0 ≤ T) :
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (bernoulliMass (insideParameter q (H.slotCollisionSupport s)))
      (H.slotCollisionLocalBad s T) ≤
      (slotCollisionMomentEnvelope qmax J S lambda k) ^ k := by
  rw [H.slotCollisionLocalBad_mass_eq_global q s T]
  exact H.avoidingSlotPairCollision_tail_mul_le q qmax s J S lambda k T
    hq0 hq1 hqmax0 hqmax hjobDegree hslotDegree hjobSlot hpair hT

/-- If the moment envelope is at most half the threshold, the local bad
event has mass at most `2^{-k}`. -/
theorem slotCollisionLocalBad_mass_le_half_pow
    (q : Option → ℝ) (qmax : ℝ) (s : Slot)
    (J S lambda k : ℕ) (T : ℝ)
    (hq0 : ∀ p, 0 ≤ q p) (hq1 : ∀ p, q p ≤ 1)
    (hqmax0 : 0 ≤ qmax) (hqmax : ∀ p, q p ≤ qmax)
    (hjobDegree : ∀ j, (H.fiber j).card ≤ J)
    (hslotDegree : ∀ t, H.slotDegree t ≤ S)
    (hjobSlot : ∀ j t, H.jobSlotCodegree j t ≤ lambda)
    (hpair : ∀ t u, t ≠ u → H.slotPairCodegree t u ≤ lambda)
    (hT : 0 < T)
    (henvelope : slotCollisionMomentEnvelope qmax J S lambda k ≤ T / 2) :
    WeightedEdgeColoring.FiniteLocalLemma.eventMass
      (bernoulliMass (insideParameter q (H.slotCollisionSupport s)))
      (H.slotCollisionLocalBad s T) ≤ (1 / 2 : ℝ) ^ k := by
  have hraw := H.slotCollisionLocalBad_tail_mul_le
    q qmax s J S lambda k T hq0 hq1 hqmax0 hqmax
    hjobDegree hslotDegree hjobSlot hpair hT.le
  have henv0 := slotCollisionMomentEnvelope_nonneg
    qmax J S lambda k hqmax0
  have hpow :
      (slotCollisionMomentEnvelope qmax J S lambda k) ^ k ≤
        (T / 2) ^ k := pow_le_pow_left₀ henv0 henvelope k
  have hmul :
      T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
          (bernoulliMass (insideParameter q (H.slotCollisionSupport s)))
          (H.slotCollisionLocalBad s T) ≤
        T ^ k * (1 / 2 : ℝ) ^ k := by
    calc
    T ^ k * WeightedEdgeColoring.FiniteLocalLemma.eventMass
        (bernoulliMass (insideParameter q (H.slotCollisionSupport s)))
        (H.slotCollisionLocalBad s T) ≤
      (slotCollisionMomentEnvelope qmax J S lambda k) ^ k := hraw
    _ ≤ (T / 2) ^ k := hpow
    _ = T ^ k * (1 / 2 : ℝ) ^ k := by ring
  exact le_of_mul_le_mul_left hmul (pow_pos hT k)

end WeightedEdgeColoring.RankThreeOptionSystem
