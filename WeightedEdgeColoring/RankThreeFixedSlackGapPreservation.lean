import WeightedEdgeColoring.RankThreeFixedSlackBalance

/-!
# Preserving a fixed slot slack through a rank-three nibble

The coarse fixed-slack estimate loses half of the declared gap in one
round.  For iteration one should instead retain the positive first-order
separation between the job and slot factors.  This file records the exact
identity and its direct consequence.
-/

namespace WeightedEdgeColoring

/-- After both factors are measured against the same old slot cap
`1 - gamma`, their exact separation is `a * gamma * (1 - gamma)`.

This is the amount available to pay the two additive errors in a sharp
nibble round. -/
theorem fixedSlack_same_gap_exact_error
    (a gamma xi : ℝ) :
    (1 - gamma) * (fixedSlackJobRetention a gamma - xi) -
        (fixedSlackSlotRetention a gamma * (1 - gamma) + xi) =
      a * gamma * (1 - gamma) - xi * (2 - gamma) := by
  simp only [fixedSlackJobRetention, fixedSlackSlotRetention]
  ring

/-- A sharp round preserves the whole old slot/job gap whenever its
additive error fits inside the first-order separation. -/
theorem fixedSlack_preserves_same_gap
    (a gamma xi : ℝ)
    (herror : xi * (2 - gamma) ≤ a * gamma * (1 - gamma)) :
    fixedSlackSlotRetention a gamma * (1 - gamma) + xi ≤
      (1 - gamma) * (fixedSlackJobRetention a gamma - xi) := by
  apply sub_nonneg.mp
  rw [fixedSlack_same_gap_exact_error]
  linarith

/-- A convenient sufficient condition.  For a gap at most one half,
`xi ≤ a*gamma/4` leaves enough room to preserve that gap. -/
theorem fixedSlack_preserves_same_gap_of_four_mul
    (a gamma xi : ℝ)
    (ha0 : 0 ≤ a) (hgamma0 : 0 ≤ gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hxi0 : 0 ≤ xi) (hxi : 4 * xi ≤ a * gamma) :
    fixedSlackSlotRetention a gamma * (1 - gamma) + xi ≤
      (1 - gamma) * (fixedSlackJobRetention a gamma - xi) := by
  apply fixedSlack_preserves_same_gap
  have hag0 : 0 ≤ a * gamma := mul_nonneg ha0 hgamma0
  have hleft : xi * (2 - gamma) ≤ 2 * xi := by
    have hcoef : 2 - gamma ≤ 2 := by linarith
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hcoef hxi0
  have hmiddle : 2 * xi ≤ (a * gamma) / 2 := by linarith
  have hright : (a * gamma) / 2 ≤ a * gamma * (1 - gamma) := by
    have hfactor : (1 / 2 : ℝ) ≤ 1 - gamma := by linarith
    nlinarith
  exact hleft.trans (hmiddle.trans hright)

/-- Exact bookkeeping with independent job-side and slot-side errors.  The
slot error may combine a lower-tail loss, the `3*lambda` incidence loss, and
the quadratic collision deficit. -/
theorem fixedSlack_same_gap_separate_errors
    (a gamma jobError slotError : ℝ) :
    (1 - gamma) * (fixedSlackJobRetention a gamma - jobError) -
        (fixedSlackSlotRetention a gamma * (1 - gamma) + slotError) =
      a * gamma * (1 - gamma) -
        ((1 - gamma) * jobError + slotError) := by
  simp only [fixedSlackJobRetention, fixedSlackSlotRetention]
  ring

/-- Separate error budgets preserve the old gap when their weighted sum
fits inside the exact first-order separation. -/
theorem fixedSlack_preserves_same_gap_of_separate_errors
    (a gamma jobError slotError : ℝ)
    (herror : (1 - gamma) * jobError + slotError ≤
      a * gamma * (1 - gamma)) :
    fixedSlackSlotRetention a gamma * (1 - gamma) + slotError ≤
      (1 - gamma) *
        (fixedSlackJobRetention a gamma - jobError) := by
  apply sub_nonneg.mp
  rw [fixedSlack_same_gap_separate_errors]
  linarith

end WeightedEdgeColoring
