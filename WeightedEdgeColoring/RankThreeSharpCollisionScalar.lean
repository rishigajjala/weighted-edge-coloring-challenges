import WeightedEdgeColoring.RankThreeCollisionTail

/-!
# Scalar form of the uniform collision envelope

For a round with common job and slot degree bound `d` and proposal rate
`a/d`, the abstract quadratic-moment envelope has three transparent terms.
This identity is useful when choosing the moment order as a slow-growing
function of the outer asymptotic scale.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

/-- Exact expansion of the collision envelope at `J=S=d` and `rho=a/d`. -/
theorem slotCollisionMomentEnvelope_uniform_eq
    (a : ℝ) (d lambda k : ℕ) (hd : 0 < d) :
    slotCollisionMomentEnvelope (a / (d : ℝ)) d d lambda k =
      9 * a ^ 2 * d + 36 * a * k * lambda + 12 * k ^ 2 * lambda := by
  unfold slotCollisionMomentEnvelope
  push_cast
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- A direct three-term scalar comparison discharges the collision-envelope
hypothesis of the sharp round. -/
theorem slotCollisionMomentEnvelope_uniform_le
    (a eta : ℝ) (d lambda k : ℕ) (hd : 0 < d)
    (h : 9 * a ^ 2 * d + 36 * a * k * lambda +
        12 * k ^ 2 * lambda ≤ eta * d) :
    slotCollisionMomentEnvelope (a / (d : ℝ)) d d lambda k ≤ eta * d := by
  rw [slotCollisionMomentEnvelope_uniform_eq a d lambda k hd]
  exact h

/-- A convenient split of the collision budget into one half for the mean
term and one half for the two finite-moment correction terms. -/
theorem slotCollisionMomentEnvelope_uniform_le_of_split
    (a eta : ℝ) (d lambda k : ℕ) (hd : 0 < d)
    (hmean : 18 * a ^ 2 ≤ eta)
    (hcorrection : 36 * a * k * lambda + 12 * k ^ 2 * lambda ≤
      eta * d / 2) :
    slotCollisionMomentEnvelope (a / (d : ℝ)) d d lambda k ≤ eta * d := by
  apply slotCollisionMomentEnvelope_uniform_le a eta d lambda k hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmean' : 9 * a ^ 2 * d ≤ eta * d / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hmean hd0]
  linarith

end WeightedEdgeColoring.RankThreeOptionSystem
