import WeightedEdgeColoring.SubtwoFinitePackingMax

/-! Finitely many strict linear inequalities admit a common positive
symmetric step. Rows of zero slope may already be tight. -/

namespace WeightedEdgeColoring.Subtwo.FinitePacking

variable {R : Type*} [Fintype R]

theorem exists_small_symmetric_step (value slope cap : R → ℝ)
    (hbase : ∀ r, value r ≤ cap r)
    (hstrict : ∀ r, slope r ≠ 0 → value r < cap r) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ r,
      value r + eps * slope r ≤ cap r ∧ value r - eps * slope r ≤ cap r := by
  let A : R → Unit → ℝ := fun r _ ↦ |slope r|
  let b : R → ℝ := fun r ↦ cap r - value r
  let zero : Unit → ℝ := fun _ ↦ 0
  have hA : ∀ r e, 0 ≤ A r e := fun r _ ↦ abs_nonneg _
  have hz : Feasible zero A b zero := by
    refine ⟨fun _ ↦ le_rfl, fun _ ↦ by norm_num [zero], ?_⟩
    intro r
    simpa [zero, b] using sub_nonneg.mpr (hbase r)
  have hslack (r : R) (hr : 0 < A r ()) :
      (∑ e, A r e * zero e) < b r := by
    have hne : slope r ≠ 0 := by
      intro hh
      simp [A, hh] at hr
    simpa [zero, b] using sub_pos.mpr (hstrict r hne)
  obtain ⟨eps, heps, hfeas⟩ := exists_coordinate_increase zero A b hA zero hz ()
    (by norm_num [zero]) hslack
  refine ⟨eps, heps, ?_⟩
  intro r
  have hrow : |slope r| * eps ≤ cap r - value r := by
    simpa [A, b, zero] using hfeas.2.2 r
  have hu := mul_le_mul_of_nonneg_left (le_abs_self (slope r)) heps.le
  have hl := mul_le_mul_of_nonneg_left (neg_abs_le (slope r)) heps.le
  constructor <;> nlinarith

end WeightedEdgeColoring.Subtwo.FinitePacking
