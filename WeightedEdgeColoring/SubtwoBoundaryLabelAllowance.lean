import WeightedEdgeColoring.SubtwoActualLabelBudget

/-! Convert the label error to the integer allowance used by block restoration. -/

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section

/-- A fixed constant and a sufficiently small linear label error fit within
half of the padded palette. The threshold precedes the graph. -/
theorem exists_uniform_boundaryLabelAllowance
    (padding rate constant : ℝ)
    (hpadding : 0 < padding) (hrate0 : 0 ≤ rate)
    (hrate : rate ≤ padding / 20) (hconstant : 0 ≤ constant) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ D : ℕ, rate * n + constant ≤ D ∧
        5 * ((D : ℝ) + 1) ≤ (padding / 2) * n := by
  let N : ℕ := ⌈20 * (constant + 2) / padding⌉₊
  refine ⟨N, ?_⟩
  intro n hn
  let D : ℕ := ⌈rate * n + constant⌉₊
  have hx : 0 ≤ rate * n + constant := by positivity
  have hD : rate * n + constant ≤ (D : ℝ) := Nat.le_ceil _
  have hDup : (D : ℝ) < rate * n + constant + 1 :=
    Nat.ceil_lt_add_one hx
  have hN : 20 * (constant + 2) / padding ≤ (n : ℝ) := by
    calc
      _ ≤ (N : ℝ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast hn
  have hNmul := (div_le_iff₀ hpadding).1 hN
  have hrateMul := mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg n)
  refine ⟨D,hD,?_⟩
  nlinarith

theorem boundaryLabelAllowance_palette
    {n K D : ℕ} {padding kappa : ℝ}
    (hallowance : 5 * ((D : ℝ) + 1) ≤ (padding / 2) * n)
    (hK : (kappa + padding / 2) * n ≤ K) :
    (n : ℝ) * kappa + 5 * ((D : ℝ) + 1) ≤ K := by
  nlinarith

theorem boundaryLabelAllowance_normalizedCharge
    {n D : ℕ} {count exterior error : ℝ}
    (hn : 0 < n) (hcount : count ≤ exterior + error) (herror : error ≤ D) :
    count ≤ n * (exterior / n) + D := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : (n : ℝ) * (exterior / n) = exterior := by field_simp
  rw [heq]
  linarith

end
end WeightedEdgeColoring.WeightedMultigraph
