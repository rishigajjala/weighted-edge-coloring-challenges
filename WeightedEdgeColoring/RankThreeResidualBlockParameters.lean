import WeightedEdgeColoring.RankThreeResidualFixedRateCoverage

/-!
# The dyadic block size used by the residual iteration

The retained endpoint blocks should have size comparable to `S/lambda`,
where `S` is the current slot-degree cap.  Taking the ceiling of
`S/(10*lambda)` gives both inequalities needed by the one-round theorem once
`S` is at least `10*lambda`.
-/

namespace WeightedEdgeColoring

/-- Canonical endpoint-block size at slot scale `S`. -/
noncomputable def fixedRateBlockSize (lambda S : ℕ) : ℕ :=
  Nat.ceil ((S : ℝ) / (10 * (lambda : ℝ)))

theorem fixedRateBlockSize_mono (lambda : ℕ) :
    Monotone (fixedRateBlockSize lambda) := by
  intro S T hST
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (by exact_mod_cast hST)
    (mul_nonneg (by norm_num) (Nat.cast_nonneg lambda))

theorem fixedRateBlockSize_pos
    (lambda S : ℕ) (hlambda : 0 < lambda) (hS : 0 < S) :
    0 < fixedRateBlockSize lambda S := by
  have hx : (0 : ℝ) < (S : ℝ) / (10 * (lambda : ℝ)) := by positivity
  have hceil := Nat.le_ceil ((S : ℝ) / (10 * (lambda : ℝ)))
  change (S : ℝ) / (10 * (lambda : ℝ)) ≤
    (fixedRateBlockSize lambda S : ℝ) at hceil
  by_contra hzero
  have hKzero : fixedRateBlockSize lambda S = 0 := by omega
  rw [hKzero] at hceil
  norm_num at hceil
  linarith

/-- The block size is large enough for the support lower-tail estimate. -/
theorem fixedRate_groupSize_le
    (lambda S : ℕ) (hlambda : 0 < lambda) :
    S ≤ 10 * lambda * fixedRateBlockSize lambda S := by
  have hden : (0 : ℝ) < 10 * (lambda : ℝ) := by positivity
  have hceil := Nat.le_ceil ((S : ℝ) / (10 * (lambda : ℝ)))
  change (S : ℝ) / (10 * (lambda : ℝ)) ≤
    (fixedRateBlockSize lambda S : ℝ) at hceil
  have hreal : (S : ℝ) ≤
      (10 * (lambda : ℝ)) * fixedRateBlockSize lambda S := by
    rw [div_le_iff₀ hden] at hceil
    nlinarith
  exact_mod_cast hreal

/-- Above the startup scale, the ceiling block is still at most
`S/(5*lambda)`. -/
theorem fixedRate_five_mul_blockSize_le
    (lambda S : ℕ) (hlambda : 0 < lambda) (hscale : 10 * lambda ≤ S) :
    5 * lambda * fixedRateBlockSize lambda S ≤ S := by
  have hden : (0 : ℝ) < 10 * (lambda : ℝ) := by positivity
  have hx0 : (0 : ℝ) ≤ (S : ℝ) / (10 * (lambda : ℝ)) := by positivity
  have hceil := Nat.ceil_lt_add_one hx0
  change (fixedRateBlockSize lambda S : ℝ) <
    (S : ℝ) / (10 * (lambda : ℝ)) + 1 at hceil
  have hscaleR : (10 : ℝ) * (lambda : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast hscale
  have hstrict : ((5 * lambda * fixedRateBlockSize lambda S : ℕ) : ℝ) <
      (S : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    have hmul := mul_lt_mul_of_pos_left hceil
      (show (0 : ℝ) < 5 * (lambda : ℝ) by positivity)
    field_simp at hmul
    nlinarith
  have hnat : 5 * lambda * fixedRateBlockSize lambda S < S := by
    exact_mod_cast hstrict
  omega

theorem fixedRate_two_mul_blockSize_le
    (lambda S : ℕ) (hlambda : 0 < lambda) (hscale : 10 * lambda ≤ S) :
    2 * fixedRateBlockSize lambda S ≤ S := by
  have hfive := fixedRate_five_mul_blockSize_le lambda S hlambda hscale
  have hlambdaOne : 1 ≤ lambda := hlambda
  have hcoeff : 2 ≤ 5 * lambda := by omega
  exact (Nat.mul_le_mul_right (fixedRateBlockSize lambda S) hcoeff).trans
    (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hfive)

/-- Therefore the canonical block size satisfies the two-sided conditions
used by the fixed coverage-rate lemma. -/
theorem fixedRateBlockSize_window
    (lambda S : ℕ) (hlambda : 0 < lambda) (hscale : 10 * lambda ≤ S) :
    S ≤ 10 * lambda * fixedRateBlockSize lambda S ∧
      5 * lambda * fixedRateBlockSize lambda S ≤ S ∧
      2 * fixedRateBlockSize lambda S ≤ S := by
  exact ⟨fixedRate_groupSize_le lambda S hlambda,
    fixedRate_five_mul_blockSize_le lambda S hlambda hscale,
    fixedRate_two_mul_blockSize_le lambda S hlambda hscale⟩

end WeightedEdgeColoring
