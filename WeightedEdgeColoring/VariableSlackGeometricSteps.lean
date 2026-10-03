import WeightedEdgeColoring.VariableSlackIterationScalars

/-!
# An explicit `O(lambda)` round count
-/

namespace WeightedEdgeColoring

noncomputable section

/-- Number of corrected nibble rounds used to reduce the active trace to
an `epsilon` fraction when `delta=1/2`. -/
def variableSlackSteps
    (alpha gamma epsilon : ℝ) (lambda : ℕ) : ℕ :=
  Nat.ceil
    (16 * (lambda : ℝ) * Real.log (1 / epsilon) / (alpha * gamma))

/-- Fixed multiplier which bounds `variableSlackSteps/lambda`. -/
def variableSlackStepMultiplier
    (alpha gamma epsilon : ℝ) : ℝ :=
  16 * Real.log (1 / epsilon) / (alpha * gamma) + 1

theorem variableSlackSteps_cast_le
    {alpha gamma epsilon : ℝ} {lambda : ℕ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hlambda : 0 < lambda) :
    (variableSlackSteps alpha gamma epsilon lambda : ℝ) ≤
      variableSlackStepMultiplier alpha gamma epsilon * lambda := by
  have hinv : (1 : ℝ) ≤ 1 / epsilon := by
    exact (le_div_iff₀ hepsilon).2 (by simpa using hepsilon1)
  have hlog0 : 0 ≤ Real.log (1 / epsilon) := Real.log_nonneg hinv
  let x : ℝ :=
    16 * (lambda : ℝ) * Real.log (1 / epsilon) / (alpha * gamma)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    (Nat.ceil_lt_add_one hx0).le
  have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  change (Nat.ceil x : ℝ) ≤
    (16 * Real.log (1 / epsilon) / (alpha * gamma) + 1) * lambda
  calc
    (Nat.ceil x : ℝ) ≤ x + 1 := hceil
    _ ≤ x + (lambda : ℝ) := by linarith
    _ = (16 * Real.log (1 / epsilon) / (alpha * gamma) + 1) *
        (lambda : ℝ) := by
      dsimp [x]
      field_simp [halpha.ne', hgamma.ne']

/-- The chosen number of rounds makes the geometric trace term at most
`epsilon`. -/
theorem variableSlack_geometric_pow_steps_le
    {alpha gamma epsilon : ℝ} {lambda : ℕ}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hlambda : 0 < lambda) :
    (1 - (1 - (1 / 2 : ℝ)) *
        variableSlackA alpha gamma lambda / 8) ^
      variableSlackSteps alpha gamma epsilon lambda ≤ epsilon := by
  let theta : ℝ := alpha * gamma / (16 * (lambda : ℝ))
  have hlambdaR : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
  have hlambdaPos : (0 : ℝ) < lambda := by exact_mod_cast hlambda
  have htheta0 : 0 < theta := by dsimp [theta]; positivity
  have htheta1 : theta ≤ 1 := by
    dsimp [theta]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * lambda)).2
    nlinarith [mul_le_mul halpha1 hgamma1 hgamma.le (by norm_num)]
  have hbase0 : 0 ≤ 1 - theta := sub_nonneg.mpr htheta1
  have hbaseExp : 1 - theta ≤ Real.exp (-theta) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-theta)
  have hpow : (1 - theta) ^ variableSlackSteps alpha gamma epsilon lambda ≤
      (Real.exp (-theta)) ^ variableSlackSteps alpha gamma epsilon lambda :=
    pow_le_pow_left₀ hbase0 hbaseExp _
  have hinv : (1 : ℝ) ≤ 1 / epsilon := by
    exact (le_div_iff₀ hepsilon).2 (by simpa using hepsilon1)
  have hlog0 : 0 ≤ Real.log (1 / epsilon) := Real.log_nonneg hinv
  have hceil :
      16 * (lambda : ℝ) * Real.log (1 / epsilon) / (alpha * gamma) ≤
        variableSlackSteps alpha gamma epsilon lambda := by
    unfold variableSlackSteps
    exact Nat.le_ceil _
  have hthetaSteps : Real.log (1 / epsilon) ≤
      theta * variableSlackSteps alpha gamma epsilon lambda := by
    have hscaled := mul_le_mul_of_nonneg_left hceil
      (le_of_lt htheta0)
    calc
      Real.log (1 / epsilon) =
          theta * (16 * (lambda : ℝ) * Real.log (1 / epsilon) /
            (alpha * gamma)) := by
        dsimp [theta]
        field_simp [halpha.ne', hgamma.ne', hlambdaPos.ne'] <;> ring
      _ ≤ theta * variableSlackSteps alpha gamma epsilon lambda := hscaled
  have hexp : Real.exp
      (-theta * (variableSlackSteps alpha gamma epsilon lambda : ℝ)) ≤
      epsilon := by
    calc
      Real.exp (-theta *
          (variableSlackSteps alpha gamma epsilon lambda : ℝ)) ≤
          Real.exp (-Real.log (1 / epsilon)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = epsilon := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 1 / epsilon)]
        field_simp
  have hpowExp :
      (Real.exp (-theta)) ^ variableSlackSteps alpha gamma epsilon lambda =
        Real.exp
          (-theta * (variableSlackSteps alpha gamma epsilon lambda : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hfactor :
      (1 - (1 - (1 / 2 : ℝ)) *
          variableSlackA alpha gamma lambda / 8) = 1 - theta := by
    unfold variableSlackA
    dsimp [theta]
    field_simp [hlambdaPos.ne'] <;> ring
  rw [hfactor]
  exact hpow.trans (hpowExp.trans_le hexp)

end

end WeightedEdgeColoring
