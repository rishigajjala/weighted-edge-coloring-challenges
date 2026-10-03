import WeightedEdgeColoring.GeneralFiniteTinyChargeAccounting

/-!
# Scalar bounds for the general finite/tiny construction

We use the reciprocal cutoff `tau = 1 / (T + 1)` and run moment mixing at
scale `4n`.  The packet base reserves `2n/5` missing colors.  Thus the fixed
mixing constants `alpha = 1/10` and `C = 1` work once `n` is large compared
with the fixed number of harmonic classes.  The same reciprocal cutoff adds
only `O(n/T)` to the `2n + O(1)` packet palette.
-/

namespace WeightedEdgeColoring

noncomputable section

/-- The tiny inflation at cutoff `1/(T+1)` is exactly `1/T`. -/
theorem reciprocalSucc_tinyInflation_eq
    {T : ℕ} (hT : 0 < T) :
    ((1 : ℝ) / (T + 1)) /
        (1 - (1 : ℝ) / (T + 1)) = (1 : ℝ) / T := by
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have hsuccR : (T : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp [hTR, hsuccR]
  ring

/-- Repacking plus tiny-charge inflation costs at most `5n/T`. -/
theorem reciprocalSucc_totalTinyOverhead_le
    {T : ℕ} (hT : 0 < T) :
    4 * ((1 : ℝ) / (T + 1)) +
        ((1 : ℝ) / (T + 1)) /
          (1 - (1 : ℝ) / (T + 1)) ≤
      5 / (T : ℝ) := by
  rw [reciprocalSucc_tinyInflation_eq hT]
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hle : (1 : ℝ) / (T + 1) ≤ 1 / T := by
    apply one_div_le_one_div_of_le hTR
    norm_num
  calc
    4 * ((1 : ℝ) / (T + 1)) + 1 / T ≤
        4 * (1 / (T : ℝ)) + 1 / T := by gcongr
    _ = 5 / (T : ℝ) := by ring

/-- Starting from the `8n/5 + 3` charge cap, the complete mixed charge and
tiny inflation are at most `(8/5 + 5/T)n + 3`. -/
theorem eightFifths_add_reciprocalOverhead_le
    {T n : ℕ} (hT : 0 < T) :
    (8 / 5 : ℝ) * n + 3 +
        (4 * ((1 : ℝ) / (T + 1)) +
          ((1 : ℝ) / (T + 1)) /
            (1 - (1 : ℝ) / (T + 1))) * n ≤
      ((8 / 5 : ℝ) + 5 / T) * n + 3 := by
  have h := reciprocalSucc_totalTinyOverhead_le hT
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_right h hn]

/-- The `5/4` ordinary-color target is `2n + O(n/T) + 15/4`. -/
theorem fiveFourth_eightFifths_reciprocalTarget_eq
    (T n : ℕ) :
    (5 / 4 : ℝ) * (((8 / 5 : ℝ) + 5 / T) * n + 3) =
      (2 + 25 / (4 * (T : ℝ))) * n + 15 / 4 := by
  by_cases hT : T = 0
  · subst T
    norm_num
    ring
  · have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    field_simp [hTR]
    ring

/-- If `25/(4T) ≤ delta`, the packet target is at most
`(2+delta)n + 15/4`. -/
theorem fiveFourth_eightFifths_reciprocalTarget_le
    {T n : ℕ} {delta : ℝ} (hT : 0 < T)
    (hdelta : 25 / (4 * (T : ℝ)) ≤ delta) :
    (5 / 4 : ℝ) * (((8 / 5 : ℝ) + 5 / T) * n + 3) ≤
      (2 + delta) * n + 15 / 4 := by
  rw [fiveFourth_eightFifths_reciprocalTarget_eq]
  have hmul := mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg n)
  nlinarith

/-- The exact `2n/5` reserve is the missing-color lower bound required by
mixing at scale `4n` with `alpha=1/10`. -/
theorem oneTenth_four_mul_le_of_twoFifths_reserve
    {J M : ℝ} {n : ℕ} (hJ : 0 ≤ J)
    (hreserve : J + (2 / 5 : ℝ) * n ≤ M) :
    (1 / 10 : ℝ) * (4 * n : ℕ) ≤ M := by
  push_cast
  nlinarith

/-- A `2n + delta*n + c` palette fits below the scale `4n` as soon as the
error and constant together cost at most `2n`. -/
theorem palette_le_four_mul
    {K n : ℕ} {delta c : ℝ}
    (hK : (K : ℝ) ≤ (2 + delta) * n + c)
    (herr : delta * n + c ≤ 2 * n) :
    K ≤ 4 * n := by
  have hreal : (K : ℝ) ≤ 4 * n := by nlinarith
  exact_mod_cast hreal

/-- The diffuse finite-class term is at most `1/40` once
`n ≥ 1000(T+1)`. -/
theorem finiteClassDiffuse_oneTenth_fourScale_le
    {T n : ℕ} (hn : 1000 * (T + 1) ≤ n) :
    (T + 1 : ℝ) *
        (1 / (((1 / 10 : ℝ) ^ 2) * (4 * n : ℕ))) ≤
      (1 / 40 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hscale : (1000 : ℝ) * (T + 1) ≤ n := by exact_mod_cast hn
  calc
    (T + 1 : ℝ) *
        (1 / (((1 / 10 : ℝ) ^ 2) * (4 * n : ℕ))) =
        25 * (T + 1) / n := by
      push_cast
      field_simp [hnpos.ne']
      ring
    _ ≤ (1 / 40 : ℝ) := by
      rw [div_le_iff₀ hnpos]
      nlinarith

/-- A positive gap below a quantity of size at most `C*n` gives a ratio
bounded away from one. -/
theorem div_le_one_sub_of_add_gap_le_general
    {J M alpha C n : ℝ}
    (hJ : 0 ≤ J) (halpha : 0 < alpha) (hC : 0 < C) (hn : 0 < n)
    (hgap : J + alpha * n ≤ M) (hupper : M ≤ C * n) :
    J / M ≤ 1 - alpha / C := by
  have hM : 0 < M := by
    have : 0 < J + alpha * n := by positivity
    exact this.trans_le hgap
  apply (div_le_iff₀ hM).2
  have hscaled : alpha * M / C ≤ alpha * n := by
    apply (div_le_iff₀ hC).2
    have hmul := mul_le_mul_of_nonneg_left hupper halpha.le
    nlinarith
  calc
    J ≤ M - alpha * n := by linarith
    _ ≤ M - alpha * M / C := by linarith
    _ = (1 - alpha / C) * M := by ring

/-- The fixed choices `alpha=1/10`, `C=1`, and scale `4n` meet the row
budget when both error terms are at most `1/40`. -/
theorem generalFiniteTiny_localBudget
    {J M eps diffuse : ℝ} {n : ℕ}
    (hn : 0 < n) (hJ : 0 ≤ J)
    (hgap : J + (1 / 10 : ℝ) * (4 * n : ℕ) ≤ M)
    (hupper : M ≤ (4 * n : ℕ))
    (heps : eps ≤ (1 / 40 : ℝ))
    (hdiffuse : diffuse ≤ (1 / 40 : ℝ)) :
    J / M + eps + diffuse ≤ 1 := by
  have hnR : (0 : ℝ) < (4 * n : ℕ) := by positivity
  have hratio := div_le_one_sub_of_add_gap_le_general
    hJ (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1)
    hnR hgap (by simpa using hupper)
  norm_num at hratio
  linarith

end

end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.generalFiniteTiny_localBudget
