import WeightedEdgeColoring.EvenCeilingPalette

/-!
# Scalar bounds for the bipartite finite-plus-tiny proof

This file isolates the numerical bookkeeping in the proof of the uniform
harmonic-charge coloring theorem.  The graph-theoretic construction uses a
mixed harmonic-charge target and then pads it to an even palette.  The
lemmas below keep that palette below four times the original scale and
absorb the fresh cleanup colors into the requested final error.
-/

namespace WeightedEdgeColoring

noncomputable section

/-- Harmonic-charge target after replacing the tiny physical edges by
endpoint packets. -/
def bipartiteMixedChargeTarget (A n tau : ℝ) : ℝ :=
  min A (2 * n) + 4 * tau * n

/-- Palette target which also pays the tiny-edge inflation and leaves a
positive gap for coordinated rounding. -/
def bipartitePaletteTarget (A n tau gamma : ℝ) : ℝ :=
  bipartiteMixedChargeTarget A n tau + tau / (1 - tau) * n + gamma * n

theorem bipartiteMixedChargeTarget_nonneg
    {A n tau : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n) (htau : 0 ≤ tau) :
    0 ≤ bipartiteMixedChargeTarget A n tau := by
  unfold bipartiteMixedChargeTarget
  positivity

theorem bipartitePaletteTarget_nonneg
    {A n tau gamma : ℝ} (hA : 0 ≤ A) (hn : 0 ≤ n)
    (htau : 0 ≤ tau) (htau1 : tau < 1) (hgamma : 0 ≤ gamma) :
    0 ≤ bipartitePaletteTarget A n tau gamma := by
  unfold bipartitePaletteTarget
  have hden : 0 ≤ 1 - tau := (sub_pos.mpr htau1).le
  have hmixed := bipartiteMixedChargeTarget_nonneg hA hn htau
  exact add_nonneg (add_nonneg hmixed
    (mul_nonneg (div_nonneg htau hden) hn)) (mul_nonneg hgamma hn)

theorem bipartitePaletteTarget_le_A
    {A n tau gamma : ℝ} (hn : 0 ≤ n) (htau : 0 ≤ tau)
    (htauHalf : tau ≤ (1 : ℝ) / 2) :
    bipartitePaletteTarget A n tau gamma ≤
      A + (6 * tau + gamma) * n := by
  have hinflate := div_one_sub_le_two_mul htau htauHalf
  unfold bipartitePaletteTarget bipartiteMixedChargeTarget
  have hmin : min A (2 * n) ≤ A := min_le_left _ _
  have hmul := mul_le_mul_of_nonneg_right hinflate hn
  linarith

theorem bipartitePaletteTarget_le_scale
    {A n tau gamma : ℝ} (hn : 0 ≤ n) (htau : 0 ≤ tau)
    (htauHalf : tau ≤ (1 : ℝ) / 2) :
    bipartitePaletteTarget A n tau gamma ≤
      (2 + 6 * tau + gamma) * n := by
  have hinflate := div_one_sub_le_two_mul htau htauHalf
  unfold bipartitePaletteTarget bipartiteMixedChargeTarget
  have hmin : min A (2 * n) ≤ 2 * n := min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_right hinflate hn
  linarith

/-- The even padded palette is at most four times the original integer
scale.  The assumptions used later give much more slack than this lemma
needs. -/
theorem evenCeiling_bipartitePaletteTarget_le_four_mul
    {A tau gamma : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (htau : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (htauGamma : tau ≤ gamma / 2)
    (hgamma : gamma ≤ (1 : ℝ) / 64) (hn : 6 ≤ n) :
    evenCeilingPalette (bipartitePaletteTarget A n tau gamma) ≤ 4 * n := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have htarget0 := bipartitePaletteTarget_nonneg hA hn0 htau
    (by linarith : tau < 1) (by linarith : 0 ≤ gamma)
  have htarget := bipartitePaletteTarget_le_scale hn0 htau htauHalf
    (A := A) (gamma := gamma)
  have hceil := evenCeilingPalette_le_add_six htarget0
  have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hreal : (evenCeilingPalette
      (bipartitePaletteTarget A n tau gamma) : ℝ) ≤ 4 * n := by
    calc
      (evenCeilingPalette
          (bipartitePaletteTarget A n tau gamma) : ℝ)
          ≤ bipartitePaletteTarget A n tau gamma + 6 := hceil
      _ ≤ (2 + 6 * tau + gamma) * n + 6 := by linarith
      _ ≤ 4 * n := by nlinarith
  exact_mod_cast hreal

/-- Real-valued form of the cleanup-color ceiling estimate. -/
theorem freshCleanupColorCount_le
    {gamma : ℝ} {n : ℕ} (hgamma : 0 ≤ gamma) :
    ((4 * Nat.ceil ((gamma / 32 + gamma / 32) * (4 * n : ℕ)) + 1 : ℕ) : ℝ)
      ≤ gamma * n + 5 := by
  have harg : 0 ≤ (gamma / 32 + gamma / 32) * (4 * n : ℕ) := by
    positivity
  have hceil := (Nat.ceil_lt_add_one harg).le
  push_cast at hceil ⊢
  nlinarith

/-- Explicit threshold making the finite-class diffuse term smaller than
one quarter of the ratio slack. -/
noncomputable def bipartiteDiffuseThreshold (T : ℕ) (gamma : ℝ) : ℕ :=
  Nat.ceil (64 * (T + 1 : ℝ) / gamma ^ 3)

theorem finiteClassDiffuseTerm_le
    {T n : ℕ} {gamma : ℝ} (hgamma : 0 < gamma) (hnpos : 0 < n)
    (hn : bipartiteDiffuseThreshold T gamma ≤ n) :
    (T + 1 : ℝ) *
        (1 / ((gamma / 4) ^ 2 * (4 * n : ℕ))) ≤ gamma / 16 := by
  have hceil : 64 * (T + 1 : ℝ) / gamma ^ 3 ≤
      (bipartiteDiffuseThreshold T gamma : ℝ) := by
    exact Nat.le_ceil _
  have hnR : (bipartiteDiffuseThreshold T gamma : ℝ) ≤ n := by
    exact_mod_cast hn
  have hlarge : 64 * (T + 1 : ℝ) / gamma ^ 3 ≤ (n : ℝ) :=
    hceil.trans hnR
  have hpow : 0 < gamma ^ 3 := pow_pos hgamma _
  have hscaled : 64 * (T + 1 : ℝ) ≤ (n : ℝ) * gamma ^ 3 := by
    exact (div_le_iff₀ hpow).mp hlarge
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hden : 0 < (gamma / 4) ^ 2 * (4 * (n : ℝ)) := by positivity
  rw [show ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) by push_cast; rfl]
  rw [one_div]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg gamma]

/-- Palette plus cleanup cost before the final asymptotic absorption. -/
theorem bipartitePalette_add_cleanup_le
    {A tau gamma : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (htau : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (htauGamma : tau ≤ gamma / 2) (hgamma : 0 ≤ gamma) :
    ((evenCeilingPalette (bipartitePaletteTarget A n tau gamma) +
        (4 * Nat.ceil ((gamma / 32 + gamma / 32) * (4 * n : ℕ)) + 1) : ℕ) : ℝ)
      ≤ A + 5 * gamma * n + 11 := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have htarget0 := bipartitePaletteTarget_nonneg hA hn0 htau
    (by linarith : tau < 1) hgamma
  have htargetA := bipartitePaletteTarget_le_A hn0 htau htauHalf
    (A := A) (gamma := gamma)
  have hpalette := evenCeilingPalette_le_add_six htarget0
  have hfresh := freshCleanupColorCount_le (n := n) hgamma
  calc
    ((evenCeilingPalette (bipartitePaletteTarget A n tau gamma) +
        (4 * Nat.ceil ((gamma / 32 + gamma / 32) * (4 * n : ℕ)) + 1) : ℕ) : ℝ)
        = (evenCeilingPalette (bipartitePaletteTarget A n tau gamma) : ℝ) +
          ((4 * Nat.ceil ((gamma / 32 + gamma / 32) * (4 * n : ℕ)) + 1 : ℕ) : ℝ) := by
            push_cast
            rfl
    _
        ≤ (bipartitePaletteTarget A n tau gamma + 6) +
          (gamma * n + 5) := add_le_add hpalette hfresh
    _ ≤ A + 5 * gamma * n + 11 := by nlinarith

/-- A convenient explicit scale threshold absorbs the eleven constant
colors left by the two ceiling operations. -/
theorem five_slack_mul_add_eleven_le_eta_mul
    {eta gamma : ℝ} {n : ℕ} (heta : 0 < eta)
    (hgamma : 5 * gamma ≤ eta / 8)
    (hn : 16 / eta ≤ (n : ℝ)) :
    5 * gamma * n + 11 ≤ eta * n := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hetan : 16 ≤ eta * n := by
    rw [div_le_iff₀ heta] at hn
    nlinarith
  have hsmall := mul_le_mul_of_nonneg_right hgamma hn0
  nlinarith

end

end WeightedEdgeColoring
