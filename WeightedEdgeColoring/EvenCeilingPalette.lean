import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# A padded even ceiling

The finite-plus-tiny mixing theorem asks for an even palette with at least
four colors.  `evenCeilingPalette B` is an even integer above a nonnegative
real target `B` and less than `B + 6`.
-/

namespace WeightedEdgeColoring

/-- A small positive error share used by the bipartite proof. -/
noncomputable def bipartiteProofSlack (eta : ℝ) : ℝ :=
  min (eta / 64) (1 / 64)

theorem bipartiteProofSlack_pos {eta : ℝ} (heta : 0 < eta) :
    0 < bipartiteProofSlack eta := by
  unfold bipartiteProofSlack
  exact lt_min (div_pos heta (by norm_num)) (by norm_num)

theorem bipartiteProofSlack_le_eta_div (eta : ℝ) :
    bipartiteProofSlack eta ≤ eta / 64 := by
  exact min_le_left _ _

theorem bipartiteProofSlack_le_one_div (eta : ℝ) :
    bipartiteProofSlack eta ≤ (1 : ℝ) / 64 := by
  exact min_le_right _ _

theorem five_mul_bipartiteProofSlack_le_eta_eighth
    {eta : ℝ} (heta : 0 < eta) :
    5 * bipartiteProofSlack eta ≤ eta / 8 := by
  have h := bipartiteProofSlack_le_eta_div eta
  linarith

/-- An even integer palette, padded by four colors. -/
noncomputable def evenCeilingPalette (B : ℝ) : ℕ :=
  2 * (Nat.ceil (B / 2) + 2)

theorem even_evenCeilingPalette (B : ℝ) : Even (evenCeilingPalette B) := by
  exact even_two_mul _

theorem four_le_evenCeilingPalette (B : ℝ) :
    4 ≤ evenCeilingPalette B := by
  unfold evenCeilingPalette
  omega

theorem evenCeilingPalette_pos (B : ℝ) :
    0 < evenCeilingPalette B :=
  (by omega : 0 < 2 * (Nat.ceil (B / 2) + 2))

theorem le_evenCeilingPalette (B : ℝ) :
    B ≤ (evenCeilingPalette B : ℝ) := by
  have hceil : B / 2 ≤ (Nat.ceil (B / 2) : ℝ) := Nat.le_ceil _
  unfold evenCeilingPalette
  push_cast
  linarith

theorem evenCeilingPalette_lt_add_six {B : ℝ} (hB : 0 ≤ B) :
    (evenCeilingPalette B : ℝ) < B + 6 := by
  have hhalf : 0 ≤ B / 2 := div_nonneg hB (by norm_num)
  have hceil := Nat.ceil_lt_add_one hhalf
  unfold evenCeilingPalette
  push_cast
  linarith

theorem evenCeilingPalette_le_add_six {B : ℝ} (hB : 0 ≤ B) :
    (evenCeilingPalette B : ℝ) ≤ B + 6 :=
  (evenCeilingPalette_lt_add_six hB).le

/-- There is an integer denominator at least two whose reciprocal is below
any requested positive accuracy. -/
theorem exists_nat_two_le_one_div_lt {gamma : ℝ} (hgamma : 0 < gamma) :
    ∃ t : ℕ, 2 ≤ t ∧ (1 : ℝ) / t < gamma := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgamma
  refine ⟨m + 2, by omega, ?_⟩
  have hden : (0 : ℝ) < m + 1 := by positivity
  have hle : (m : ℝ) + 1 ≤ (m + 2 : ℕ) := by
    push_cast
    linarith
  calc
    (1 : ℝ) / (m + 2 : ℕ) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le hden hle
    _ < gamma := hm

/-- Reciprocal threshold used to separate finite harmonic classes from the
tiny tail. -/
noncomputable def reciprocalTinyThreshold (t : ℕ) : ℝ :=
  1 / (2 * (t : ℝ))

theorem reciprocalTinyThreshold_pos {t : ℕ} (ht : 0 < t) :
    0 < reciprocalTinyThreshold t := by
  unfold reciprocalTinyThreshold
  positivity

theorem reciprocalTinyThreshold_le_half {t : ℕ} (ht : 1 ≤ t) :
    reciprocalTinyThreshold t ≤ (1 : ℝ) / 2 := by
  unfold reciprocalTinyThreshold
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hden : (0 : ℝ) < 2 := by norm_num
  apply (div_le_iff₀ (mul_pos hden (by positivity : (0 : ℝ) < t))).2
  nlinarith

theorem two_mul_reciprocalTinyThreshold {t : ℕ} (ht : 0 < t) :
    2 * reciprocalTinyThreshold t = (1 : ℝ) / t := by
  unfold reciprocalTinyThreshold
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp [htR]

theorem inv_double_eq_reciprocalTinyThreshold (t : ℕ) :
    (1 : ℝ) / (2 * t : ℕ) = reciprocalTinyThreshold t := by
  unfold reciprocalTinyThreshold
  push_cast
  rfl

theorem inv_le_four_mul_reciprocalTinyThreshold {t : ℕ} (ht : 0 < t) :
    (1 : ℝ) / t ≤ 4 * reciprocalTinyThreshold t := by
  rw [← two_mul_reciprocalTinyThreshold ht]
  have hpos := reciprocalTinyThreshold_pos ht
  linarith

theorem reciprocalTinyThreshold_lt_half {t : ℕ} {gamma : ℝ}
    (ht : 0 < t) (hinv : (1 : ℝ) / t < gamma) :
    reciprocalTinyThreshold t < gamma / 2 := by
  rw [← two_mul_reciprocalTinyThreshold ht] at hinv
  linarith

theorem div_one_sub_le_two_mul {tau : ℝ}
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2) :
    tau / (1 - tau) ≤ 2 * tau := by
  have hden : 0 < 1 - tau := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith

end WeightedEdgeColoring
