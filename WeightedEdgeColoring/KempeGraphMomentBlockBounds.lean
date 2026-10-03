import WeightedEdgeColoring.KempeComponentActiveIndicator

/-!
# Uniform bounds for one Kempe moment block

For one switched color pair, first-moment rows and the `n`-scaled second-
moment rows have bounded total mass.  At one active endpoint their complete
row-cap mass is linear in `n`, while every individual cap is `O(1/n)`.
These are the three numerical inputs to the component-coin selector.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics
open WeightedEdgeColoring.FiniteCategoricalSelection

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

theorem momentBlockVertexCap_nonneg {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (w : G.V) (row : MomentBlockRow G.V q) :
    0 ≤ G.momentBlockVertexCap (n := n) R charge F color a b w row := by
  cases row with
  | first v side =>
      change 0 ≤ G.firstLinkCharge R charge F color v w
      exact G.firstLinkCharge_nonneg R charge F color hcharge v w
  | diagonal v side =>
      change 0 ≤ (n : ℝ) * G.secondLinkCharge R charge F color v w
      exact mul_nonneg (Nat.cast_nonneg n)
        (G.secondLinkCharge_nonneg R charge F color hcharge v w)
  | pair v side d =>
      change 0 ≤ if d = a ∨ d = b then 0 else
        (n : ℝ) * G.secondLinkCharge R charge F color v w *
          paletteIndicator (G.missingColorsAt F color w) d
      split
      · exact le_rfl
      · exact mul_nonneg
          (mul_nonneg (Nat.cast_nonneg n)
            (G.secondLinkCharge_nonneg R charge F color hcharge v w))
          (paletteIndicator_nonneg _ _)

/-- For a fixed receiving vertex, the first-link charges over all opposite
endpoints have total at most `1/alpha`. -/
theorem sum_firstLinkCharge_left_le_inv_alpha {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ v, G.restrictedCharge R charge v ≤ n)
    (v : G.V) :
    (∑ w : G.V, G.firstLinkCharge R charge F color v w) ≤
      1 / alpha := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < alpha * (n : ℝ) := mul_pos halpha hnreal
  simp_rw [G.firstLinkCharge_eq_pairCharge_div R charge F color]
  calc
    (∑ w : G.V,
      G.pairCharge R charge v w / G.momentMissingSize F color w) ≤
        ∑ w : G.V,
          G.pairCharge R charge v w / (alpha * n) := by
      apply Finset.sum_le_sum
      intro w _hw
      exact div_le_div_of_nonneg_left
        (G.pairCharge_nonneg R charge hcharge v w) hden
        (hmissing w)
    _ = G.restrictedCharge R charge v / (alpha * n) := by
      rw [← Finset.sum_div, G.sum_pairCharge]
    _ ≤ (n : ℝ) / (alpha * n) :=
      div_le_div_of_nonneg_right (hrestricted v) hden.le
    _ = 1 / alpha := by field_simp

/-- The `n`-scaled second-link charges have total at most `1/alpha^2`. -/
theorem sum_n_mul_secondLinkCharge_left_le_inv_alpha_sq {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ v, G.restrictedCharge R charge v ≤ n)
    (v : G.V) :
    (∑ w : G.V,
      (n : ℝ) * G.secondLinkCharge R charge F color v w) ≤
      1 / alpha ^ 2 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < alpha * (n : ℝ) := mul_pos halpha hnreal
  simp_rw [G.secondLinkCharge_eq_pairCharge_div_sq R charge F color]
  calc
    (∑ w : G.V,
      (n : ℝ) *
        (G.pairCharge R charge v w /
          (G.momentMissingSize F color w) ^ 2)) =
        ∑ w : G.V,
          ((n : ℝ) * G.pairCharge R charge v w) /
            (G.momentMissingSize F color w) ^ 2 := by
      apply Finset.sum_congr rfl
      intro w _hw
      ring
    _ ≤ ∑ w : G.V,
          ((n : ℝ) * G.pairCharge R charge v w) /
            (alpha * n) ^ 2 := by
      apply Finset.sum_le_sum
      intro w _hw
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg hnreal.le
          (G.pairCharge_nonneg R charge hcharge v w)
      · exact sq_pos_of_pos hden
      · exact (sq_le_sq₀ hden.le (hden.le.trans (hmissing w))).2
          (hmissing w)
    _ = (n : ℝ) * G.restrictedCharge R charge v /
          (alpha * n) ^ 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum, G.sum_pairCharge]
    _ ≤ (n : ℝ) * n / (alpha * n) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hrestricted v) hnreal.le)
        (sq_nonneg _)
    _ = 1 / alpha ^ 2 := by field_simp

/-- The same bounds with the opposite endpoint fixed follow directly from
the exact link-sum identities. -/
theorem sum_firstLinkCharge_right_le_inv_alpha {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (w : G.V) :
    (∑ v : G.V, G.firstLinkCharge R charge F color v w) ≤
      1 / alpha := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < G.momentMissingSize F color w :=
    (mul_pos halpha hnreal).trans_le (hmissing w)
  rw [G.sum_firstLinkCharge]
  calc
    G.restrictedCharge R charge w / G.momentMissingSize F color w ≤
        (n : ℝ) / G.momentMissingSize F color w :=
      div_le_div_of_nonneg_right (hrestricted w) hden.le
    _ ≤ (n : ℝ) / (alpha * n) :=
      div_le_div_of_nonneg_left hnreal.le (mul_pos halpha hnreal)
        (hmissing w)
    _ = 1 / alpha := by field_simp

theorem sum_n_mul_secondLinkCharge_right_le_inv_alpha_sq {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (w : G.V) :
    (∑ v : G.V,
      (n : ℝ) * G.secondLinkCharge R charge F color v w) ≤
      1 / alpha ^ 2 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < G.momentMissingSize F color w :=
    (mul_pos halpha hnreal).trans_le (hmissing w)
  rw [← Finset.mul_sum, G.sum_secondLinkCharge]
  calc
    (n : ℝ) *
        (G.restrictedCharge R charge w /
          (G.momentMissingSize F color w) ^ 2) ≤
      (n : ℝ) *
        ((n : ℝ) / (G.momentMissingSize F color w) ^ 2) := by
      gcongr
      exact hrestricted w
    _ ≤ (n : ℝ) * ((n : ℝ) / (alpha * n) ^ 2) := by
      gcongr
      exact hmissing w
    _ = 1 / alpha ^ 2 := by field_simp

/-- Every statistic row has cap mass at most the common constant `M`. -/
theorem sum_momentBlockVertexCap_le_rowMass {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ v, G.restrictedCharge R charge v ≤ n)
    (row : MomentBlockRow G.V q) :
    (∑ w : G.V,
      G.momentBlockVertexCap (n := n) R charge F color a b w row) ≤
      1 / alpha + 1 / alpha ^ 2 := by
  have hinv0 : 0 ≤ (1 : ℝ) / alpha :=
    div_nonneg zero_le_one halpha.le
  have hinvsq0 : 0 ≤ (1 : ℝ) / alpha ^ 2 :=
    div_nonneg zero_le_one (sq_nonneg alpha)
  cases row with
  | first v side =>
      change (∑ w : G.V,
        G.firstLinkCharge R charge F color v w) ≤
          1 / alpha + 1 / alpha ^ 2
      exact (sum_firstLinkCharge_left_le_inv_alpha (G := G) (n := n)
        R charge F color alpha halpha hn hcharge hmissing hrestricted v).trans
        (le_add_of_nonneg_right hinvsq0)
  | diagonal v side =>
      change (∑ w : G.V,
        (n : ℝ) * G.secondLinkCharge R charge F color v w) ≤
          1 / alpha + 1 / alpha ^ 2
      exact (sum_n_mul_secondLinkCharge_left_le_inv_alpha_sq
        (G := G) (n := n)
        R charge F color alpha halpha hn hcharge hmissing hrestricted v).trans
        (le_add_of_nonneg_left hinv0)
  | pair v side d =>
      change (∑ w : G.V,
        if d = a ∨ d = b then 0 else
          (n : ℝ) * G.secondLinkCharge R charge F color v w *
            paletteIndicator (G.missingColorsAt F color w) d) ≤
        1 / alpha + 1 / alpha ^ 2
      by_cases hd : d = a ∨ d = b
      · simpa [hd] using add_nonneg hinv0 hinvsq0
      · simp only [hd, if_false]
        calc
          (∑ w : G.V,
            (n : ℝ) * G.secondLinkCharge R charge F color v w *
              paletteIndicator (G.missingColorsAt F color w) d) ≤
              ∑ w : G.V,
                (n : ℝ) * G.secondLinkCharge R charge F color v w := by
            apply Finset.sum_le_sum
            intro w _hw
            exact mul_le_of_le_one_right
              (mul_nonneg (Nat.cast_nonneg n)
                (G.secondLinkCharge_nonneg
                  R charge F color hcharge v w))
              (paletteIndicator_le_one _ _)
          _ ≤ 1 / alpha ^ 2 :=
            sum_n_mul_secondLinkCharge_left_le_inv_alpha_sq
              (G := G) (n := n)
              R charge F color alpha halpha hn hcharge hmissing
              hrestricted v
          _ ≤ 1 / alpha + 1 / alpha ^ 2 :=
            le_add_of_nonneg_left hinv0

/-- The cap sum over active endpoints and components inherits the same row
bound. -/
theorem sum_componentInfluenceCap_momentBlock_le_rowMass {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ v, G.restrictedCharge R charge v ≤ n)
    (row : MomentBlockRow G.V q) :
    (∑ component : G.TwoColorComponent F color a b,
      G.componentInfluenceCap F color a b
        (G.momentBlockVertexCap (n := n) R charge F color a b)
        component row) ≤
      1 / alpha + 1 / alpha ^ 2 := by
  rw [show
      (∑ component : G.TwoColorComponent F color a b,
        G.componentInfluenceCap F color a b
          (G.momentBlockVertexCap (n := n) R charge F color a b)
          component row) =
        ∑ w : G.V,
          if G.IsTwoColorActive F color a b w then
            G.momentBlockVertexCap (n := n)
              R charge F color a b w row else 0 by
    simpa only [componentInfluenceCap] using
      (G.sum_activeVerticesInComponent F color a b
        (fun w ↦ G.momentBlockVertexCap (n := n)
          R charge F color a b w row))]
  calc
    (∑ w : G.V,
      if G.IsTwoColorActive F color a b w then
        G.momentBlockVertexCap (n := n)
          R charge F color a b w row else 0) ≤
        ∑ w : G.V,
          G.momentBlockVertexCap (n := n)
            R charge F color a b w row := by
      apply Finset.sum_le_sum
      intro w _hw
      split
      · exact le_rfl
      · exact momentBlockVertexCap_nonneg (G := G) (n := n)
          R charge F color a b hcharge w row
    _ ≤ 1 / alpha + 1 / alpha ^ 2 :=
      sum_momentBlockVertexCap_le_rowMass (G := G) (n := n)
        R charge F color a b alpha halpha hn hcharge hmissing
        hrestricted row

theorem rowMean_momentBlockUse_nonneg {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (row : MomentBlockRow G.V q) :
    0 ≤ rowMean
      (fun (_component : G.TwoColorComponent F color a b)
        (_bit : Bool) ↦ (1 : ℝ) / 2)
      (G.momentBlockUse (n := n) R charge F color a b) row := by
  unfold rowMean
  apply Finset.sum_nonneg
  intro component _hcomponent
  apply Finset.sum_nonneg
  intro bit _hbit
  exact mul_nonneg (by norm_num)
    (G.momentBlockUse_nonneg (n := n) R charge F color a b hcharge
      component bit row)

/-- The fair mean is at most the cap mass of the row. -/
theorem rowMean_momentBlockUse_le_componentCap {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (row : MomentBlockRow G.V q) :
    rowMean
      (fun (_component : G.TwoColorComponent F color a b)
        (_bit : Bool) ↦ (1 : ℝ) / 2)
      (G.momentBlockUse (n := n) R charge F color a b) row ≤
      ∑ component : G.TwoColorComponent F color a b,
        G.componentInfluenceCap F color a b
          (G.momentBlockVertexCap (n := n) R charge F color a b)
          component row := by
  unfold rowMean
  calc
    (∑ component : G.TwoColorComponent F color a b,
      ∑ bit : Bool, (1 : ℝ) / 2 *
        G.momentBlockUse (n := n)
          R charge F color a b component bit row) ≤
        ∑ component : G.TwoColorComponent F color a b,
          ∑ _bit : Bool, (1 : ℝ) / 2 *
            G.componentInfluenceCap F color a b
              (G.momentBlockVertexCap (n := n) R charge F color a b)
              component row := by
      apply Finset.sum_le_sum
      intro component _hcomponent
      apply Finset.sum_le_sum
      intro bit _hbit
      exact mul_le_mul_of_nonneg_left
        (G.momentBlockUse_le_componentInfluenceCap (n := n)
          R charge F color a b hcharge component bit row) (by norm_num)
    _ = ∑ component : G.TwoColorComponent F color a b,
        G.componentInfluenceCap F color a b
          (G.momentBlockVertexCap (n := n) R charge F color a b)
          component row := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      simp

theorem rowMean_momentBlockUse_le_rowMass {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ v, G.restrictedCharge R charge v ≤ n)
    (row : MomentBlockRow G.V q) :
    rowMean
      (fun (_component : G.TwoColorComponent F color a b)
        (_bit : Bool) ↦ (1 : ℝ) / 2)
      (G.momentBlockUse (n := n) R charge F color a b) row ≤
      1 / alpha + 1 / alpha ^ 2 := by
  exact (rowMean_momentBlockUse_le_componentCap (G := G) (n := n)
    R charge F color a b hcharge row).trans
      (sum_componentInfluenceCap_momentBlock_le_rowMass
        (G := G) (n := n)
        R charge F color a b alpha halpha hn hcharge hmissing
        hrestricted row)

theorem componentCap_sub_rowMean_momentBlockUse_le_rowMass {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ v, G.restrictedCharge R charge v ≤ n)
    (row : MomentBlockRow G.V q) :
    (∑ component : G.TwoColorComponent F color a b,
      G.componentInfluenceCap F color a b
        (G.momentBlockVertexCap (n := n) R charge F color a b)
        component row) -
      rowMean
        (fun (_component : G.TwoColorComponent F color a b)
          (_bit : Bool) ↦ (1 : ℝ) / 2)
        (G.momentBlockUse (n := n) R charge F color a b) row ≤
      1 / alpha + 1 / alpha ^ 2 := by
  exact (sub_le_self _
    (rowMean_momentBlockUse_nonneg (G := G) (n := n)
      R charge F color a b hcharge row)).trans
    (sum_componentInfluenceCap_momentBlock_le_rowMass
      (G := G) (n := n)
      R charge F color a b alpha halpha hn hcharge hmissing
      hrestricted row)

/-- At one active endpoint the total cap over every tracked row is linear
in `n` (and, more explicitly, linear in the palette size `q`). -/
theorem sum_momentBlockVertexCap_le_columnMass {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (alpha : ℝ) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (w : G.V) :
    (∑ row : MomentBlockRow G.V q,
      G.momentBlockVertexCap (n := n) R charge F color a b w row) ≤
      2 * (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2) := by
  have hfirst := sum_firstLinkCharge_right_le_inv_alpha
    (G := G) (n := n)
    R charge F color alpha halpha hn hmissing hrestricted w
  have hsecond := sum_n_mul_secondLinkCharge_right_le_inv_alpha_sq
    (G := G) (n := n)
    R charge F color alpha halpha hn hmissing hrestricted w
  rw [sum_momentBlockRow]
  have hFirstFamily :
      (∑ v : G.V, ∑ side : Bool,
        G.momentBlockVertexCap (n := n)
          R charge F color a b w (.first v side)) ≤
        2 * (1 / alpha) := by
    calc
      (∑ v : G.V, ∑ side : Bool,
        G.momentBlockVertexCap (n := n)
          R charge F color a b w (.first v side)) =
          2 * ∑ v : G.V, G.firstLinkCharge R charge F color v w := by
        simp [momentBlockVertexCap, Finset.mul_sum]
      _ ≤ 2 * (1 / alpha) := mul_le_mul_of_nonneg_left hfirst (by norm_num)
  have hDiagonalFamily :
      (∑ v : G.V, ∑ side : Bool,
        G.momentBlockVertexCap (n := n) R charge F color a b w
          (.diagonal v side)) ≤ 2 * (1 / alpha ^ 2) := by
    calc
      (∑ v : G.V, ∑ side : Bool,
        G.momentBlockVertexCap (n := n) R charge F color a b w
          (.diagonal v side)) =
          2 * ∑ v : G.V,
            (n : ℝ) * G.secondLinkCharge R charge F color v w := by
        simp [momentBlockVertexCap, Finset.mul_sum]
      _ ≤ 2 * (1 / alpha ^ 2) :=
        mul_le_mul_of_nonneg_left hsecond (by norm_num)
  have hPairFamily :
      (∑ v : G.V, ∑ side : Bool, ∑ d : Fin q,
        G.momentBlockVertexCap (n := n)
          R charge F color a b w (.pair v side d)) ≤
        2 * (q : ℝ) * (1 / alpha ^ 2) := by
    calc
      (∑ v : G.V, ∑ side : Bool, ∑ d : Fin q,
        G.momentBlockVertexCap (n := n)
          R charge F color a b w (.pair v side d)) ≤
          ∑ v : G.V, ∑ _side : Bool, ∑ _d : Fin q,
            (n : ℝ) * G.secondLinkCharge R charge F color v w := by
        apply Finset.sum_le_sum
        intro v _hv
        apply Finset.sum_le_sum
        intro side _hside
        apply Finset.sum_le_sum
        intro d _hd
        change (if d = a ∨ d = b then 0 else
            (n : ℝ) * G.secondLinkCharge R charge F color v w *
              paletteIndicator (G.missingColorsAt F color w) d) ≤
          (n : ℝ) * G.secondLinkCharge R charge F color v w
        by_cases hd : d = a ∨ d = b
        · rw [if_pos hd]
          exact mul_nonneg (Nat.cast_nonneg n)
            (G.secondLinkCharge_nonneg
              R charge F color hcharge v w)
        · rw [if_neg hd]
          exact mul_le_of_le_one_right
            (mul_nonneg (Nat.cast_nonneg n)
              (G.secondLinkCharge_nonneg
                R charge F color hcharge v w))
            (paletteIndicator_le_one _ _)
      _ = 2 * (q : ℝ) *
          (∑ v : G.V,
            (n : ℝ) * G.secondLinkCharge R charge F color v w) := by
        simp [Finset.mul_sum]
        ring
      _ ≤ 2 * (q : ℝ) * (1 / alpha ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsecond
          (mul_nonneg (by norm_num) (Nat.cast_nonneg q))
  calc
    _ ≤ 2 * (1 / alpha) + 2 * (1 / alpha ^ 2) +
          2 * (q : ℝ) * (1 / alpha ^ 2) :=
      add_le_add (add_le_add hFirstFamily hDiagonalFamily) hPairFamily
    _ = 2 * (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2) := by ring

end

end WeightedMultigraph
end WeightedEdgeColoring
