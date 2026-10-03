import WeightedEdgeColoring.GeneralFiniteTinyParameterBounds

/-! Fixed five-label padding in the weighted-moment local row. -/

namespace WeightedEdgeColoring

noncomputable section

/-- Five original endpoint labels cost at most `1/40` at the fixed mixing
parameters once `n` is 5000 times the number of harmonic classes. -/
theorem fiveLabelDiffuse_oneTenth_fourScale_le
    {T n : ℕ} (hn : 5000 * (T + 1) ≤ n) :
    5 * (T + 1 : ℝ) *
        (1 / (((1 / 10 : ℝ) ^ 2) * (4 * n : ℕ))) ≤
      (1 / 40 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hscale : (5000 : ℝ) * (T + 1) ≤ n := by exact_mod_cast hn
  calc
    5 * (T + 1 : ℝ) *
        (1 / (((1 / 10 : ℝ) ^ 2) * (4 * n : ℕ))) =
        125 * (T + 1) / n := by
      push_cast
      field_simp [hnpos.ne']
      ring
    _ ≤ (1 / 40 : ℝ) := by
      rw [div_le_iff₀ hnpos]
      nlinarith

theorem boundedLabelDiffuse_oneTenth_fourScale_le
    {T n : ℕ} {Label : Type*} [Fintype Label]
    (hcard : Fintype.card Label ≤ 5)
    (hn : 5000 * (T + 1) ≤ n) :
    (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
        (1 / (((1 / 10 : ℝ) ^ 2) * (4 * n : ℕ))) ≤
      (1 / 40 : ℝ) := by
  have hcardR : (Fintype.card Label : ℝ) ≤ 5 := by exact_mod_cast hcard
  have hfact : 0 ≤ (T + 1 : ℝ) *
      (1 / (((1 / 10 : ℝ) ^ 2) * (4 * n : ℕ))) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcardR hfact
  have hfive := fiveLabelDiffuse_oneTenth_fourScale_le hn
  nlinarith

/-- This is the paper's fixed missing-palette reserve with the strengthened
five-label diffuse overhead. -/
theorem generalFiniteTiny_labelLocalBudget
    {J M : ℝ} {T n : ℕ} {Label : Type*} [Fintype Label]
    (hn : 5000 * (T + 1) ≤ n)
    (hcard : Fintype.card Label ≤ 5)
    (hJ : 0 ≤ J)
    (hgap : J + (1 / 10 : ℝ) * (4 * n : ℕ) ≤ M)
    (hupper : M ≤ (4 * n : ℕ)) :
    J / M + (1 / 40 : ℝ) +
        (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
          (1 / (((1 / 10 : ℝ) ^ 2) * (4 * n : ℕ))) ≤ 1 := by
  have hnpos : 0 < n := by omega
  exact generalFiniteTiny_localBudget hnpos hJ hgap hupper
    (by norm_num) (boundedLabelDiffuse_oneTenth_fourScale_le hcard hn)

/-- The smaller missing-palette reserve available in the sub-two quotient
still leaves enough room for five endpoint labels.  Here moment mixing uses
`alpha=1/20` at scale `4n`, so its guaranteed missing count is `n/5`.
The fixed threshold is independent of the graph and proposal. -/
theorem fiveLabelDiffuse_oneTwentieth_fourScale_le
    {T n : ℕ} (hn : 50000 * (T + 1) ≤ n) :
    5 * (T + 1 : ℝ) *
        (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤
      (1 / 100 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hscale : (50000 : ℝ) * (T + 1) ≤ n := by exact_mod_cast hn
  calc
    5 * (T + 1 : ℝ) *
        (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) =
        500 * (T + 1) / n := by
      push_cast
      field_simp [hnpos.ne']
      ring
    _ ≤ (1 / 100 : ℝ) := by
      rw [div_le_iff₀ hnpos]
      nlinarith

theorem boundedLabelDiffuse_oneTwentieth_fourScale_le
    {T n : ℕ} {Label : Type*} [Fintype Label]
    (hcard : Fintype.card Label ≤ 5)
    (hn : 50000 * (T + 1) ≤ n) :
    (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
        (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤
      (1 / 100 : ℝ) := by
  have hcardR : (Fintype.card Label : ℝ) ≤ 5 := by exact_mod_cast hcard
  have hfact : 0 ≤ (T + 1 : ℝ) *
      (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcardR hfact
  have hfive := fiveLabelDiffuse_oneTwentieth_fourScale_le hn
  nlinarith

theorem subtwoFiniteTiny_labelLocalBudget
    {J Missing : ℝ} {T n : ℕ} {Label : Type*} [Fintype Label]
    (hn : 50000 * (T + 1) ≤ n)
    (hcard : Fintype.card Label ≤ 5)
    (hJ : 0 ≤ J)
    (hgap : J + (1 / 5 : ℝ) * n ≤ Missing)
    (hupper : Missing ≤ (4 * n : ℕ)) :
    J / Missing + (1 / 100 : ℝ) +
        (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
          (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤ 1 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (4 * n : ℕ) := by positivity
  have hgap' : J + (1 / 20 : ℝ) * (4 * n : ℕ) ≤ Missing := by
    push_cast
    nlinarith [hgap]
  have hratio := div_le_one_sub_of_add_gap_le_general
    hJ (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num : (0 : ℝ) < 1)
    hnR hgap' (by simpa using hupper)
  have hdiffuse := boundedLabelDiffuse_oneTwentieth_fourScale_le hcard hn
  norm_num at hratio
  linarith

/-- The mixing error may tend to zero; the fixed reserve was checked at
the larger value `1/100`. -/
theorem subtwoFiniteTiny_labelLocalBudget_smallEps
    {J Missing epsMix : ℝ} {T n : ℕ}
    {Label : Type*} [Fintype Label]
    (hn : 50000 * (T + 1) ≤ n)
    (hcard : Fintype.card Label ≤ 5)
    (hJ : 0 ≤ J)
    (hgap : J + (1 / 5 : ℝ) * n ≤ Missing)
    (hupper : Missing ≤ (4 * n : ℕ))
    (heps : epsMix ≤ 1 / 100) :
    J / Missing + epsMix +
        (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
          (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤ 1 := by
  have h := subtwoFiniteTiny_labelLocalBudget hn hcard hJ hgap hupper
  linarith

/-- The six-symbol encoding includes one unused sentinel.  A slightly larger
uniform threshold absorbs its possible diffuse atom without changing the
sub-two palette constants. -/
theorem subtwoFiniteTiny_sixLabelDiffuse_le
    {T n : ℕ} {Label : Type*} [Fintype Label]
    (hcard : Fintype.card Label ≤ 6)
    (hn : 60000 * (T + 1) ≤ n) :
    (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
        (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤
      (1 / 100 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hscale : (60000 : ℝ) * (T + 1) ≤ n := by exact_mod_cast hn
  have hcardR : (Fintype.card Label : ℝ) ≤ 6 := by exact_mod_cast hcard
  have hratio :
      (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) = 100 / n := by
    push_cast
    field_simp [hnpos.ne']
    ring
  rw [hratio]
  rw [show (Fintype.card Label : ℝ) * (T + 1 : ℝ) * (100 / n) =
    ((Fintype.card Label : ℝ) * (T + 1 : ℝ) * 100) / n by ring]
  apply (div_le_iff₀ hnpos).2
  have hT : (0 : ℝ) ≤ T + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hcardR hT]

theorem subtwoFiniteTiny_sixLabelLocalBudget_smallEps
    {J Missing epsMix : ℝ} {T n : ℕ}
    {Label : Type*} [Fintype Label]
    (hn : 60000 * (T + 1) ≤ n)
    (hcard : Fintype.card Label ≤ 6)
    (hJ : 0 ≤ J)
    (hgap : J + (1 / 5 : ℝ) * n ≤ Missing)
    (hupper : Missing ≤ (4 * n : ℕ))
    (heps : epsMix ≤ 1 / 100) :
    J / Missing + epsMix +
        (Fintype.card Label : ℝ) * (T + 1 : ℝ) *
          (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤ 1 := by
  have hnR : (0 : ℝ) < (4 * n : ℕ) := by
    have : 0 < n := by omega
    positivity
  have hgap' : J + (1 / 20 : ℝ) * (4 * n : ℕ) ≤ Missing := by
    push_cast
    nlinarith [hgap]
  have hratio := div_le_one_sub_of_add_gap_le_general
    hJ (by norm_num : (0 : ℝ) < 1 / 20) (by norm_num : (0 : ℝ) < 1)
    hnR hgap' (by simpa using hupper)
  have hdiffuse := subtwoFiniteTiny_sixLabelDiffuse_le hcard hn
  norm_num at hratio
  linarith

/-- Summing a diffuse atom over at most `4n` colors costs only the fixed
additive constant `400(T+1)`, independent of the graph order. -/
theorem subtwoFiniteTiny_totalLabelDiffuse_le
    {T K n : ℕ} (hn : 0 < n)
    (hK : (K : ℝ) ≤ (4 * n : ℕ)) :
    (K : ℝ) * (T + 1 : ℝ) *
        (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) ≤
      400 * (T + 1 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg : 0 ≤ (T + 1 : ℝ) := by positivity
  have hratio :
      (1 / (((1 / 20 : ℝ) ^ 2) * (4 * n : ℕ))) = 100 / n := by
    push_cast
    field_simp [hnR.ne']
    ring
  rw [hratio]
  have hK' : (K : ℝ) ≤ 4 * n := by simpa using hK
  have hKN : (K : ℝ) * (100 / n) ≤ 400 := by
    rw [show (K : ℝ) * (100 / n) = K * 100 / n by ring]
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hK' (by norm_num : (0 : ℝ) ≤ 100)]
  nlinarith [mul_le_mul_of_nonneg_right hKN hnonneg]

end
end WeightedEdgeColoring
