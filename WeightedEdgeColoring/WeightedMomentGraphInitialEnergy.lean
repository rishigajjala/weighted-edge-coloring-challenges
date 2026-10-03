import WeightedEdgeColoring.WeightedMomentGraphScheduleCoordinates

/-!
# Coarse initial energy bounds for graph moments

Nonnegative coordinates with fixed total have squared energy at most the
square of that total.  Centering only subtracts the uniform projection, so
the same bound applies to the centered one-color and off-diagonal arrays.
-/

namespace WeightedEdgeColoring

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics
open WeightedEdgeColoring.WeightedMomentPairArray

noncomputable section

theorem sum_sq_sub_average_le_sq_sum
    {I : Type*} [Fintype I] [Nonempty I]
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, (x i - (∑ j, x j) / Fintype.card I) ^ 2) ≤
      (∑ i, x i) ^ 2 := by
  let W : ℝ := ∑ i, x i
  let K : ℝ := Fintype.card I
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  have hsquares : (∑ i, (x i) ^ 2) ≤ W ^ 2 := by
    dsimp [W]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _hi ↦ hx i)
  have hidentity :
      (∑ i, (x i - W / K) ^ 2) =
        (∑ i, (x i) ^ 2) - W ^ 2 / K := by
    calc
      (∑ i, (x i - W / K) ^ 2) =
          ∑ i, ((x i) ^ 2 - (2 * (W / K)) * x i + (W / K) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i, (x i) ^ 2) - (2 * (W / K)) * W +
          K * (W / K) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      _ = (∑ i, (x i) ^ 2) - W ^ 2 / K := by
        field_simp [hK.ne']
        ring
  rw [show (∑ j, x j) / Fintype.card I = W / K by rfl, hidentity]
  exact (sub_le_self _ (div_nonneg (sq_nonneg W) hK.le)).trans hsquares

theorem firstMoment_nonneg_of_weight
    {Item Color : Type*} [Fintype Item] [Fintype Color] [DecidableEq Color]
    (palette : Item → Finset Color) (weight : Item → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (c : Color) :
    0 ≤ firstMoment palette weight c := by
  unfold firstMoment paletteSize
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg (div_nonneg (hweight i) (by positivity)) (by
    split <;> norm_num)

theorem diagonalMoment_nonneg_of_weight
    {Item Color : Type*} [Fintype Item] [Fintype Color] [DecidableEq Color]
    (palette : Item → Finset Color) (weight : Item → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (c : Color) :
    0 ≤ diagonalMoment palette weight c := by
  unfold diagonalMoment paletteSize
  apply Finset.sum_nonneg
  intro i _hi
  exact mul_nonneg (div_nonneg (hweight i) (by positivity)) (by
    split <;> norm_num)

theorem pairMoment_nonneg_of_weight
    {Item Color : Type*} [Fintype Item] [Fintype Color] [DecidableEq Color]
    (palette : Item → Finset Color) (weight : Item → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (c d : Color) :
    0 ≤ pairMoment palette weight c d := by
  unfold pairMoment paletteSize
  split
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro i _hi
    exact mul_nonneg
      (mul_nonneg
        (div_nonneg (hweight i) (sq_nonneg _)) (by split <;> norm_num))
      (by split <;> norm_num)

theorem energy_le_total_sq_of_nonneg
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (h : Color → Color → ℝ) (hnonneg : ∀ c d, 0 ≤ h c d) :
    energy h ≤ (total h) ^ 2 := by
  let x : Color × Color → ℝ := fun cd ↦
    if cd.1 = cd.2 then 0 else h cd.1 cd.2
  have hx : ∀ cd, 0 ≤ x cd := by
    intro cd
    dsimp [x]
    split
    · exact le_rfl
    · exact hnonneg _ _
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Color × Color)))
    (f := x) (fun cd _hcd ↦ hx cd)
  simpa [x, energy, total, rowSum, Fintype.sum_prod_type] using hs

theorem energy_sub_offDiagonalConstant_eq
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (h : Color → Color → ℝ) (mu : ℝ) :
    energy (fun c d ↦ h c d - offDiagonalConstant mu c d) =
      energy h - 2 * mu * total h +
        ((Fintype.card Color : ℝ) *
          ((Fintype.card Color : ℝ) - 1)) * mu ^ 2 := by
  have hcount :
      (∑ c : Color, ∑ d : Color, if c = d then 0 else (1 : ℝ)) =
        (Fintype.card Color : ℝ) *
          ((Fintype.card Color : ℝ) - 1) := by
    calc
      (∑ c : Color, ∑ d : Color, if c = d then 0 else (1 : ℝ)) =
          ∑ c : Color, ∑ d : Color,
            if c = d then 0 else (1 : ℝ) * 1 := by
        apply Finset.sum_congr rfl
        intro c _hc
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hcd : c = d <;> simp [hcd]
      _ = (∑ _c : Color, (1 : ℝ)) ^ 2 -
          ∑ _c : Color, (1 : ℝ) ^ 2 :=
        sum_offDiagonal_mul (fun _c : Color ↦ (1 : ℝ))
      _ = (Fintype.card Color : ℝ) *
          ((Fintype.card Color : ℝ) - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          one_pow, mul_one]
        ring
  have hcross :
      (∑ c : Color, ∑ d : Color,
        2 * mu * (if c = d then 0 else h c d)) =
        2 * mu *
          (∑ c : Color, ∑ d : Color,
            if c = d then 0 else h c d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _hc
    rw [Finset.mul_sum]
  have hconstant :
      (∑ c : Color, ∑ d : Color,
        (if c = d then 0 else (1 : ℝ)) * mu ^ 2) =
        (∑ c : Color, ∑ d : Color,
          if c = d then 0 else (1 : ℝ)) * mu ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _hc
    rw [Finset.sum_mul]
  unfold energy total rowSum offDiagonalConstant
  rw [show
      (∑ c : Color, ∑ d : Color,
        if c = d then 0 else
          (h c d - (if c = d then 0 else mu)) ^ 2) =
      (∑ c : Color, ∑ d : Color,
        if c = d then 0 else (h c d) ^ 2) -
      2 * mu *
        (∑ c : Color, ∑ d : Color,
          if c = d then 0 else h c d) +
      (∑ c : Color, ∑ d : Color,
        if c = d then 0 else (1 : ℝ)) * mu ^ 2 by
    calc
      _ = ∑ c : Color, ∑ d : Color,
          ((if c = d then 0 else (h c d) ^ 2) -
            2 * mu * (if c = d then 0 else h c d) +
            (if c = d then 0 else (1 : ℝ)) * mu ^ 2) := by
        apply Finset.sum_congr rfl
        intro c _hc
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hcd : c = d
        · simp [hcd]
        · simp [hcd]
          ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hcross, hconstant]]
  rw [hcount]

theorem energy_centered_offDiagonal_le_total_sq
    {Color : Type*} [Fintype Color] [DecidableEq Color]
    (h : Color → Color → ℝ) (hnonneg : ∀ c d, 0 ≤ h c d)
    (hcard : 2 ≤ Fintype.card Color) :
    energy (fun c d ↦ h c d -
      offDiagonalConstant
        (total h /
          ((Fintype.card Color : ℝ) *
            ((Fintype.card Color : ℝ) - 1))) c d) ≤
      (total h) ^ 2 := by
  let M : ℝ := (Fintype.card Color : ℝ) *
    ((Fintype.card Color : ℝ) - 1)
  have hcardReal : (2 : ℝ) ≤ (Fintype.card Color : ℝ) := by
    exact_mod_cast hcard
  have hM : 0 < M := by
    dsimp [M]
    exact mul_pos (by linarith) (by linarith)
  rw [energy_sub_offDiagonalConstant_eq]
  have henergy := energy_le_total_sq_of_nonneg h hnonneg
  have hsubtract :
      energy h - 2 * (total h / M) * total h +
          M * (total h / M) ^ 2 =
        energy h - (total h) ^ 2 / M := by
    field_simp [hM.ne']
    ring
  rw [hsubtract]
  exact (sub_le_self _ (div_nonneg (sq_nonneg _) hM.le)).trans henergy

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

theorem graphMomentItemWeight_nonneg
    (R : Finset G.E) (charge : G.E → ℝ)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (v : G.V) (e : R) :
    0 ≤ G.graphMomentItemWeight R charge v e := by
  unfold graphMomentItemWeight
  split
  · exact hcharge e.1 e.2
  · exact le_rfl

theorem graphFirstMoment_nonneg {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (v : G.V) (c : Fin q) :
    0 ≤ G.graphFirstMoment R charge F color v c := by
  exact firstMoment_nonneg_of_weight _ _
    (G.graphMomentItemWeight_nonneg R charge hcharge v) c

theorem graphDiagonalMoment_nonneg {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (v : G.V) (c : Fin q) :
    0 ≤ G.graphDiagonalMoment R charge F color v c := by
  exact diagonalMoment_nonneg_of_weight _ _
    (G.graphMomentItemWeight_nonneg R charge hcharge v) c

theorem graphPairMoment_nonneg {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (v : G.V) (c d : Fin q) :
    0 ≤ G.graphPairMoment R charge F color v c d := by
  exact pairMoment_nonneg_of_weight _ _
    (G.graphMomentItemWeight_nonneg R charge hcharge v) c d

theorem sum_sq_graphFirstCentered_le {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (hq : 0 < q) (v : G.V) :
    (∑ c, (G.graphFirstCentered R charge F color v c) ^ 2) ≤
      (G.restrictedCharge R charge v) ^ 2 := by
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have h := sum_sq_sub_average_le_sq_sum
    (fun c ↦ G.graphFirstMoment R charge F color v c)
    (G.graphFirstMoment_nonneg R charge F color hcharge v)
  rw [G.sum_graphFirstMoment R charge F color hmissing] at h
  simpa [graphFirstCentered] using h

theorem sum_sq_graphDiagonalCentered_le {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (hq : 0 < q) (v : G.V) :
    (∑ c, (G.graphDiagonalCentered R charge F color v c) ^ 2) ≤
      (G.graphHarmonicMoment R charge F color v) ^ 2 := by
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have h := sum_sq_sub_average_le_sq_sum
    (fun c ↦ G.graphDiagonalMoment R charge F color v c)
    (G.graphDiagonalMoment_nonneg R charge F color hcharge v)
  rw [G.sum_graphDiagonalMoment R charge F color hmissing] at h
  simpa [graphDiagonalCentered] using h

theorem energy_graphPairCentered_le {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (hq : 2 ≤ q) (v : G.V) :
    energy (G.graphPairCentered R charge F color v) ≤
      (G.restrictedCharge R charge v -
        G.graphHarmonicMoment R charge F color v) ^ 2 := by
  have hqCard : 2 ≤ Fintype.card (Fin q) := by simpa using hq
  have h := energy_centered_offDiagonal_le_total_sq
    (G.graphPairMoment R charge F color v)
    (G.graphPairMoment_nonneg R charge F color hcharge v) hqCard
  have htotal :
      total (G.graphPairMoment R charge F color v) =
        G.restrictedCharge R charge v -
          G.graphHarmonicMoment R charge F color v := by
    unfold total rowSum
    calc
      (∑ c : Fin q, ∑ d : Fin q,
        if c = d then 0 else G.graphPairMoment R charge F color v c d) =
          ∑ c : Fin q, ∑ d : Fin q,
            G.graphPairMoment R charge F color v c d := by
        apply Finset.sum_congr rfl
        intro c _hc
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hcd : c = d
        · subst d
          simp [graphPairMoment, pairMoment]
        · simp [hcd]
      _ = _ := G.sum_graphPairMoment R charge F color hmissing v
  rw [htotal] at h
  simpa only [graphPairCentered, Fintype.card_fin] using h

/-- Coarse graph-only form of the universal-schedule coordinate estimate.
The initial first and pair energies cost `n²`, while the diagonal energy
costs only `alpha⁻²`. -/
theorem exists_realizing_universalSchedule_coordinates_coarse
    {q n s : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color)
    (heven : Even q) (hq4 : 4 ≤ q)
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 < L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L) :
    ∃ mixed : G.E → Fin q,
      G.IsProperOn F mixed ∧
      (∀ v c,
        |G.graphFirstMoment R charge F mixed v c -
          G.restrictedCharge R charge v / q| ≤
        s * G.momentBlockError alpha L n q +
          Real.sqrt
            ((n : ℝ) ^ 2 *
              ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2)))) ∧
      (∀ v c,
        |G.graphDiagonalMoment R charge F mixed v c -
          G.graphHarmonicMoment R charge F color v / q| ≤
        s * (G.momentBlockError alpha L n q / n) +
          Real.sqrt
            ((1 / alpha) ^ 2 *
              ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2)))) ∧
      ∀ v c d,
        |G.graphPairMoment R charge F mixed v c d -
          offDiagonalConstant
            ((G.restrictedCharge R charge v -
                G.graphHarmonicMoment R charge F color v) /
              ((q : ℝ) * ((q : ℝ) - 1))) c d| ≤
        2 * s * (G.momentBlockError alpha L n q / n) +
          Real.sqrt
            (((n : ℝ) ^ 2 / 4) *
              ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2))) := by
  have hmissingPos : ∀ w, 0 < (G.missingColorsAt F color w).card := by
    intro w
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hcardReal : (0 : ℝ) < (G.missingColorsAt F color w).card :=
      lt_of_lt_of_le (mul_pos halpha hnreal) (hmissing w)
    exact_mod_cast hcardReal
  rcases G.exists_realizing_universalSchedule_coordinates (s := s)
      R charge F color
      hproper heven hq4 alpha L halpha hL hn hcharge hmissing hrestricted hpair with
    ⟨mixed, hproperMixed, hfirst, hdiag, hpairCoord⟩
  refine ⟨mixed, hproperMixed, ?_, ?_, ?_⟩
  · intro v c
    have hW0 : 0 ≤ G.restrictedCharge R charge v := by
      unfold restrictedCharge
      apply Finset.sum_nonneg
      intro e he
      split
      · exact hcharge e he
      · exact le_rfl
    have henergy := G.sum_sq_graphFirstCentered_le R charge F color
      hcharge hmissingPos (by omega) v
    have hWsq : (G.restrictedCharge R charge v) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith [hrestricted v]
    have hloss0 : 0 ≤ (1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2) := by positivity
    exact (hfirst v c).trans (by
      simpa [add_comm] using add_le_add_left
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (henergy.trans hWsq) hloss0))
        (s * G.momentBlockError alpha L n q))
  · intro v c
    have hD0 := G.graphHarmonicMoment_nonneg R charge F color hcharge v
    have hD := G.graphHarmonicMoment_le_inv_alpha R charge F color alpha v
      halpha hn hcharge hmissing (hrestricted v)
    have henergy := G.sum_sq_graphDiagonalCentered_le R charge F color
      hcharge hmissingPos (by omega) v
    have hDsq : (G.graphHarmonicMoment R charge F color v) ^ 2 ≤
        (1 / alpha) ^ 2 := by
      nlinarith [hD, one_div_pos.mpr halpha]
    have hloss0 : 0 ≤ (1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2) := by positivity
    exact (hdiag v c).trans (by
      simpa [add_comm] using add_le_add_left
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (henergy.trans hDsq) hloss0))
        (s * (G.momentBlockError alpha L n q / n)))
  · intro v c d
    have hW0 : 0 ≤ G.restrictedCharge R charge v := by
      unfold restrictedCharge
      apply Finset.sum_nonneg
      intro e he
      split
      · exact hcharge e he
      · exact le_rfl
    have hD0 := G.graphHarmonicMoment_nonneg R charge F color hcharge v
    have hDW := G.graphHarmonicMoment_le_restrictedCharge R charge F color
      hcharge hmissingPos v
    have henergy := G.energy_graphPairCentered_le R charge F color
      hcharge hmissingPos (by omega) v
    have hTsq :
        (G.restrictedCharge R charge v -
          G.graphHarmonicMoment R charge F color v) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      nlinarith [hrestricted v]
    have hloss0 : 0 ≤ (1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2) := by positivity
    have hquarter :
        energy (G.graphPairCentered R charge F color v) / 4 ≤
          (n : ℝ) ^ 2 / 4 := by linarith [henergy.trans hTsq]
    exact (hpairCoord v c d).trans (by
      simpa [add_comm] using add_le_add_left
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hquarter hloss0))
        (2 * s * (G.momentBlockError alpha L n q / n)))

end WeightedMultigraph
end
end WeightedEdgeColoring
