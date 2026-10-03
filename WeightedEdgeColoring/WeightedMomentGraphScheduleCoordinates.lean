import WeightedEdgeColoring.KempeGraphMomentPairingSchedule
import WeightedEdgeColoring.WeightedMomentGraphErrorFromCoordinates

/-!
# Centered graph moments along a universal pairing schedule

This file separates the exact operator contraction from the concrete Kempe
selection error.  The estimates retain the initial centered energies; crude
graph bounds or sharper application-specific bounds can be inserted later.
-/

namespace WeightedEdgeColoring

open scoped BigOperators
open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators
open WeightedEdgeColoring.FiniteColorPairingUniversalSchedule
open WeightedEdgeColoring.FiniteColorPairingScheduleRobust
open WeightedEdgeColoring.WeightedMomentPairArray

noncomputable section

theorem singleAverage_sub_const {Color : Type*}
    [Fintype Color] [DecidableEq Color]
    (p : Pairing Color) (x : Color → ℝ) (mu : ℝ) :
    singleAverage p (fun c ↦ x c - mu) =
      fun c ↦ singleAverage p x c - mu := by
  funext c
  unfold singleAverage
  ring

theorem applySingleSchedule_sub_const {Color : Type*}
    [Fintype Color] [DecidableEq Color]
    (schedule : List (Pairing Color)) (x : Color → ℝ) (mu : ℝ) :
    applySingleSchedule schedule (fun c ↦ x c - mu) =
      fun c ↦ applySingleSchedule schedule x c - mu := by
  induction schedule generalizing x with
  | nil => rfl
  | cons p schedule ih =>
      change
        applySingleSchedule schedule
            (singleAverage p (fun c ↦ x c - mu)) =
          fun c ↦ applySingleSchedule schedule (singleAverage p x) c - mu
      rw [singleAverage_sub_const]
      exact ih (singleAverage p x)

def offDiagonalConstant {Color : Type*} [DecidableEq Color]
    (mu : ℝ) (c d : Color) : ℝ := if c = d then 0 else mu

theorem pairAverage_offDiagonalConstant {Color : Type*}
    [Fintype Color] [DecidableEq Color]
    (p : Pairing Color) (mu : ℝ) :
    pairAverage p (offDiagonalConstant mu) = offDiagonalConstant mu := by
  funext c d
  by_cases hcd : c = d
  · subst d
    simp [pairAverage, offDiagonalConstant]
  by_cases hpcd : partner Color p c = d
  · simp [pairAverage, offDiagonalConstant, hcd, hpcd]
  have hc_pd : c ≠ partner Color p d := by
    intro h
    have := congrArg (partner Color p) h
    exact hpcd (by simpa only [partner_partner] using this)
  have hpc_pd : partner Color p c ≠ partner Color p d := by
    exact fun h ↦ hcd (partner_injective Color p h)
  simp [pairAverage, offDiagonalConstant, hcd, hpcd, hc_pd, hpc_pd]
  ring

theorem pairAverage_sub {Color : Type*}
    [Fintype Color] [DecidableEq Color]
    (p : Pairing Color) (x y : Color → Color → ℝ) :
    pairAverage p (fun c d ↦ x c d - y c d) =
      fun c d ↦ pairAverage p x c d - pairAverage p y c d := by
  funext c d
  unfold pairAverage
  by_cases hcd : c = d
  · simp [hcd]
  · by_cases hpcd : partner Color p c = d
    · simp [hcd, hpcd]
    · simp [hcd, hpcd]
      ring

theorem applyPairSchedule_sub_offDiagonalConstant {Color : Type*}
    [Fintype Color] [DecidableEq Color]
    (schedule : List (Pairing Color))
    (x : Color → Color → ℝ) (mu : ℝ) :
    applyPairSchedule schedule
        (fun c d ↦ x c d - offDiagonalConstant mu c d) =
      fun c d ↦ applyPairSchedule schedule x c d -
        offDiagonalConstant mu c d := by
  induction schedule generalizing x with
  | nil => rfl
  | cons p schedule ih =>
      change
        applyPairSchedule schedule
            (pairAverage p
              (fun c d ↦ x c d - offDiagonalConstant mu c d)) =
          fun c d ↦ applyPairSchedule schedule (pairAverage p x) c d -
            offDiagonalConstant mu c d
      rw [pairAverage_sub, pairAverage_offDiagonalConstant]
      exact ih (pairAverage p x)

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

def graphFirstCentered {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) : Fin q → ℝ :=
  fun c ↦ G.graphFirstMoment R charge F color v c -
    G.restrictedCharge R charge v / q

def graphDiagonalCentered {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) : Fin q → ℝ :=
  fun c ↦ G.graphDiagonalMoment R charge F color v c -
    G.graphHarmonicMoment R charge F color v / q

def graphPairCentered {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) :
    Fin q → Fin q → ℝ :=
  fun c d ↦ G.graphPairMoment R charge F color v c d -
    offDiagonalConstant
      ((G.restrictedCharge R charge v -
          G.graphHarmonicMoment R charge F color v) /
        ((q : ℝ) * ((q : ℝ) - 1))) c d

theorem sum_graphFirstCentered {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (hq : 0 < q) (v : G.V) :
    ∑ c, G.graphFirstCentered R charge F color v c = 0 := by
  unfold graphFirstCentered
  rw [Finset.sum_sub_distrib, G.sum_graphFirstMoment R charge F color hmissing]
  simp
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hq0]
  ring

theorem sum_graphDiagonalCentered {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (hq : 0 < q) (v : G.V) :
    ∑ c, G.graphDiagonalCentered R charge F color v c = 0 := by
  unfold graphDiagonalCentered
  rw [Finset.sum_sub_distrib,
    G.sum_graphDiagonalMoment R charge F color hmissing]
  simp
  have hq0 : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hq)
  field_simp [hq0]
  ring

theorem graphPairCentered_symmetric {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) (c d : Fin q) :
    G.graphPairCentered R charge F color v c d =
      G.graphPairCentered R charge F color v d c := by
  unfold graphPairCentered offDiagonalConstant
  rw [G.graphPairMoment_symmetric R charge F color v c d]
  by_cases hcd : c = d
  · simp [hcd]
  · simp [hcd, Ne.symm hcd]

theorem graphPairCentered_diagonal {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) (c : Fin q) :
    G.graphPairCentered R charge F color v c c = 0 := by
  simp [graphPairCentered, graphPairMoment,
    WeightedMomentStatistics.pairMoment, offDiagonalConstant]

theorem total_graphPairCentered {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (hq : 2 ≤ q) (v : G.V) :
    total (G.graphPairCentered R charge F color v) = 0 := by
  let T := G.restrictedCharge R charge v -
    G.graphHarmonicMoment R charge F color v
  have hqReal : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by nlinarith
  have hq1 : (q : ℝ) - 1 ≠ 0 := by nlinarith
  unfold total rowSum graphPairCentered
  rw [show
      (∑ c : Fin q, ∑ d : Fin q,
        if c = d then 0 else
          (G.graphPairMoment R charge F color v c d -
            offDiagonalConstant (T / ((q : ℝ) * ((q : ℝ) - 1))) c d)) =
      (∑ c : Fin q, ∑ d : Fin q,
        G.graphPairMoment R charge F color v c d) -
      (∑ c : Fin q, ∑ d : Fin q,
        offDiagonalConstant (T / ((q : ℝ) * ((q : ℝ) - 1))) c d) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    by_cases hcd : c = d <;>
      simp [hcd, graphPairMoment, WeightedMomentStatistics.pairMoment,
        offDiagonalConstant]]
  rw [G.sum_graphPairMoment R charge F color hmissing]
  have hoff :
      (∑ c : Fin q, ∑ d : Fin q,
        offDiagonalConstant (T / ((q : ℝ) * ((q : ℝ) - 1))) c d) = T := by
    calc
      (∑ c : Fin q, ∑ d : Fin q,
        offDiagonalConstant (T / ((q : ℝ) * ((q : ℝ) - 1))) c d) =
          (∑ c : Fin q, ∑ d : Fin q,
            if c = d then 0 else (1 : ℝ)) *
              (T / ((q : ℝ) * ((q : ℝ) - 1))) := by
        unfold offDiagonalConstant
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _hc
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hcd : c = d <;> simp [hcd]
      _ = ((∑ _c : Fin q, (1 : ℝ)) ^ 2 -
            ∑ _c : Fin q, (1 : ℝ) ^ 2) *
              (T / ((q : ℝ) * ((q : ℝ) - 1))) := by
        have hcount :
            (∑ c : Fin q, ∑ d : Fin q,
              if c = d then 0 else (1 : ℝ)) =
              (∑ _c : Fin q, (1 : ℝ)) ^ 2 -
                ∑ _c : Fin q, (1 : ℝ) ^ 2 := by
          calc
            _ = ∑ c : Fin q, ∑ d : Fin q,
                if c = d then 0 else (1 : ℝ) * 1 := by
              apply Finset.sum_congr rfl
              intro c _hc
              apply Finset.sum_congr rfl
              intro d _hd
              by_cases hcd : c = d <;> simp [hcd]
            _ = _ := WeightedMomentStatistics.sum_offDiagonal_mul
              (fun _c : Fin q ↦ (1 : ℝ))
        rw [hcount]
      _ = (q : ℝ) * ((q : ℝ) - 1) *
          (T / ((q : ℝ) * ((q : ℝ) - 1))) := by
        have hcoefficient :
            ((∑ _c : Fin q, (1 : ℝ)) ^ 2 -
                ∑ _c : Fin q, (1 : ℝ) ^ 2) =
              (q : ℝ) * ((q : ℝ) - 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, one_pow, mul_one]
          ring
        rw [hcoefficient]
      _ = T := by
        have hden : (q : ℝ) * ((q : ℝ) - 1) ≠ 0 := mul_ne_zero hq0 hq1
        calc
          _ = (T / ((q : ℝ) * ((q : ℝ) - 1))) *
                ((q : ℝ) * ((q : ℝ) - 1)) := by ring
          _ = T := div_mul_cancel₀ T hden
  simpa [T] using congrArg
    (fun x : ℝ ↦
      (G.restrictedCharge R charge v -
        G.graphHarmonicMoment R charge F color v) - x) hoff

/-- The ideal universal schedule and the concrete Kempe realization combine
into uniform centered-coordinate bounds at every graph vertex. -/
theorem exists_realizing_universalSchedule_coordinates
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
            ((∑ i, (G.graphFirstCentered R charge F color v i) ^ 2) *
              ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2)))) ∧
      (∀ v c,
        |G.graphDiagonalMoment R charge F mixed v c -
          G.graphHarmonicMoment R charge F color v / q| ≤
        s * (G.momentBlockError alpha L n q / n) +
          Real.sqrt
            ((∑ i, (G.graphDiagonalCentered R charge F color v i) ^ 2) *
              ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2)))) ∧
      ∀ v c d,
        |G.graphPairMoment R charge F mixed v c d -
          offDiagonalConstant
            ((G.restrictedCharge R charge v -
                G.graphHarmonicMoment R charge F color v) /
              ((q : ℝ) * ((q : ℝ) - 1))) c d| ≤
        2 * s * (G.momentBlockError alpha L n q / n) +
          Real.sqrt
            ((energy (G.graphPairCentered R charge F color v) / 4) *
              ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2))) := by
  have hmissingPos : ∀ w, 0 < (G.missingColorsAt F color w).card := by
    intro w
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hcardReal : (0 : ℝ) < (G.missingColorsAt F color w).card :=
      lt_of_lt_of_le (mul_pos halpha hnreal) (hmissing w)
    exact_mod_cast hcardReal
  have hevenCard : Even (Fintype.card (Fin q)) := by
    simpa only [Fintype.card_fin] using heven
  have hq4Card : 4 ≤ Fintype.card (Fin q) := by
    simpa only [Fintype.card_fin] using hq4
  rcases exists_universalOperatorSchedule_two_sq (Color := Fin q)
      hevenCard hq4Card s with
    ⟨schedule, hlength, hsingle, hpairOperator⟩
  rcases G.exists_realizing_pairingSchedule R charge F color hproper schedule
      alpha L halpha hL hn hcharge hmissing hrestricted hpair with
    ⟨mixed, hproperMixed, hfirstOrbit, hdiagOrbit, hpairOrbit⟩
  have hE0 : 0 ≤ G.momentBlockError alpha L n q :=
    G.momentBlockError_nonneg halpha hL hn
  refine ⟨mixed, hproperMixed, ?_, ?_, ?_⟩
  · intro v c
    have horbit := (hfirstOrbit v).error_le_length_mul c
    have hidealSq :
        (applySingleSchedule schedule
          (G.graphFirstCentered R charge F color v) c) ^ 2 ≤
          (∑ a, (G.graphFirstCentered R charge F color v a) ^ 2) *
            ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2)) := by
      simpa only [Fintype.card_fin] using
        hsingle (G.graphFirstCentered R charge F color v)
          (G.sum_graphFirstCentered R charge F color hmissingPos (by omega) v) c
    have hideal := Real.abs_le_sqrt hidealSq
    change
      |applySingleSchedule schedule
          (fun d ↦ G.graphFirstMoment R charge F color v d -
            G.restrictedCharge R charge v / q) c| ≤ _ at hideal
    rw [applySingleSchedule_sub_const] at hideal
    calc
      |_ - _| ≤
          |G.graphFirstMoment R charge F mixed v c -
            applySingleSchedule schedule
              (G.graphFirstMoment R charge F color v) c| +
          |applySingleSchedule schedule
              (G.graphFirstMoment R charge F color v) c -
            G.restrictedCharge R charge v / q| := by
        exact abs_sub_le _ _ _
      _ ≤ schedule.length * G.momentBlockError alpha L n q +
          Real.sqrt _ := add_le_add horbit hideal
      _ = _ := by rw [hlength]
  · intro v c
    have horbit := (hdiagOrbit v).error_le_length_mul c
    have hidealSq :
        (applySingleSchedule schedule
          (G.graphDiagonalCentered R charge F color v) c) ^ 2 ≤
          (∑ a, (G.graphDiagonalCentered R charge F color v a) ^ 2) *
            ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2)) := by
      simpa only [Fintype.card_fin] using
        hsingle (G.graphDiagonalCentered R charge F color v)
          (G.sum_graphDiagonalCentered R charge F color hmissingPos
            (by omega) v) c
    have hideal := Real.abs_le_sqrt hidealSq
    change
      |applySingleSchedule schedule
          (fun d ↦ G.graphDiagonalMoment R charge F color v d -
            G.graphHarmonicMoment R charge F color v / q) c| ≤ _ at hideal
    rw [applySingleSchedule_sub_const] at hideal
    calc
      |_ - _| ≤
          |G.graphDiagonalMoment R charge F mixed v c -
            applySingleSchedule schedule
              (G.graphDiagonalMoment R charge F color v) c| +
          |applySingleSchedule schedule
              (G.graphDiagonalMoment R charge F color v) c -
            G.graphHarmonicMoment R charge F color v / q| := by
        exact abs_sub_le _ _ _
      _ ≤ schedule.length * (G.momentBlockError alpha L n q / n) +
          Real.sqrt _ := add_le_add horbit hideal
      _ = _ := by rw [hlength]
  · intro v c d
    have horbit := (hpairOrbit v).error_le_two_mul_length_mul
      (div_nonneg hE0 (by positivity)) c d
    have hidealSq :
        (applyPairSchedule schedule
          (G.graphPairCentered R charge F color v) c d) ^ 2 ≤
          (energy (G.graphPairCentered R charge F color v) / 4) *
            ((1 / 2 : ℝ) ^ s * (2 * (q : ℝ) ^ 2)) := by
      simpa only [Fintype.card_fin] using
        hpairOperator (G.graphPairCentered R charge F color v)
          (G.graphPairCentered_symmetric R charge F color v)
          (G.graphPairCentered_diagonal R charge F color v)
          (G.total_graphPairCentered R charge F color hmissingPos
            (by omega) v) c d
    have hideal := Real.abs_le_sqrt hidealSq
    change
      |applyPairSchedule schedule
          (fun i j ↦ G.graphPairMoment R charge F color v i j -
            offDiagonalConstant
              ((G.restrictedCharge R charge v -
                  G.graphHarmonicMoment R charge F color v) /
                ((q : ℝ) * ((q : ℝ) - 1))) i j) c d| ≤ _ at hideal
    rw [applyPairSchedule_sub_offDiagonalConstant] at hideal
    calc
      |_ - _| ≤
          |G.graphPairMoment R charge F mixed v c d -
            applyPairSchedule schedule
              (G.graphPairMoment R charge F color v) c d| +
          |applyPairSchedule schedule
              (G.graphPairMoment R charge F color v) c d -
            offDiagonalConstant
              ((G.restrictedCharge R charge v -
                  G.graphHarmonicMoment R charge F color v) /
                ((q : ℝ) * ((q : ℝ) - 1))) c d| := by
        exact abs_sub_le _ _ _
      _ ≤ 2 * schedule.length * (G.momentBlockError alpha L n q / n) +
          Real.sqrt _ := add_le_add horbit hideal
      _ = _ := by rw [hlength]

end WeightedMultigraph
end
end WeightedEdgeColoring
