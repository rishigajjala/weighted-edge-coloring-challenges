import WeightedEdgeColoring.WeightedMomentGraphStatistics
import WeightedEdgeColoring.WeightedMomentErrorBound

/-!
# Expanding the graph overlap error into `z`, `d`, and `Z`

This file proves the exact algebraic bridge between the normalized common
palette size on a residual edge and the three graph moments.  For a fixed
vertex `v`, write `A_c` for its missing-color indicator and `B_{e,c}` for
the indicator at the opposite endpoint of `e`.  Then

`lambda_e = (q / f_v) * sum_c A_c B_{e,c} / f_e`.

Squaring and separating equal from distinct color indices produces the
diagonal moment `d` and ordered pair moment `Z`.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- At an incident vertex, common-palette membership is membership at that
vertex and at the opposite endpoint. -/
theorem mem_momentCommonMissingColors_iff_of_inc {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    {v : G.V} {e : G.E} (hinc : G.Inc v e) (c : Fin q) :
    c ∈ G.momentCommonMissingColors F color e ↔
      c ∈ G.missingColorsAt F color v ∧
        c ∈ G.missingColorsAt F color (G.kempeOtherEndpoint v e) := by
  rcases hinc with hfst | hsnd
  · simp [momentCommonMissingColors, kempeOtherEndpoint, hfst]
  · have hne : G.fst e ≠ v := by
      intro hfst
      exact G.noLoop e (hfst.trans hsnd.symm)
    simp [momentCommonMissingColors, kempeOtherEndpoint, hne, hsnd,
      and_comm]

/-- The common-palette cardinality is the dot product of the two indicator
vectors. -/
theorem card_momentCommonMissingColors_eq_indicator_sum_of_inc {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    {v : G.V} {e : G.E} (hinc : G.Inc v e) :
    ((G.momentCommonMissingColors F color e).card : ℝ) =
      ∑ c : Fin q,
        paletteIndicator (G.missingColorsAt F color v) c *
          paletteIndicator
            (G.missingColorsAt F color (G.kempeOtherEndpoint v e)) c := by
  classical
  calc
    ((G.momentCommonMissingColors F color e).card : ℝ) =
        ∑ c : Fin q,
          if c ∈ G.momentCommonMissingColors F color e then 1 else 0 := by
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _hc
      unfold paletteIndicator
      by_cases hv : c ∈ G.missingColorsAt F color v <;>
        by_cases hw : c ∈ G.missingColorsAt F color
          (G.kempeOtherEndpoint v e) <;>
        simp [G.mem_momentCommonMissingColors_iff_of_inc F color hinc c,
          hv, hw]

/-- Indicator-sum formula for one normalized common-palette size. -/
theorem momentLambda_eq_indicator_sum_of_inc {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < G.momentMissingSize F color w)
    {v : G.V} {e : G.E} (hinc : G.Inc v e) :
    G.momentLambda F color e =
      (q : ℝ) / G.momentMissingSize F color v *
        ∑ c : Fin q,
          paletteIndicator (G.missingColorsAt F color v) c *
            (paletteIndicator
                (G.missingColorsAt F color
                  (G.kempeOtherEndpoint v e)) c /
              G.momentMissingSize F color
                (G.kempeOtherEndpoint v e)) := by
  have hprod := G.momentMissingSize_mul_otherEndpoint F color hinc
  have hcard :=
    G.card_momentCommonMissingColors_eq_indicator_sum_of_inc
      F color hinc
  unfold momentLambda
  rw [hcard, ← hprod]
  have hv : G.momentMissingSize F color v ≠ 0 :=
    ne_of_gt (hmissing v)
  have hw : G.momentMissingSize F color
      (G.kempeOtherEndpoint v e) ≠ 0 :=
    ne_of_gt (hmissing (G.kempeOtherEndpoint v e))
  have hsum :
      (∑ c : Fin q,
        paletteIndicator (G.missingColorsAt F color v) c *
          (paletteIndicator
              (G.missingColorsAt F color
                (G.kempeOtherEndpoint v e)) c /
            G.momentMissingSize F color
              (G.kempeOtherEndpoint v e))) =
        (∑ c : Fin q,
          paletteIndicator (G.missingColorsAt F color v) c *
            paletteIndicator
              (G.missingColorsAt F color
                (G.kempeOtherEndpoint v e)) c) /
          G.momentMissingSize F color
            (G.kempeOtherEndpoint v e) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _hc
    ring
  rw [hsum]
  field_simp [hv, hw]

/-- The first term in the error expansion. -/
def graphOverlapFirst {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) : ℝ :=
  (q : ℝ) / G.momentMissingSize F color v *
    ∑ c : Fin q,
      paletteIndicator (G.missingColorsAt F color v) c *
        G.graphFirstMoment R charge F color v c

/-- The second term in the error expansion. -/
def graphOverlapSecond {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) : ℝ :=
  ((q : ℝ) / G.momentMissingSize F color v) ^ 2 *
    ((∑ c : Fin q,
        paletteIndicator (G.missingColorsAt F color v) c *
          G.graphDiagonalMoment R charge F color v c) +
      ∑ c : Fin q, ∑ d : Fin q,
        paletteIndicator (G.missingColorsAt F color v) c *
          paletteIndicator (G.missingColorsAt F color v) d *
            G.graphPairMoment R charge F color v c d)

/-- Summing the normalized overlap itself against residual charge gives the
graph first-overlap term. -/
theorem sum_charge_mul_momentLambda_eq_graphOverlapFirst {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < G.momentMissingSize F color w)
    (v : G.V) :
    (∑ e ∈ R,
      if G.Inc v e then charge e * G.momentLambda F color e else 0) =
      G.graphOverlapFirst R charge F color v := by
  unfold graphOverlapFirst graphFirstMoment firstMoment
    graphMomentItemPalette graphMomentItemWeight paletteSize
  rw [← Finset.sum_attach]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hinc : G.Inc v e.1
  · rw [if_pos hinc,
      G.momentLambda_eq_indicator_sum_of_inc F color hmissing hinc]
    simp only [if_pos hinc]
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _hc
    unfold paletteIndicator momentMissingSize
    by_cases hc : c ∈ G.missingColorsAt F color v <;>
      by_cases hd : c ∈ G.missingColorsAt F color
        (G.kempeOtherEndpoint v e.1) <;> simp [hc, hd] <;> ring
  · simp [hinc]

/-- Pointwise square of the indicator dot product, split into diagonal and
ordered off-diagonal terms. -/
theorem indicator_dot_sq_eq_diag_add_offdiag {q : ℕ}
    (left right : Finset (Fin q)) :
    (∑ c : Fin q,
      paletteIndicator left c * paletteIndicator right c) ^ 2 =
      (∑ c : Fin q,
        paletteIndicator left c * paletteIndicator right c) +
      ∑ c : Fin q, ∑ d : Fin q,
        if c = d then 0 else
          paletteIndicator left c * paletteIndicator left d *
            (paletteIndicator right c * paletteIndicator right d) := by
  let a : Fin q → ℝ := fun c ↦
    paletteIndicator left c * paletteIndicator right c
  have hoff := sum_offDiagonal_mul a
  have hsquare : ∀ c, (a c) ^ 2 = a c := by
    intro c
    unfold a paletteIndicator
    split <;> split <;> norm_num
  have hoff' :
      (∑ c : Fin q, ∑ d : Fin q,
        if c = d then 0 else
          paletteIndicator left c * paletteIndicator left d *
            (paletteIndicator right c * paletteIndicator right d)) =
        (∑ c : Fin q, a c) ^ 2 - ∑ c : Fin q, (a c) ^ 2 := by
    calc
      _ = ∑ c : Fin q, ∑ d : Fin q,
          if c = d then 0 else a c * a d := by
        apply Finset.sum_congr rfl
        intro c _hc
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hcd : c = d
        · simp [hcd]
        · simp [hcd, a]
          ring
      _ = _ := hoff
  change (∑ c : Fin q, a c) ^ 2 =
    (∑ c : Fin q, a c) +
      ∑ c : Fin q, ∑ d : Fin q,
        if c = d then 0 else
          paletteIndicator left c * paletteIndicator left d *
            (paletteIndicator right c * paletteIndicator right d)
  rw [hoff']
  simp_rw [hsquare]
  ring

/-- Summing squared normalized overlaps gives the graph second-overlap
term. -/
theorem sum_charge_mul_momentLambda_sq_eq_graphOverlapSecond {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < G.momentMissingSize F color w)
    (v : G.V) :
    (∑ e ∈ R,
      if G.Inc v e then charge e * (G.momentLambda F color e) ^ 2
      else 0) =
      G.graphOverlapSecond R charge F color v := by
  let K : ℝ := (q : ℝ) / G.momentMissingSize F color v
  let A : Fin q → ℝ := fun c ↦
    paletteIndicator (G.missingColorsAt F color v) c
  unfold graphOverlapSecond graphDiagonalMoment graphPairMoment
    diagonalMoment pairMoment graphMomentItemPalette graphMomentItemWeight
    paletteSize
  rw [← Finset.sum_attach]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Expand each edge square, then collect diagonal and off-diagonal terms.
  calc
    (∑ e : R,
      if G.Inc v e.1 then
        charge e.1 * (G.momentLambda F color e.1) ^ 2 else 0) =
        ∑ e : R,
          (if G.Inc v e.1 then charge e.1 else 0) * K ^ 2 *
            (((∑ c : Fin q,
                A c * paletteIndicator
                  (G.missingColorsAt F color
                    (G.kempeOtherEndpoint v e.1)) c) ^ 2) /
              (G.momentMissingSize F color
                (G.kempeOtherEndpoint v e.1)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e.1
      · rw [if_pos hinc,
          G.momentLambda_eq_indicator_sum_of_inc F color hmissing hinc]
        simp only [K, A, if_pos hinc]
        have hw : G.momentMissingSize F color
            (G.kempeOtherEndpoint v e.1) ≠ 0 :=
          ne_of_gt (hmissing (G.kempeOtherEndpoint v e.1))
        have hsum :
            (∑ c : Fin q,
              paletteIndicator (G.missingColorsAt F color v) c *
                (paletteIndicator
                    (G.missingColorsAt F color
                      (G.kempeOtherEndpoint v e.1)) c /
                  G.momentMissingSize F color
                    (G.kempeOtherEndpoint v e.1))) =
              (∑ c : Fin q,
                paletteIndicator (G.missingColorsAt F color v) c *
                  paletteIndicator
                    (G.missingColorsAt F color
                      (G.kempeOtherEndpoint v e.1)) c) /
                G.momentMissingSize F color
                  (G.kempeOtherEndpoint v e.1) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro c _hc
          ring
        rw [hsum]
        field_simp [hw]
      · simp [hinc]
    _ = ∑ e : R,
          (if G.Inc v e.1 then charge e.1 else 0) * K ^ 2 *
            (((∑ c : Fin q,
                A c * paletteIndicator
                  (G.missingColorsAt F color
                    (G.kempeOtherEndpoint v e.1)) c) +
              ∑ c : Fin q, ∑ d : Fin q,
                if c = d then 0 else
                  A c * A d *
                    (paletteIndicator
                      (G.missingColorsAt F color
                        (G.kempeOtherEndpoint v e.1)) c *
                     paletteIndicator
                      (G.missingColorsAt F color
                        (G.kempeOtherEndpoint v e.1)) d)) /
              (G.momentMissingSize F color
                (G.kempeOtherEndpoint v e.1)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [indicator_dot_sq_eq_diag_add_offdiag
        (G.missingColorsAt F color v)
        (G.missingColorsAt F color (G.kempeOtherEndpoint v e.1))]
    _ = ((q : ℝ) / G.momentMissingSize F color v) ^ 2 *
        ((∑ c : Fin q,
            paletteIndicator (G.missingColorsAt F color v) c *
              ∑ e : R,
                (if G.Inc v e.1 then charge e.1 else 0) /
                  (G.momentMissingSize F color
                    (G.kempeOtherEndpoint v e.1)) ^ 2 *
                  paletteIndicator
                    (G.missingColorsAt F color
                      (G.kempeOtherEndpoint v e.1)) c) +
          ∑ c : Fin q, ∑ d : Fin q,
            paletteIndicator (G.missingColorsAt F color v) c *
              paletteIndicator (G.missingColorsAt F color v) d *
                (if c = d then 0 else
                  ∑ e : R,
                    (if G.Inc v e.1 then charge e.1 else 0) /
                      (G.momentMissingSize F color
                        (G.kempeOtherEndpoint v e.1)) ^ 2 *
                      paletteIndicator
                        (G.missingColorsAt F color
                          (G.kempeOtherEndpoint v e.1)) c *
                      paletteIndicator
                        (G.missingColorsAt F color
                          (G.kempeOtherEndpoint v e.1)) d)) := by
      let Q : ℝ := ((q : ℝ) / G.momentMissingSize F color v) ^ 2
      let C : R → ℝ := fun e ↦
        if G.Inc v e.1 then charge e.1 else 0
      let M : R → ℝ := fun e ↦
        G.momentMissingSize F color (G.kempeOtherEndpoint v e.1)
      let B : R → Fin q → ℝ := fun e c ↦
        paletteIndicator
          (G.missingColorsAt F color (G.kempeOtherEndpoint v e.1)) c
      let A₀ : Fin q → ℝ := fun c ↦
        paletteIndicator (G.missingColorsAt F color v) c
      change
        (∑ e : R, C e * Q *
          (((∑ c : Fin q, A₀ c * B e c) +
            ∑ c : Fin q, ∑ d : Fin q,
              if c = d then 0 else A₀ c * A₀ d * (B e c * B e d)) /
            (M e) ^ 2)) =
          Q *
            ((∑ c : Fin q, A₀ c *
                ∑ e : R, C e / (M e) ^ 2 * B e c) +
              ∑ c : Fin q, ∑ d : Fin q,
                A₀ c * A₀ d *
                  (if c = d then 0 else
                    ∑ e : R, C e / (M e) ^ 2 * B e c * B e d))
      have hdiag :
          (∑ e : R, C e * ((∑ c : Fin q, A₀ c * B e c) / (M e) ^ 2)) =
            ∑ c : Fin q, A₀ c *
              ∑ e : R, C e / (M e) ^ 2 * B e c := by
        calc
          _ = ∑ e : R, ∑ c : Fin q,
              A₀ c * (C e / (M e) ^ 2 * B e c) := by
            apply Finset.sum_congr rfl
            intro e _he
            rw [Finset.sum_div, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _hc
            ring
          _ = ∑ c : Fin q, ∑ e : R,
              A₀ c * (C e / (M e) ^ 2 * B e c) := by
            rw [Finset.sum_comm]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro c _hc
            rw [Finset.mul_sum]
      have hoff :
          (∑ e : R, C e *
            ((∑ c : Fin q, ∑ d : Fin q,
              if c = d then 0 else A₀ c * A₀ d * (B e c * B e d)) /
              (M e) ^ 2)) =
            ∑ c : Fin q, ∑ d : Fin q,
              A₀ c * A₀ d *
                (if c = d then 0 else
                  ∑ e : R, C e / (M e) ^ 2 * B e c * B e d) := by
        calc
          _ = ∑ e : R, ∑ c : Fin q, ∑ d : Fin q,
              C e * ((if c = d then 0 else
                A₀ c * A₀ d * (B e c * B e d)) / (M e) ^ 2) := by
            apply Finset.sum_congr rfl
            intro e _he
            rw [Finset.sum_div, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _hc
            rw [Finset.sum_div, Finset.mul_sum]
          _ = ∑ c : Fin q, ∑ d : Fin q, ∑ e : R,
              C e * ((if c = d then 0 else
                A₀ c * A₀ d * (B e c * B e d)) / (M e) ^ 2) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro c _hc
            rw [Finset.sum_comm]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro c _hc
            apply Finset.sum_congr rfl
            intro d _hd
            by_cases hcd : c = d
            · simp [hcd]
            · simp only [hcd, if_false]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro e _he
              ring
      calc
        (∑ e : R, C e * Q *
          (((∑ c : Fin q, A₀ c * B e c) +
            ∑ c : Fin q, ∑ d : Fin q,
              if c = d then 0 else A₀ c * A₀ d * (B e c * B e d)) /
            (M e) ^ 2)) =
            Q *
              ((∑ e : R,
                C e * ((∑ c : Fin q, A₀ c * B e c) / (M e) ^ 2)) +
               ∑ e : R,
                C e * ((∑ c : Fin q, ∑ d : Fin q,
                  if c = d then 0 else
                    A₀ c * A₀ d * (B e c * B e d)) / (M e) ^ 2)) := by
          calc
            _ = ∑ e : R,
                (Q * (C e * ((∑ c : Fin q, A₀ c * B e c) / (M e) ^ 2)) +
                 Q * (C e * ((∑ c : Fin q, ∑ d : Fin q,
                   if c = d then 0 else
                     A₀ c * A₀ d * (B e c * B e d)) / (M e) ^ 2))) := by
              apply Finset.sum_congr rfl
              intro e _he
              rw [add_div]
              ring
            _ = (∑ e : R,
                  Q * (C e * ((∑ c : Fin q, A₀ c * B e c) / (M e) ^ 2))) +
                ∑ e : R,
                  Q * (C e * ((∑ c : Fin q, ∑ d : Fin q,
                    if c = d then 0 else
                      A₀ c * A₀ d * (B e c * B e d)) / (M e) ^ 2)) := by
              rw [Finset.sum_add_distrib]
            _ = Q *
                ((∑ e : R,
                  C e * ((∑ c : Fin q, A₀ c * B e c) / (M e) ^ 2)) +
                 ∑ e : R,
                  C e * ((∑ c : Fin q, ∑ d : Fin q,
                    if c = d then 0 else
                      A₀ c * A₀ d * (B e c * B e d)) / (M e) ^ 2)) := by
              rw [mul_add]
              apply congrArg₂ (· + ·)
              · exact (Finset.mul_sum (Finset.univ : Finset R)
                  (fun e ↦ C e *
                    ((∑ c : Fin q, A₀ c * B e c) / (M e) ^ 2)) Q).symm
              · exact (Finset.mul_sum (Finset.univ : Finset R)
                  (fun e ↦ C e *
                    ((∑ c : Fin q, ∑ d : Fin q,
                      if c = d then 0 else
                        A₀ c * A₀ d * (B e c * B e d)) / (M e) ^ 2)) Q).symm
        _ = _ := by rw [hdiag, hoff]
    _ = _ := by
      apply congrArg (fun x : ℝ ↦
        ((q : ℝ) / G.momentMissingSize F color v) ^ 2 * x)
      apply congrArg₂ (· + ·)
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _hc
        rw [← Finset.mul_sum]
        apply congrArg (fun x : ℝ ↦
          paletteIndicator (G.missingColorsAt F color v) c * x)
        apply Finset.sum_congr rfl
        intro e _he
        unfold momentMissingSize paletteIndicator
        by_cases hmem : c ∈ G.missingColorsAt F color
          (G.kempeOtherEndpoint v e.1) <;> simp [hmem]
      · apply Finset.sum_congr rfl
        intro c _hc
        apply Finset.sum_congr rfl
        intro d _hd
        by_cases hcd : c = d
        · simp [hcd]
        · simp only [hcd, if_false]
          apply congrArg (fun x : ℝ ↦
            paletteIndicator (G.missingColorsAt F color v) c *
              paletteIndicator (G.missingColorsAt F color v) d * x)
          apply Finset.sum_congr rfl
          intro e _he
          unfold momentMissingSize paletteIndicator
          by_cases hc : c ∈ G.missingColorsAt F color
            (G.kempeOtherEndpoint v e.1) <;>
            by_cases hd : d ∈ G.missingColorsAt F color
              (G.kempeOtherEndpoint v e.1) <;> simp [hc, hd]

/-- Exact expansion consumed by `WeightedMomentErrorBound`. -/
theorem momentSquaredError_eq_graphOverlapExpansion {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < G.momentMissingSize F color w)
    (v : G.V) :
    G.momentSquaredError R charge F color v =
      G.graphOverlapSecond R charge F color v -
        2 * G.graphOverlapFirst R charge F color v +
          G.restrictedCharge R charge v := by
  unfold momentSquaredError
  rw [show
      (∑ e ∈ R,
        if G.Inc v e then charge e *
          (G.momentLambda F color e - 1) ^ 2 else 0) =
      (∑ e ∈ R,
        if G.Inc v e then charge e *
          (G.momentLambda F color e) ^ 2 else 0) -
      2 * (∑ e ∈ R,
        if G.Inc v e then charge e *
          G.momentLambda F color e else 0) +
      G.restrictedCharge R charge v by
    unfold restrictedCharge
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hinc : G.Inc v e
    · simp [hinc]
      ring
    · simp [hinc]]
  rw [G.sum_charge_mul_momentLambda_sq_eq_graphOverlapSecond
      R charge F color hmissing v,
    G.sum_charge_mul_momentLambda_eq_graphOverlapFirst
      R charge F color hmissing v]

end

end WeightedMultigraph
end WeightedEdgeColoring
