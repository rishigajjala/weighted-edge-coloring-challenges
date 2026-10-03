import WeightedEdgeColoring.KempePairingStage
import WeightedEdgeColoring.WeightedMomentStatistics
import WeightedEdgeColoring.WeightedMomentProposal

/-!
# The `z`, `d`, and `Z` statistics on a weighted multigraph

For a fixed vertex `v`, regard each residual edge as an item.  Its weight is
its residual charge when it is incident with `v`, and zero otherwise.  Its
palette is the missing palette at the endpoint opposite `v`.  The generic
statistics from `WeightedMomentStatistics` then become exactly the three
quantities used in the Kempe mixing proof:

* `graphFirstMoment` is the neighbor pressure `z`;
* `graphDiagonalMoment` is the diagonal correction `d`;
* `graphPairMoment` is the ordered off-diagonal array `Z`.

The fixed-sum identities are inherited from the generic finite identities.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics
open WeightedEdgeColoring.FiniteColorPairing
open WeightedEdgeColoring.FiniteColorPairingOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Residual charge as a weight on the subtype of residual edges, with
nonincident edges assigned weight zero. -/
def graphMomentItemWeight
    (R : Finset G.E) (charge : G.E → ℝ) (v : G.V) (e : R) : ℝ :=
  if G.Inc v e.1 then charge e.1 else 0

/-- Missing palette at the endpoint of `e` opposite the fixed vertex `v`.
The value on nonincident residual edges is irrelevant because their item
weight is zero. -/
def graphMomentItemPalette {q : ℕ}
    (R : Finset G.E) (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (e : R) : Finset (Fin q) :=
  G.missingColorsAt F color (G.kempeOtherEndpoint v e.1)

/-- Graph form of the first missing-color moment. -/
def graphFirstMoment {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c : Fin q) : ℝ :=
  firstMoment
    (G.graphMomentItemPalette R F color v)
    (G.graphMomentItemWeight R charge v) c

/-- Graph form of the diagonal second moment. -/
def graphDiagonalMoment {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c : Fin q) : ℝ :=
  diagonalMoment
    (G.graphMomentItemPalette R F color v)
    (G.graphMomentItemWeight R charge v) c

/-- Graph form of the ordered off-diagonal second moment. -/
def graphPairMoment {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c d : Fin q) : ℝ :=
  pairMoment
    (G.graphMomentItemPalette R F color v)
    (G.graphMomentItemWeight R charge v) c d

/-- The harmonic correction belonging to the opposite-end palettes. -/
def graphHarmonicMoment {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) : ℝ :=
  harmonicWeight
    (G.graphMomentItemPalette R F color v)
    (G.graphMomentItemWeight R charge v)

theorem totalWeight_graphMomentItemWeight
    (R : Finset G.E) (charge : G.E → ℝ) (v : G.V) :
    totalWeight (G.graphMomentItemWeight R charge v) =
      G.restrictedCharge R charge v := by
  unfold totalWeight graphMomentItemWeight restrictedCharge
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- The graph first moment is literally the neighbor pressure. -/
theorem graphFirstMoment_eq_momentNeighborPressure {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c : Fin q) :
    G.graphFirstMoment R charge F color v c =
      G.momentNeighborPressure R charge F color v c := by
  unfold graphFirstMoment firstMoment graphMomentItemPalette
    graphMomentItemWeight paletteSize momentNeighborPressure momentMissingSize
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hinc : G.Inc v e.1
  · by_cases hmem :
        c ∈ G.missingColorsAt F color (G.kempeOtherEndpoint v e.1)
    · simp [hinc, hmem]
      ring
    · simp [hinc, hmem]
  · simp [hinc]

/-- If every missing palette is nonempty, the first-moment coordinates sum
to the residual charge at `v`. -/
theorem sum_graphFirstMoment {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (v : G.V) :
    ∑ c, G.graphFirstMoment R charge F color v c =
      G.restrictedCharge R charge v := by
  change (∑ c, firstMoment
    (G.graphMomentItemPalette R F color v)
    (G.graphMomentItemWeight R charge v) c) = _
  rw [sum_firstMoment]
  · exact G.totalWeight_graphMomentItemWeight R charge v
  · intro e
    exact hmissing (G.kempeOtherEndpoint v e.1)

/-- The diagonal coordinates sum to the harmonic correction. -/
theorem sum_graphDiagonalMoment {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (v : G.V) :
    ∑ c, G.graphDiagonalMoment R charge F color v c =
      G.graphHarmonicMoment R charge F color v := by
  apply sum_diagonalMoment
  intro e
  exact hmissing (G.kempeOtherEndpoint v e.1)

/-- The ordered off-diagonal coordinates sum to total charge minus the
harmonic correction. -/
theorem sum_graphPairMoment {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (v : G.V) :
    (∑ c, ∑ d, G.graphPairMoment R charge F color v c d) =
      G.restrictedCharge R charge v -
        G.graphHarmonicMoment R charge F color v := by
  change (∑ c, ∑ d, pairMoment
    (G.graphMomentItemPalette R F color v)
    (G.graphMomentItemWeight R charge v) c d) = _
  rw [sum_pairMoment]
  · rw [G.totalWeight_graphMomentItemWeight]
    rfl
  · intro e
    exact hmissing (G.kempeOtherEndpoint v e.1)

/-- Under nonnegative charge, the harmonic correction is nonnegative. -/
theorem graphHarmonicMoment_nonneg {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (v : G.V) :
    0 ≤ G.graphHarmonicMoment R charge F color v := by
  unfold graphHarmonicMoment harmonicWeight graphMomentItemWeight
    graphMomentItemPalette paletteSize
  apply Finset.sum_nonneg
  intro e _he
  split
  · exact div_nonneg (hcharge e.1 e.2) (Nat.cast_nonneg _)
  · simp

/-- With nonnegative charge and nonempty opposite palettes, the harmonic
correction is at most the total residual charge. -/
theorem graphHarmonicMoment_le_restrictedCharge {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, 0 < (G.missingColorsAt F color w).card)
    (v : G.V) :
    G.graphHarmonicMoment R charge F color v ≤
      G.restrictedCharge R charge v := by
  unfold graphHarmonicMoment harmonicWeight graphMomentItemWeight
    graphMomentItemPalette paletteSize
  rw [← G.totalWeight_graphMomentItemWeight R charge v]
  unfold totalWeight graphMomentItemWeight
  apply Finset.sum_le_sum
  intro e _he
  by_cases hinc : G.Inc v e.1
  · simp only [hinc, if_true]
    have hnum : 0 ≤ charge e.1 := hcharge e.1 e.2
    have hcard : (1 : ℝ) ≤
        (G.missingColorsAt F color
          (G.kempeOtherEndpoint v e.1)).card := by
      exact_mod_cast hmissing (G.kempeOtherEndpoint v e.1)
    exact div_le_self hnum hcard
  · simp [hinc]

/-- Linear missing-palette size and charge bounds give the fixed harmonic
bound used in the squared-error estimate. -/
theorem graphHarmonicMoment_le_inv_alpha {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (alpha : ℝ) (v : G.V) (halpha : 0 < alpha) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤
      (G.missingColorsAt F color w).card)
    (hrestricted : G.restrictedCharge R charge v ≤ n) :
    G.graphHarmonicMoment R charge F color v ≤ 1 / alpha := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold graphHarmonicMoment harmonicWeight graphMomentItemPalette
    graphMomentItemWeight paletteSize
  rw [show (1 : ℝ) / alpha = (n : ℝ) / (alpha * n) by
    field_simp]
  calc
    (∑ e : R,
      (if G.Inc v e.1 then charge e.1 else 0) /
        (G.missingColorsAt F color
          (G.kempeOtherEndpoint v e.1)).card) ≤
        ∑ e : R,
          (if G.Inc v e.1 then charge e.1 else 0) / (alpha * n) := by
      apply Finset.sum_le_sum
      intro e _he
      have hnum : 0 ≤ if G.Inc v e.1 then charge e.1 else 0 := by
        split
        · exact hcharge e.1 e.2
        · exact le_rfl
      exact div_le_div_of_nonneg_left hnum (mul_pos halpha hnreal)
        (hmissing (G.kempeOtherEndpoint v e.1))
    _ = G.restrictedCharge R charge v / (alpha * n) := by
      rw [← Finset.sum_div]
      exact congrArg (fun x : ℝ ↦ x / (alpha * n))
        (G.totalWeight_graphMomentItemWeight R charge v)
    _ ≤ (n : ℝ) / (alpha * n) := by
      exact div_le_div_of_nonneg_right hrestricted (mul_pos halpha hnreal).le

/-! ## Conditional averages under one simultaneous pairing stage -/

theorem paletteSize_graphMomentItemPalette_kempePairingStage {q : ℕ}
    (R : Finset G.E) (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (p : Pairing (Fin q))
    (coin : G.PairingStageCoin F color p) (v : G.V) (e : R) :
    paletteSize
        (G.graphMomentItemPalette R F
          (G.kempePairingStage F color p coin) v) e =
      paletteSize (G.graphMomentItemPalette R F color v) e := by
  unfold paletteSize graphMomentItemPalette
  exact_mod_cast (G.card_missingColorsAt_eq_of_isProperOn
    F color (G.kempePairingStage F color p coin)
    hproper (G.isProperOn_kempePairingStage F color hproper p coin)
    (G.kempeOtherEndpoint v e.1)).symm

/-- The complete coin sum of the graph first moment is the paired average
of the old graph first moment. -/
theorem sum_graphFirstMoment_kempePairingStage {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (p : Pairing (Fin q))
    (v : G.V) (c : Fin q) :
    (∑ coin : G.PairingStageCoin F color p,
      G.graphFirstMoment R charge F
        (G.kempePairingStage F color p coin) v c) =
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) *
        singleAverage p
          (G.graphFirstMoment R charge F color v) c := by
  let M : ℝ := Fintype.card (G.PairingStageCoin F color p)
  let oldPalette := G.graphMomentItemPalette R F color v
  let itemWeight := G.graphMomentItemWeight R charge v
  calc
    (∑ coin : G.PairingStageCoin F color p,
      G.graphFirstMoment R charge F
        (G.kempePairingStage F color p coin) v c) =
        ∑ e : R, itemWeight e / paletteSize oldPalette e *
          (∑ coin : G.PairingStageCoin F color p,
            paletteIndicator
              (G.missingColorsAt F
                (G.kempePairingStage F color p coin)
                (G.kempeOtherEndpoint v e.1)) c) := by
      unfold graphFirstMoment firstMoment
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      simp only [oldPalette, itemWeight]
      simp_rw [G.paletteSize_graphMomentItemPalette_kempePairingStage
        R F color hproper p _ v e]
      rw [← Finset.mul_sum]
      rfl
    _ = ∑ e : R, itemWeight e / paletteSize oldPalette e *
          (M * singleAverage p
            (fun d ↦ paletteIndicator
              (G.missingColorsAt F color
                (G.kempeOtherEndpoint v e.1)) d) c) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [G.sum_paletteIndicator_kempePairingStage F color p
        (G.kempeOtherEndpoint v e.1) c]
    _ = M * singleAverage p
          (G.graphFirstMoment R charge F color v) c := by
      unfold singleAverage graphFirstMoment firstMoment
      ring_nf
      rw [Finset.sum_add_distrib]
      repeat' rw [Finset.mul_sum]
      repeat' rw [Finset.sum_mul]
      ring_nf
      simp only [oldPalette, itemWeight, paletteIndicator,
        graphMomentItemPalette]

theorem average_graphFirstMoment_kempePairingStage {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (p : Pairing (Fin q))
    (v : G.V) (c : Fin q) :
    (∑ coin : G.PairingStageCoin F color p,
      G.graphFirstMoment R charge F
        (G.kempePairingStage F color p coin) v c) /
        (Fintype.card (G.PairingStageCoin F color p) : ℝ) =
      singleAverage p (G.graphFirstMoment R charge F color v) c := by
  rw [G.sum_graphFirstMoment_kempePairingStage
    R charge F color hproper p v c]
  have hcard :
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The same conditional averaging identity for the diagonal moment. -/
theorem sum_graphDiagonalMoment_kempePairingStage {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (p : Pairing (Fin q))
    (v : G.V) (c : Fin q) :
    (∑ coin : G.PairingStageCoin F color p,
      G.graphDiagonalMoment R charge F
        (G.kempePairingStage F color p coin) v c) =
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) *
        singleAverage p
          (G.graphDiagonalMoment R charge F color v) c := by
  let M : ℝ := Fintype.card (G.PairingStageCoin F color p)
  let oldPalette := G.graphMomentItemPalette R F color v
  let itemWeight := G.graphMomentItemWeight R charge v
  calc
    (∑ coin : G.PairingStageCoin F color p,
      G.graphDiagonalMoment R charge F
        (G.kempePairingStage F color p coin) v c) =
        ∑ e : R, itemWeight e / (paletteSize oldPalette e) ^ 2 *
          (∑ coin : G.PairingStageCoin F color p,
            paletteIndicator
              (G.missingColorsAt F
                (G.kempePairingStage F color p coin)
                (G.kempeOtherEndpoint v e.1)) c) := by
      unfold graphDiagonalMoment diagonalMoment
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      simp only [oldPalette, itemWeight]
      simp_rw [G.paletteSize_graphMomentItemPalette_kempePairingStage
        R F color hproper p _ v e]
      rw [← Finset.mul_sum]
      rfl
    _ = ∑ e : R, itemWeight e / (paletteSize oldPalette e) ^ 2 *
          (M * singleAverage p
            (fun d ↦ paletteIndicator
              (G.missingColorsAt F color
                (G.kempeOtherEndpoint v e.1)) d) c) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [G.sum_paletteIndicator_kempePairingStage F color p
        (G.kempeOtherEndpoint v e.1) c]
    _ = M * singleAverage p
          (G.graphDiagonalMoment R charge F color v) c := by
      unfold singleAverage graphDiagonalMoment diagonalMoment
      ring_nf
      rw [Finset.sum_add_distrib]
      repeat' rw [Finset.mul_sum]
      repeat' rw [Finset.sum_mul]
      ring_nf
      simp only [oldPalette, itemWeight, paletteIndicator,
        graphMomentItemPalette]

/-- The complete coin sum of every off-diagonal graph pair moment is the
conditional `pairAverage` of the old array. -/
theorem sum_graphPairMoment_kempePairingStage {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (p : Pairing (Fin q))
    (v : G.V) {c d : Fin q} (hcd : c ≠ d) :
    (∑ coin : G.PairingStageCoin F color p,
      G.graphPairMoment R charge F
        (G.kempePairingStage F color p coin) v c d) =
      (Fintype.card (G.PairingStageCoin F color p) : ℝ) *
        pairAverage p (G.graphPairMoment R charge F color v) c d := by
  let M : ℝ := Fintype.card (G.PairingStageCoin F color p)
  let oldPalette := G.graphMomentItemPalette R F color v
  let itemWeight := G.graphMomentItemWeight R charge v
  calc
    (∑ coin : G.PairingStageCoin F color p,
      G.graphPairMoment R charge F
        (G.kempePairingStage F color p coin) v c d) =
        ∑ e : R, itemWeight e / (paletteSize oldPalette e) ^ 2 *
          (∑ coin : G.PairingStageCoin F color p,
            paletteIndicator
                (G.missingColorsAt F
                  (G.kempePairingStage F color p coin)
                  (G.kempeOtherEndpoint v e.1)) c *
              paletteIndicator
                (G.missingColorsAt F
                  (G.kempePairingStage F color p coin)
                  (G.kempeOtherEndpoint v e.1)) d) := by
      unfold graphPairMoment pairMoment
      simp only [hcd, if_false]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _he
      simp only [oldPalette, itemWeight]
      simp_rw [G.paletteSize_graphMomentItemPalette_kempePairingStage
        R F color hproper p _ v e]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      rfl
    _ = ∑ e : R, itemWeight e / (paletteSize oldPalette e) ^ 2 *
          (M * pairAverage p
            (fun a b ↦
              paletteIndicator
                  (G.missingColorsAt F color
                    (G.kempeOtherEndpoint v e.1)) a *
                paletteIndicator
                  (G.missingColorsAt F color
                    (G.kempeOtherEndpoint v e.1)) b) c d) := by
      apply Finset.sum_congr rfl
      intro e _he
      rw [G.sum_paletteIndicator_mul_kempePairingStage F color p
        (G.kempeOtherEndpoint v e.1) hcd]
    _ = M * pairAverage p
          (G.graphPairMoment R charge F color v) c d := by
      unfold pairAverage graphPairMoment pairMoment
      simp only [hcd, if_false]
      by_cases hpair : partner (Fin q) p c = d
      · simp [hpair]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _he
        dsimp only [oldPalette, itemWeight]
        unfold paletteIndicator graphMomentItemPalette
        by_cases hc : c ∈
            G.missingColorsAt F color (G.kempeOtherEndpoint v e.1) <;>
          by_cases hd : d ∈
            G.missingColorsAt F color (G.kempeOtherEndpoint v e.1) <;>
          simp [hc, hd]; ring
      · have hcpartner : c ≠ partner (Fin q) p d := by
          intro h
          apply hpair
          simpa only [partner_partner] using
            congrArg (partner (Fin q) p) h
        have hpartners :
            partner (Fin q) p c ≠ partner (Fin q) p d := by
          intro h
          apply hcd
          simpa only [partner_partner] using
            congrArg (partner (Fin q) p) h
        simp only [hpair, hcpartner, hpartners, if_false]
        ring_nf
        repeat' rw [Finset.sum_add_distrib]
        repeat' rw [Finset.mul_sum]
        repeat' rw [Finset.sum_mul]
        ring_nf
        simp only [oldPalette, itemWeight, paletteIndicator,
          graphMomentItemPalette]
        have hswap :
            (∑ x : R,
              ((M * G.graphMomentItemWeight R charge v x *
                    (paletteSize
                      (G.graphMomentItemPalette R F color v) x)⁻¹ ^ 2 *
                  (if d ∈ G.missingColorsAt F color
                      (G.kempeOtherEndpoint v x.1) then 1 else 0)) *
                (if partner (Fin q) p c ∈ G.missingColorsAt F color
                    (G.kempeOtherEndpoint v x.1) then 1 else 0)) *
                (1 / 4 : ℝ)) =
              ∑ x : R,
                ((M * G.graphMomentItemWeight R charge v x *
                      (paletteSize
                        (G.graphMomentItemPalette R F color v) x)⁻¹ ^ 2 *
                    (if partner (Fin q) p c ∈ G.missingColorsAt F color
                        (G.kempeOtherEndpoint v x.1) then 1 else 0)) *
                  (if d ∈ G.missingColorsAt F color
                      (G.kempeOtherEndpoint v x.1) then 1 else 0)) *
                  (1 / 4 : ℝ) := by
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        rw [hswap]
        ring

end

end WeightedMultigraph
end WeightedEdgeColoring
