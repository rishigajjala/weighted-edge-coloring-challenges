import WeightedEdgeColoring.KempeComponentActiveIndicator
import WeightedEdgeColoring.ConnectedComponentVertexSum

/-!
# Decoding the one-block component rows

The component-row load is exactly the sum over active graph vertices.  The
omitted inactive vertices contribute the same amount to the actual statistic
and to its ideal one-block average, so they cancel from every deviation.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.FiniteCategoricalSelection
open WeightedEdgeColoring.FiniteColorPairBlockOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

theorem rowLoad_momentBlockUse_eq_activeVertexSum {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool)
    (row : MomentBlockRow G.V q) :
    rowLoad (G.momentBlockUse (n := n) R charge F color a b) row coin =
      ∑ w : G.V,
        if G.IsTwoColorActive F color a b w then
          G.momentBlockVertexUse (n := n) R charge F color a b w
            (coin ((G.twoColorGraph F color a b).connectedComponentMk w)) row
        else 0 := by
  unfold rowLoad momentBlockUse
  change
    (∑ component : G.TwoColorComponent F color a b,
      ∑ w ∈ G.activeVerticesInComponent F color a b component,
        G.momentBlockVertexUse (n := n) R charge F color a b w.1
          (coin component) row) = _
  calc
    (∑ component : G.TwoColorComponent F color a b,
      ∑ w ∈ G.activeVerticesInComponent F color a b component,
        G.momentBlockVertexUse (n := n) R charge F color a b w.1
          (coin component) row) =
      ∑ component : G.TwoColorComponent F color a b,
        ∑ w ∈ G.activeVerticesInComponent F color a b component,
          G.momentBlockVertexUse (n := n) R charge F color a b w.1
            (coin ((G.twoColorGraph F color a b).connectedComponentMk w.1)) row := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      apply Finset.sum_congr rfl
      intro w _hw
      have hwcomponent :
          (G.twoColorGraph F color a b).connectedComponentMk w.1 = component :=
        (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff component w.1).mp w.2
      rw [hwcomponent]
    _ = _ := G.sum_activeVerticesInComponent F color a b
      (fun w ↦ G.momentBlockVertexUse (n := n) R charge F color a b w
        (coin ((G.twoColorGraph F color a b).connectedComponentMk w)) row)

theorem rowMean_momentBlockUse_eq_activeFairSum {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (row : MomentBlockRow G.V q) :
    rowMean (fun (_component : G.TwoColorComponent F color a b)
      (_bit : Bool) ↦ (1 : ℝ) / 2)
      (G.momentBlockUse (n := n) R charge F color a b) row =
      ∑ w : G.V,
        if G.IsTwoColorActive F color a b w then
          ∑ bit : Bool, (1 : ℝ) / 2 *
            G.momentBlockVertexUse (n := n) R charge F color a b w bit row
        else 0 := by
  unfold rowMean momentBlockUse
  change
    (∑ component : G.TwoColorComponent F color a b,
      ∑ bit : Bool, (1 / 2 : ℝ) *
        ∑ w ∈ G.activeVerticesInComponent F color a b component,
          G.momentBlockVertexUse (n := n) R charge F color a b w.1 bit row) = _
  calc
    (∑ component : G.TwoColorComponent F color a b,
      ∑ bit : Bool, (1 / 2 : ℝ) *
        ∑ w ∈ G.activeVerticesInComponent F color a b component,
          G.momentBlockVertexUse (n := n) R charge F color a b w.1 bit row) =
      ∑ component : G.TwoColorComponent F color a b,
        ∑ w ∈ G.activeVerticesInComponent F color a b component,
          ∑ bit : Bool, (1 / 2 : ℝ) *
            G.momentBlockVertexUse (n := n) R charge F color a b w.1 bit row := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      rw [show
          (∑ bit : Bool, (1 / 2 : ℝ) *
            ∑ w ∈ G.activeVerticesInComponent F color a b component,
              G.momentBlockVertexUse (n := n) R charge F color a b w.1 bit row) =
          ∑ w ∈ G.activeVerticesInComponent F color a b component,
            ∑ bit : Bool, (1 / 2 : ℝ) *
              G.momentBlockVertexUse (n := n) R charge F color a b w.1 bit row by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]]
    _ = _ := G.sum_activeVerticesInComponent F color a b
      (fun w ↦ ∑ bit : Bool, (1 : ℝ) / 2 *
        G.momentBlockVertexUse (n := n) R charge F color a b w bit row)

theorem momentMissingSize_kempeBoolSwitch {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) (w : G.V) :
    G.momentMissingSize F (G.kempeBoolSwitch F color a b coin) w =
      G.momentMissingSize F color w := by
  unfold momentMissingSize
  let flip : G.TwoColorComponent F color a b → Prop :=
    fun component ↦ coin component = true
  letI : DecidablePred flip := fun component ↦
    inferInstanceAs (Decidable (coin component = true))
  have hproperSwitch :
      G.IsProperOn F (G.kempeBoolSwitch F color a b coin) := by
    simpa [kempeBoolSwitch, flip] using
      G.isProperOn_kempeComponentSwitch F color hproper a b flip
  exact_mod_cast (G.card_missingColorsAt_eq_of_isProperOn F
    color (G.kempeBoolSwitch F color a b coin) hproper hproperSwitch w).symm

theorem firstLinkCharge_kempeBoolSwitch {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) (v w : G.V) :
    G.firstLinkCharge R charge F
      (G.kempeBoolSwitch F color a b coin) v w =
        G.firstLinkCharge R charge F color v w := by
  unfold firstLinkCharge
  apply Finset.sum_congr rfl
  intro e _he
  split
  · rw [G.momentMissingSize_kempeBoolSwitch F color hproper a b coin w]
  · rfl

theorem secondLinkCharge_kempeBoolSwitch {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) (v w : G.V) :
    G.secondLinkCharge R charge F
      (G.kempeBoolSwitch F color a b coin) v w =
        G.secondLinkCharge R charge F color v w := by
  unfold secondLinkCharge
  apply Finset.sum_congr rfl
  intro e _he
  split
  · rw [G.momentMissingSize_kempeBoolSwitch F color hproper a b coin w]
  · rfl

theorem paletteIndicator_kempeBoolSwitch_outside {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b d : Fin q)
    (hda : d ≠ a) (hdb : d ≠ b)
    (coin : G.TwoColorComponent F color a b → Bool) (w : G.V) :
    paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) w) d =
      paletteIndicator (G.missingColorsAt F color w) d := by
  unfold paletteIndicator
  have htransport :=
    G.mem_missingColorsAt_kempeComponentSwitch_localPerm_iff
      F color a b (fun component ↦ coin component = true) w d
  by_cases hflip :
      coin ((G.twoColorGraph F color a b).connectedComponentMk w) = true
  · have hmem :
        d ∈ G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) w ↔
          d ∈ G.missingColorsAt F color w := by
      simpa [kempeBoolSwitch, kempeLocalPerm, hflip,
        Equiv.swap_apply_of_ne_of_ne hda hdb] using htransport
    simp only [hmem]
  · have hmem :
        d ∈ G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) w ↔
          d ∈ G.missingColorsAt F color w := by
      simpa [kempeBoolSwitch, kempeLocalPerm, hflip] using htransport
    simp only [hmem]

theorem graphPairMoment_symmetric {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (v : G.V) (c d : Fin q) :
    G.graphPairMoment R charge F color v c d =
      G.graphPairMoment R charge F color v d c := by
  unfold graphPairMoment WeightedMomentStatistics.pairMoment
  by_cases hcd : c = d
  · subst d
    rfl
  · simp only [hcd, Ne.symm hcd, if_false]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hc : c ∈ G.graphMomentItemPalette R F color v e <;>
      by_cases hd : d ∈ G.graphMomentItemPalette R F color v e <;>
      simp [hc, hd, mul_comm]

theorem graphFirstMoment_kempeBoolSwitch_outside {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b d : Fin q)
    (hda : d ≠ a) (hdb : d ≠ b)
    (coin : G.TwoColorComponent F color a b → Bool) (v : G.V) :
    G.graphFirstMoment R charge F
        (G.kempeBoolSwitch F color a b coin) v d =
      G.graphFirstMoment R charge F color v d := by
  rw [G.graphFirstMoment_eq_sum_firstLinkCharge,
    G.graphFirstMoment_eq_sum_firstLinkCharge]
  apply Finset.sum_congr rfl
  intro w _hw
  rw [G.firstLinkCharge_kempeBoolSwitch R charge F color
      hproper a b coin,
    G.paletteIndicator_kempeBoolSwitch_outside
      F color a b d hda hdb coin]

theorem graphDiagonalMoment_kempeBoolSwitch_outside {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b d : Fin q)
    (hda : d ≠ a) (hdb : d ≠ b)
    (coin : G.TwoColorComponent F color a b → Bool) (v : G.V) :
    G.graphDiagonalMoment R charge F
        (G.kempeBoolSwitch F color a b coin) v d =
      G.graphDiagonalMoment R charge F color v d := by
  rw [G.graphDiagonalMoment_eq_sum_secondLinkCharge,
    G.graphDiagonalMoment_eq_sum_secondLinkCharge]
  apply Finset.sum_congr rfl
  intro w _hw
  rw [G.secondLinkCharge_kempeBoolSwitch R charge F color
      hproper a b coin,
    G.paletteIndicator_kempeBoolSwitch_outside
      F color a b d hda hdb coin]

theorem graphPairMoment_kempeBoolSwitch_outside {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b c d : Fin q)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (coin : G.TwoColorComponent F color a b → Bool) (v : G.V) :
    G.graphPairMoment R charge F
        (G.kempeBoolSwitch F color a b coin) v c d =
      G.graphPairMoment R charge F color v c d := by
  rw [G.graphPairMoment_eq_sum_secondLinkCharge,
    G.graphPairMoment_eq_sum_secondLinkCharge]
  by_cases hcd : c = d
  · simp [hcd]
  · simp only [hcd, if_false]
    apply Finset.sum_congr rfl
    intro w _hw
    rw [G.secondLinkCharge_kempeBoolSwitch R charge F color
        hproper a b coin,
      G.paletteIndicator_kempeBoolSwitch_outside
        F color a b c hca hcb coin,
      G.paletteIndicator_kempeBoolSwitch_outside
        F color a b d hda hdb coin]

theorem graphPairMoment_kempeBoolSwitch_paired {q : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) (v : G.V) :
    G.graphPairMoment R charge F
        (G.kempeBoolSwitch F color a b coin) v a b =
      G.graphPairMoment R charge F color v a b := by
  rw [G.graphPairMoment_eq_sum_secondLinkCharge,
    G.graphPairMoment_eq_sum_secondLinkCharge]
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, if_false]
    apply Finset.sum_congr rfl
    intro w _hw
    rw [G.secondLinkCharge_kempeBoolSwitch R charge F color
      hproper a b coin]
    simpa [mul_assoc] using congrArg (fun x : ℝ ↦
      G.secondLinkCharge R charge F color v w * x)
      (G.paletteIndicator_mul_kempeBoolSwitch_invariant
        F color a b coin w)

theorem graphFirstMoment_blockDeviation_eq_rowDeviation {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool)
    (v : G.V) (side : Bool) :
    G.graphFirstMoment R charge F
        (G.kempeBoolSwitch F color a b coin) v
        (blockSideColor a b side) -
      singleBlockAverage a b
        (G.graphFirstMoment R charge F color v)
        (blockSideColor a b side) =
      rowLoad (G.momentBlockUse (n := n) R charge F color a b)
          (.first v side) coin -
        rowMean (fun (_component : G.TwoColorComponent F color a b)
          (_bit : Bool) ↦ (1 : ℝ) / 2)
          (G.momentBlockUse (n := n) R charge F color a b) (.first v side) := by
  have hold :
      singleBlockAverage a b
          (G.graphFirstMoment R charge F color v)
          (blockSideColor a b side) =
        singleBlockAverage a b
          (fun c ↦ ∑ w : G.V,
            G.firstLinkCharge R charge F color v w *
              paletteIndicator (G.missingColorsAt F color w) c)
          (blockSideColor a b side) := by
    unfold singleBlockAverage
    rw [G.graphFirstMoment_eq_sum_firstLinkCharge,
      G.graphFirstMoment_eq_sum_firstLinkCharge]
  rw [G.graphFirstMoment_eq_sum_firstLinkCharge, hold]
  simp_rw [G.firstLinkCharge_kempeBoolSwitch
    R charge F color hproper a b coin]
  rw [G.rowLoad_momentBlockUse_eq_activeVertexSum,
    G.rowMean_momentBlockUse_eq_activeFairSum]
  unfold momentBlockVertexUse
  rw [show
      singleBlockAverage a b
        (fun c ↦ ∑ w : G.V,
          G.firstLinkCharge R charge F color v w *
            paletteIndicator (G.missingColorsAt F color w) c)
        (blockSideColor a b side) =
      ∑ w : G.V, G.firstLinkCharge R charge F color v w *
        singleBlockAverage a b
          (fun c ↦ paletteIndicator (G.missingColorsAt F color w) c)
          (blockSideColor a b side) by
    unfold singleBlockAverage
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _hw
    ring]
  rw [show
      (∑ w : G.V,
        G.firstLinkCharge R charge F color v w *
          paletteIndicator
            (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) w)
            (blockSideColor a b side)) =
      ∑ w : G.V, G.firstLinkCharge R charge F color v w *
        G.blockIndicator F color a b
          (coin ((G.twoColorGraph F color a b).connectedComponentMk w))
          side w by
    apply Finset.sum_congr rfl
    intro w _hw
    rw [G.paletteIndicator_kempeBoolSwitch_blockSideColor]]
  rw [show
      (∑ w : G.V, G.firstLinkCharge R charge F color v w *
        G.blockIndicator F color a b
          (coin ((G.twoColorGraph F color a b).connectedComponentMk w))
          side w) -
      (∑ w : G.V, G.firstLinkCharge R charge F color v w *
        singleBlockAverage a b
          (fun c ↦ paletteIndicator (G.missingColorsAt F color w) c)
          (blockSideColor a b side)) =
      (∑ w : G.V, if G.IsTwoColorActive F color a b w then
        G.firstLinkCharge R charge F color v w *
          G.blockIndicator F color a b
            (coin ((G.twoColorGraph F color a b).connectedComponentMk w))
            side w else 0) -
      (∑ w : G.V, if G.IsTwoColorActive F color a b w then
        ∑ bit : Bool, (1 / 2 : ℝ) *
          (G.firstLinkCharge R charge F color v w *
            G.blockIndicator F color a b bit side w) else 0) by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _hw
    by_cases hactive : G.IsTwoColorActive F color a b w
    · simp only [hactive, if_true]
      have hmean :
          (∑ bit : Bool, (1 / 2 : ℝ) *
              (G.firstLinkCharge R charge F color v w *
                G.blockIndicator F color a b bit side w)) =
            G.firstLinkCharge R charge F color v w *
              singleBlockAverage a b
                (fun c ↦ paletteIndicator (G.missingColorsAt F color w) c)
                (blockSideColor a b side) := by
        calc
          (∑ bit : Bool, (1 / 2 : ℝ) *
              (G.firstLinkCharge R charge F color v w *
                G.blockIndicator F color a b bit side w)) =
            ∑ bit : Bool, G.firstLinkCharge R charge F color v w *
              ((1 / 2 : ℝ) * G.blockIndicator F color a b bit side w) := by
                apply Finset.sum_congr rfl
                intro bit _hbit
                ring
          _ = G.firstLinkCharge R charge F color v w *
              ∑ bit : Bool, (1 / 2 : ℝ) *
                G.blockIndicator F color a b bit side w := by
                  rw [Finset.mul_sum]
          _ = _ := by
            rw [G.fairMean_blockIndicator F color a b w side]
      rw [hmean]
    · simp only [hactive, if_false]
      rw [G.blockIndicator_eq_singleBlockAverage_of_not_active
        F color a b w _ side hactive]
      ring]

theorem graphDiagonalMoment_blockDeviation_eq_rowDeviation {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool)
    (v : G.V) (side : Bool) :
    (n : ℝ) *
      (G.graphDiagonalMoment R charge F
          (G.kempeBoolSwitch F color a b coin) v
          (blockSideColor a b side) -
        singleBlockAverage a b
          (G.graphDiagonalMoment R charge F color v)
          (blockSideColor a b side)) =
      rowLoad (G.momentBlockUse (n := n) R charge F color a b)
          (.diagonal v side) coin -
        rowMean (fun (_component : G.TwoColorComponent F color a b)
          (_bit : Bool) ↦ (1 : ℝ) / 2)
          (G.momentBlockUse (n := n) R charge F color a b) (.diagonal v side) := by
  have hold :
      singleBlockAverage a b
          (G.graphDiagonalMoment R charge F color v)
          (blockSideColor a b side) =
        singleBlockAverage a b
          (fun c ↦ ∑ w : G.V,
            G.secondLinkCharge R charge F color v w *
              paletteIndicator (G.missingColorsAt F color w) c)
          (blockSideColor a b side) := by
    unfold singleBlockAverage
    rw [G.graphDiagonalMoment_eq_sum_secondLinkCharge,
      G.graphDiagonalMoment_eq_sum_secondLinkCharge]
  rw [G.graphDiagonalMoment_eq_sum_secondLinkCharge, hold]
  simp_rw [G.secondLinkCharge_kempeBoolSwitch
    R charge F color hproper a b coin]
  rw [G.rowLoad_momentBlockUse_eq_activeVertexSum,
    G.rowMean_momentBlockUse_eq_activeFairSum]
  unfold momentBlockVertexUse
  simp_rw [G.paletteIndicator_kempeBoolSwitch_blockSideColor]
  unfold singleBlockAverage
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hactive : G.IsTwoColorActive F color a b w
  · simp only [hactive, if_true]
    have hmean :
        (∑ bit : Bool, (1 / 2 : ℝ) *
            ((n : ℝ) * G.secondLinkCharge R charge F color v w *
              G.blockIndicator F color a b bit side w)) =
          (n : ℝ) * G.secondLinkCharge R charge F color v w *
            singleBlockAverage a b
              (fun c ↦ paletteIndicator (G.missingColorsAt F color w) c)
              (blockSideColor a b side) := by
      calc
        (∑ bit : Bool, (1 / 2 : ℝ) *
            ((n : ℝ) * G.secondLinkCharge R charge F color v w *
              G.blockIndicator F color a b bit side w)) =
          ∑ bit : Bool,
            ((n : ℝ) * G.secondLinkCharge R charge F color v w) *
              ((1 / 2 : ℝ) * G.blockIndicator F color a b bit side w) := by
                apply Finset.sum_congr rfl
                intro bit _hbit
                ring
        _ = ((n : ℝ) * G.secondLinkCharge R charge F color v w) *
            ∑ bit : Bool, (1 / 2 : ℝ) *
              G.blockIndicator F color a b bit side w := by
                rw [Finset.mul_sum]
        _ = _ := by
          rw [G.fairMean_blockIndicator F color a b w side]
    rw [hmean]
    unfold singleBlockAverage
    ring
  · simp only [hactive, if_false]
    rw [G.blockIndicator_eq_singleBlockAverage_of_not_active
      F color a b w _ side hactive]
    unfold singleBlockAverage
    ring

theorem graphPairMoment_blockDeviation_eq_rowDeviation {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b d : Fin q)
    (hda : d ≠ a) (hdb : d ≠ b)
    (coin : G.TwoColorComponent F color a b → Bool)
    (v : G.V) (side : Bool) :
    (n : ℝ) *
      (G.graphPairMoment R charge F
          (G.kempeBoolSwitch F color a b coin) v
          (blockSideColor a b side) d -
        pairBlockAverage a b
          (G.graphPairMoment R charge F color v)
          (blockSideColor a b side) d) =
      rowLoad (G.momentBlockUse (n := n) R charge F color a b)
          (.pair v side d) coin -
        rowMean (fun (_component : G.TwoColorComponent F color a b)
          (_bit : Bool) ↦ (1 : ℝ) / 2)
          (G.momentBlockUse (n := n) R charge F color a b) (.pair v side d) := by
  have hside_ne_d : blockSideColor a b side ≠ d := by
    cases side
    · exact Ne.symm hda
    · exact Ne.symm hdb
  have hswapSide_ne_d : Equiv.swap a b (blockSideColor a b side) ≠ d := by
    cases side <;> simp [blockSideColor, Ne.symm hda, Ne.symm hdb]
  have hold :
      pairBlockAverage a b
          (G.graphPairMoment R charge F color v)
          (blockSideColor a b side) d =
        pairBlockAverage a b
          (fun c₁ c₂ ↦ ∑ w : G.V,
            G.secondLinkCharge R charge F color v w *
              paletteIndicator (G.missingColorsAt F color w) c₁ *
              paletteIndicator (G.missingColorsAt F color w) c₂)
          (blockSideColor a b side) d := by
    unfold pairBlockAverage
    rw [G.graphPairMoment_eq_sum_secondLinkCharge,
      G.graphPairMoment_eq_sum_secondLinkCharge]
    rw [if_neg hside_ne_d,
      Equiv.swap_apply_of_ne_of_ne hda hdb,
      if_neg hswapSide_ne_d]
  rw [G.graphPairMoment_eq_sum_secondLinkCharge, hold]
  simp only [hside_ne_d, if_false]
  simp_rw [G.secondLinkCharge_kempeBoolSwitch
    R charge F color hproper a b coin]
  simp_rw [G.paletteIndicator_kempeBoolSwitch_blockSideColor]
  simp_rw [G.paletteIndicator_kempeBoolSwitch_outside
    F color a b d hda hdb coin]
  rw [G.rowLoad_momentBlockUse_eq_activeVertexSum,
    G.rowMean_momentBlockUse_eq_activeFairSum]
  unfold momentBlockVertexUse
  simp only [hda, hdb, or_self, if_false]
  rw [show
      pairBlockAverage a b
        (fun c₁ c₂ ↦ ∑ w : G.V,
          G.secondLinkCharge R charge F color v w *
            paletteIndicator (G.missingColorsAt F color w) c₁ *
            paletteIndicator (G.missingColorsAt F color w) c₂)
        (blockSideColor a b side) d =
      ∑ w : G.V, G.secondLinkCharge R charge F color v w *
        pairBlockAverage a b
          (fun c₁ c₂ ↦
            paletteIndicator (G.missingColorsAt F color w) c₁ *
              paletteIndicator (G.missingColorsAt F color w) c₂)
          (blockSideColor a b side) d by
    unfold pairBlockAverage
    have hdSwap : Equiv.swap a b d = d :=
      Equiv.swap_apply_of_ne_of_ne hda hdb
    rw [hdSwap]
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro w _hw
    ring]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hactive : G.IsTwoColorActive F color a b w
  · simp only [hactive, if_true]
    have hmean :
        (∑ bit : Bool, (1 / 2 : ℝ) *
            ((n : ℝ) * G.secondLinkCharge R charge F color v w *
              G.blockIndicator F color a b bit side w *
              paletteIndicator (G.missingColorsAt F color w) d)) =
          ((n : ℝ) * G.secondLinkCharge R charge F color v w) *
            pairBlockAverage a b
              (fun c₁ c₂ ↦
                paletteIndicator (G.missingColorsAt F color w) c₁ *
                  paletteIndicator (G.missingColorsAt F color w) c₂)
              (blockSideColor a b side) d := by
      calc
        (∑ bit : Bool, (1 / 2 : ℝ) *
            ((n : ℝ) * G.secondLinkCharge R charge F color v w *
              G.blockIndicator F color a b bit side w *
              paletteIndicator (G.missingColorsAt F color w) d)) =
          ∑ bit : Bool,
            ((n : ℝ) * G.secondLinkCharge R charge F color v w) *
              ((1 / 2 : ℝ) *
                (G.blockIndicator F color a b bit side w *
                  paletteIndicator (G.missingColorsAt F color w) d)) := by
                apply Finset.sum_congr rfl
                intro bit _hbit
                ring
        _ = ((n : ℝ) * G.secondLinkCharge R charge F color v w) *
            ∑ bit : Bool, (1 / 2 : ℝ) *
              (G.blockIndicator F color a b bit side w *
                paletteIndicator (G.missingColorsAt F color w) d) := by
                  rw [Finset.mul_sum]
        _ = _ := by
          rw [G.fairMean_blockIndicator_mul_outside
            F color a b d hda hdb w side]
    rw [hmean]
    ring
  · simp only [hactive, if_false]
    rw [G.blockIndicator_eq_singleBlockAverage_of_not_active
      F color a b w _ side hactive]
    unfold pairBlockAverage singleBlockAverage
    rw [Equiv.swap_apply_of_ne_of_ne hda hdb]
    ring

end

end WeightedMultigraph
end WeightedEdgeColoring
