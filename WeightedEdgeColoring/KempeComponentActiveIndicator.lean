import WeightedEdgeColoring.KempeGraphMomentBlockSelection
import WeightedEdgeColoring.ConnectedComponentVertexSum

/-!
# Active and inactive endpoints of one Kempe block

Only vertices at which exactly one of the two block colors is missing can
change a missing-color statistic.  This file records that observation both
pointwise and after taking the fair average of one component coin.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.WeightedMomentStatistics
open WeightedEdgeColoring.FiniteColorPairBlockOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

noncomputable instance instDecidablePredIsTwoColorActive {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) :
    DecidablePred (G.IsTwoColorActive F color a b) :=
  Classical.decPred _

theorem not_isTwoColorActive_iff_membership_agrees {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (w : G.V) :
    (¬ G.IsTwoColorActive F color a b w) ↔
      (a ∈ G.missingColorsAt F color w ↔
        b ∈ G.missingColorsAt F color w) := by
  unfold IsTwoColorActive
  tauto

theorem not_isTwoColorActive_iff_paletteIndicator_eq {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (w : G.V) :
    (¬ G.IsTwoColorActive F color a b w) ↔
      paletteIndicator (G.missingColorsAt F color w) a =
        paletteIndicator (G.missingColorsAt F color w) b := by
  rw [G.not_isTwoColorActive_iff_membership_agrees F color a b w]
  unfold paletteIndicator
  by_cases ha : a ∈ G.missingColorsAt F color w <;>
    by_cases hb : b ∈ G.missingColorsAt F color w <;> simp [ha, hb]

theorem paletteIndicator_add_eq_one_of_isTwoColorActive {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (w : G.V)
    (hactive : G.IsTwoColorActive F color a b w) :
    paletteIndicator (G.missingColorsAt F color w) a +
        paletteIndicator (G.missingColorsAt F color w) b = 1 := by
  rcases hactive with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;>
    simp [paletteIndicator, ha, hb]

/-- Reindex a sum over all active vertices of all two-color components as a
single filtered vertex sum. -/
theorem sum_activeVerticesInComponent {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (f : G.V → ℝ) :
    (∑ component : G.TwoColorComponent F color a b,
      ∑ w ∈ G.activeVerticesInComponent F color a b component, f w.1) =
      ∑ w : G.V,
        if G.IsTwoColorActive F color a b w then f w else 0 := by
  calc
    (∑ component : G.TwoColorComponent F color a b,
      ∑ w ∈ G.activeVerticesInComponent F color a b component, f w.1) =
        ∑ component : G.TwoColorComponent F color a b,
          ∑ w : component,
            if G.IsTwoColorActive F color a b w.1 then f w.1 else 0 := by
      apply Finset.sum_congr rfl
      intro component _hcomponent
      unfold activeVerticesInComponent
      rw [Finset.sum_filter]
      apply Finset.sum_congr
      · ext w
        simp
      · intro w _hw
        rfl
    _ = _ := WeightedEdgeColoring.SimpleGraph.sum_components_vertices_filter
      (G.twoColorGraph F color a b)
      (G.IsTwoColorActive F color a b) f

/-- The indicator after the actual component switch is the local block
indicator read from the component coin of the vertex. -/
theorem paletteIndicator_kempeBoolSwitch_blockSideColor {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool)
    (w : G.V) (side : Bool) :
    paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) w)
        (blockSideColor a b side) =
      G.blockIndicator F color a b
        (coin ((G.twoColorGraph F color a b).connectedComponentMk w))
        side w := by
  cases side
  · by_cases hcoin :
        coin ((G.twoColorGraph F color a b).connectedComponentMk w) = true <;>
      simp [blockSideColor, blockIndicator, paletteIndicator,
        G.mem_missingColorsAt_kempeBoolSwitch_a_iff, hcoin]
  · by_cases hcoin :
        coin ((G.twoColorGraph F color a b).connectedComponentMk w) = true <;>
      simp [blockSideColor, blockIndicator, paletteIndicator,
        G.mem_missingColorsAt_kempeBoolSwitch_b_iff, hcoin]

/-- At an inactive vertex either coin value gives the old indicator. -/
theorem blockIndicator_eq_old_of_not_active {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (w : G.V) (bit side : Bool)
    (hinactive : ¬ G.IsTwoColorActive F color a b w) :
    G.blockIndicator F color a b bit side w =
      paletteIndicator (G.missingColorsAt F color w)
        (blockSideColor a b side) := by
  have heq :=
    (G.not_isTwoColorActive_iff_paletteIndicator_eq F color a b w).mp
      hinactive
  cases bit <;> cases side <;>
    simp [blockIndicator, blockSideColor, heq]

theorem paletteIndicator_kempeBoolSwitch_eq_old_of_not_active {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool)
    (w : G.V) (side : Bool)
    (hinactive : ¬ G.IsTwoColorActive F color a b w) :
    paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) w)
        (blockSideColor a b side) =
      paletteIndicator (G.missingColorsAt F color w)
        (blockSideColor a b side) := by
  rw [G.paletteIndicator_kempeBoolSwitch_blockSideColor]
  exact G.blockIndicator_eq_old_of_not_active
    F color a b w _ side hinactive

/-- A fair component coin gives the arithmetic one-block average. -/
theorem fairMean_blockIndicator {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (w : G.V) (side : Bool) :
    (∑ bit : Bool, (1 : ℝ) / 2 *
      G.blockIndicator F color a b bit side w) =
      singleBlockAverage a b
        (fun c ↦ paletteIndicator (G.missingColorsAt F color w) c)
        (blockSideColor a b side) := by
  cases side <;>
    simp [blockIndicator, blockSideColor, singleBlockAverage] <;> ring

/-- The corresponding fair-coin identity for a pair coordinate whose other
color lies outside the switched block. -/
theorem fairMean_blockIndicator_mul_outside {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b d : Fin q)
    (hda : d ≠ a) (hdb : d ≠ b) (w : G.V) (side : Bool) :
    (∑ bit : Bool, (1 : ℝ) / 2 *
      (G.blockIndicator F color a b bit side w *
        paletteIndicator (G.missingColorsAt F color w) d)) =
      pairBlockAverage a b
        (fun c₁ c₂ ↦
          paletteIndicator (G.missingColorsAt F color w) c₁ *
            paletteIndicator (G.missingColorsAt F color w) c₂)
        (blockSideColor a b side) d := by
  cases side <;>
    simp [blockIndicator, blockSideColor, pairBlockAverage,
      Equiv.swap_apply_of_ne_of_ne hda hdb] <;> ring

/-- Hence an inactive endpoint already equals its one-block average. -/
theorem blockIndicator_eq_singleBlockAverage_of_not_active {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (w : G.V) (bit side : Bool)
    (hinactive : ¬ G.IsTwoColorActive F color a b w) :
    G.blockIndicator F color a b bit side w =
      singleBlockAverage a b
        (fun c ↦ paletteIndicator (G.missingColorsAt F color w) c)
        (blockSideColor a b side) := by
  rw [G.blockIndicator_eq_old_of_not_active
    F color a b w bit side hinactive]
  have heq :=
    (G.not_isTwoColorActive_iff_paletteIndicator_eq F color a b w).mp
      hinactive
  cases side <;>
    simp [blockSideColor, singleBlockAverage, heq]

end

end WeightedMultigraph
end WeightedEdgeColoring
