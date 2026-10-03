import WeightedEdgeColoring.KempeComponentSwitch
import Mathlib.Data.Fintype.Pi

/-!
# Exact endpoint averages for random Kempe component switches

This file connects the structural component-switch API to the analytic
pairing argument.  A switch is parametrized by one Boolean for each
two-color component.  At a fixed vertex, averaging over all Boolean words
replaces either missing-color indicator by the arithmetic mean of the two old
indicators.  The proof is a finite reindexing; it introduces no probability
space and no independence assumption.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/- A two-color component is a quotient of the finite vertex type, hence is
finite.  These instances make literal Boolean component words available to
this file and to later Kempe averaging modules. -/
noncomputable instance instFintypeTwoColorComponent {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) :
    Fintype (G.TwoColorComponent F color a b) :=
  Fintype.ofFinite _

noncomputable instance instDecidableEqTwoColorComponent {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) :
    DecidableEq (G.TwoColorComponent F color a b) :=
  Classical.decEq _

/-- Component switch selected by a literal Boolean word. -/
noncomputable def kempeBoolSwitch {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) : G.E → Fin q :=
  G.kempeComponentSwitch F color a b (fun component ↦ coin component = true)

/-- At a fixed vertex the new `a` indicator reads the old `a` indicator on
coin `false`, and the old `b` indicator on coin `true`. -/
theorem mem_missingColorsAt_kempeBoolSwitch_a_iff {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) (v : G.V) :
    a ∈ G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) v ↔
      if coin ((G.twoColorGraph F color a b).connectedComponentMk v) then
        b ∈ G.missingColorsAt F color v
      else a ∈ G.missingColorsAt F color v := by
  classical
  let component :=
    (G.twoColorGraph F color a b).connectedComponentMk v
  by_cases hcoin : coin component = true
  · have hflip := G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      F color a b (fun c ↦ coin c = true) v hcoin
    simpa [kempeBoolSwitch, component, hcoin] using hflip.2
  · have hnot : ¬(coin component = true) := hcoin
    have hstay := G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      F color a b (fun c ↦ coin c = true) v hnot a
    have hfalse : coin component = false := Bool.eq_false_of_not_eq_true hcoin
    simpa [kempeBoolSwitch, component, hfalse] using hstay

/-- Symmetric endpoint formula for the new `b` indicator. -/
theorem mem_missingColorsAt_kempeBoolSwitch_b_iff {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) (v : G.V) :
    b ∈ G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) v ↔
      if coin ((G.twoColorGraph F color a b).connectedComponentMk v) then
        a ∈ G.missingColorsAt F color v
      else b ∈ G.missingColorsAt F color v := by
  classical
  let component :=
    (G.twoColorGraph F color a b).connectedComponentMk v
  by_cases hcoin : coin component = true
  · have hflip := G.mem_missingColorsAt_kempeComponentSwitch_of_flip
      F color a b (fun c ↦ coin c = true) v hcoin
    simpa [kempeBoolSwitch, component, hcoin] using hflip.1
  · have hnot : ¬(coin component = true) := hcoin
    have hstay := G.mem_missingColorsAt_kempeComponentSwitch_of_not_flip_iff
      F color a b (fun c ↦ coin c = true) v hnot b
    have hfalse : coin component = false := Bool.eq_false_of_not_eq_true hcoin
    simpa [kempeBoolSwitch, component, hfalse] using hstay

/-- Real indicator of membership in a finite palette. -/
def paletteIndicator {q : ℕ} (palette : Finset (Fin q)) (c : Fin q) : ℝ :=
  if c ∈ palette then 1 else 0

theorem paletteIndicator_nonneg {q : ℕ}
    (palette : Finset (Fin q)) (c : Fin q) :
    0 ≤ paletteIndicator palette c := by
  unfold paletteIndicator
  positivity

theorem paletteIndicator_le_one {q : ℕ}
    (palette : Finset (Fin q)) (c : Fin q) :
    paletteIndicator palette c ≤ 1 := by
  unfold paletteIndicator
  split <;> norm_num

/-- If the two tracked colors are paired with each other, their indicator
product is pointwise invariant under every component switch.  This is the
special (one-coin) case in the definition of the manuscript's `B_M`. -/
theorem paletteIndicator_mul_kempeBoolSwitch_invariant {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (coin : G.TwoColorComponent F color a b → Bool) (v : G.V) :
    paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) v) a *
      paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) v) b =
    paletteIndicator (G.missingColorsAt F color v) a *
      paletteIndicator (G.missingColorsAt F color v) b := by
  classical
  by_cases hcoin :
      coin ((G.twoColorGraph F color a b).connectedComponentMk v) = true
  · simp [paletteIndicator,
      G.mem_missingColorsAt_kempeBoolSwitch_a_iff,
      G.mem_missingColorsAt_kempeBoolSwitch_b_iff, hcoin, mul_comm]
  · have hfalse :
        coin ((G.twoColorGraph F color a b).connectedComponentMk v) = false :=
      Bool.eq_false_of_not_eq_true hcoin
    simp [paletteIndicator,
      G.mem_missingColorsAt_kempeBoolSwitch_a_iff,
      G.mem_missingColorsAt_kempeBoolSwitch_b_iff, hfalse]

/-- Summing a function of one coordinate over all Boolean words factors as
the number of assignments of the remaining coordinates times the two-value
sum. -/
theorem sum_boolWords_apply
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (component : Component) (f : Bool → ℝ) :
    (∑ coin : Component → Bool, f (coin component)) =
      (Fintype.card ({c : Component // c ≠ component} → Bool) : ℝ) *
        ∑ bit : Bool, f bit := by
  classical
  let split := Equiv.funSplitAt component Bool
  have hsplit := Equiv.sum_comp split
    (fun p : Bool × ({c : Component // c ≠ component} → Bool) ↦ f p.1)
  calc
    (∑ coin : Component → Bool, f (coin component)) =
        ∑ p : Bool × ({c : Component // c ≠ component} → Bool), f p.1 := by
      simpa [split] using hsplit
    _ = (Fintype.card ({c : Component // c ≠ component} → Bool) : ℝ) *
          ∑ bit : Bool, f bit := by
      rw [Fintype.sum_prod_type]
      simp [mul_comm]
      ring

/-- Exact factorization for two independent component-coin families.  This
is the finite independence calculation used when a pair moment contains
colors belonging to two different pairs of the current color pairing. -/
theorem sum_two_boolWords_apply_mul
    {LeftComponent RightComponent : Type*}
    [Fintype LeftComponent] [DecidableEq LeftComponent]
    [Fintype RightComponent] [DecidableEq RightComponent]
    (leftComponent : LeftComponent) (rightComponent : RightComponent)
    (f g : Bool → ℝ) :
    (∑ coins : (LeftComponent → Bool) × (RightComponent → Bool),
      f (coins.1 leftComponent) * g (coins.2 rightComponent)) =
      (Fintype.card
        ({c : LeftComponent // c ≠ leftComponent} → Bool) : ℝ) *
      (Fintype.card
        ({c : RightComponent // c ≠ rightComponent} → Bool) : ℝ) *
      (∑ leftBit : Bool, f leftBit) *
      (∑ rightBit : Bool, g rightBit) := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ leftCoins : LeftComponent → Bool,
      ∑ rightCoins : RightComponent → Bool,
        f (leftCoins leftComponent) * g (rightCoins rightComponent)) =
        (∑ leftCoins : LeftComponent → Bool, f (leftCoins leftComponent)) *
          ∑ rightCoins : RightComponent → Bool,
            g (rightCoins rightComponent) := by
      rw [Finset.sum_mul_sum]
    _ = _ := by
      rw [sum_boolWords_apply leftComponent f,
        sum_boolWords_apply rightComponent g]
      ring

/-- Normalized version of `sum_two_boolWords_apply_mul`: the two selected
bits are independent fair bits, expressed entirely by finite sums. -/
theorem average_two_boolWords_apply_mul
    {LeftComponent RightComponent : Type*}
    [Fintype LeftComponent] [DecidableEq LeftComponent]
    [Fintype RightComponent] [DecidableEq RightComponent]
    (leftComponent : LeftComponent) (rightComponent : RightComponent)
    (f g : Bool → ℝ) :
    (∑ coins : (LeftComponent → Bool) × (RightComponent → Bool),
      f (coins.1 leftComponent) * g (coins.2 rightComponent)) /
        (Fintype.card
          ((LeftComponent → Bool) × (RightComponent → Bool)) : ℝ) =
      ((∑ leftBit : Bool, f leftBit) / 2) *
        ((∑ rightBit : Bool, g rightBit) / 2) := by
  rw [sum_two_boolWords_apply_mul leftComponent rightComponent f g]
  have hleftCard :
      Fintype.card (LeftComponent → Bool) =
        2 * Fintype.card
          ({c : LeftComponent // c ≠ leftComponent} → Bool) := by
    calc
      Fintype.card (LeftComponent → Bool) =
          Fintype.card
            (Bool × ({c : LeftComponent // c ≠ leftComponent} → Bool)) :=
        Fintype.card_congr (Equiv.funSplitAt leftComponent Bool)
      _ = _ := by simp
  have hrightCard :
      Fintype.card (RightComponent → Bool) =
        2 * Fintype.card
          ({c : RightComponent // c ≠ rightComponent} → Bool) := by
    calc
      Fintype.card (RightComponent → Bool) =
          Fintype.card
            (Bool × ({c : RightComponent // c ≠ rightComponent} → Bool)) :=
        Fintype.card_congr (Equiv.funSplitAt rightComponent Bool)
      _ = _ := by simp
  have hleftRest :
      (Fintype.card
        ({c : LeftComponent // c ≠ leftComponent} → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hrightRest :
      (Fintype.card
        ({c : RightComponent // c ≠ rightComponent} → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.card_prod, hleftCard, hrightCard]
  push_cast
  field_simp

/-- Exact unnormalized average for one of the two switched colors. -/
theorem sum_paletteIndicator_kempeBoolSwitch_a {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (v : G.V) :
    (∑ coin : G.TwoColorComponent F color a b → Bool,
      paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) v) a) =
      (Fintype.card
        ({c : G.TwoColorComponent F color a b //
          c ≠ (G.twoColorGraph F color a b).connectedComponentMk v} → Bool) : ℝ) *
        (paletteIndicator (G.missingColorsAt F color v) a +
          paletteIndicator (G.missingColorsAt F color v) b) := by
  classical
  let component :=
    (G.twoColorGraph F color a b).connectedComponentMk v
  let f : Bool → ℝ := fun bit ↦
    if bit then paletteIndicator (G.missingColorsAt F color v) b
    else paletteIndicator (G.missingColorsAt F color v) a
  rw [show (∑ coin : G.TwoColorComponent F color a b → Bool,
      paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) v) a) =
      ∑ coin : G.TwoColorComponent F color a b → Bool,
        f (coin component) by
      apply Finset.sum_congr rfl
      intro coin _hcoin
      cases hbit : coin component <;>
        simp [paletteIndicator, f, component,
          G.mem_missingColorsAt_kempeBoolSwitch_a_iff, hbit]]
  rw [sum_boolWords_apply component f]
  simp [f, component, add_comm]

/-- The normalized finite average of either switched indicator is the
arithmetic mean of the two old indicators. -/
theorem average_paletteIndicator_kempeBoolSwitch_a {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (v : G.V) :
    (∑ coin : G.TwoColorComponent F color a b → Bool,
      paletteIndicator
        (G.missingColorsAt F (G.kempeBoolSwitch F color a b coin) v) a) /
        (Fintype.card
          (G.TwoColorComponent F color a b → Bool) : ℝ) =
      (paletteIndicator (G.missingColorsAt F color v) a +
        paletteIndicator (G.missingColorsAt F color v) b) / 2 := by
  classical
  rw [G.sum_paletteIndicator_kempeBoolSwitch_a F color a b v]
  let component :=
    (G.twoColorGraph F color a b).connectedComponentMk v
  have hcard :
      Fintype.card (G.TwoColorComponent F color a b → Bool) =
        2 * Fintype.card
          ({c : G.TwoColorComponent F color a b // c ≠ component} → Bool) := by
    calc
      Fintype.card (G.TwoColorComponent F color a b → Bool) =
          Fintype.card
            (Bool × ({c : G.TwoColorComponent F color a b //
              c ≠ component} → Bool)) :=
        Fintype.card_congr (Equiv.funSplitAt component Bool)
      _ = 2 * Fintype.card
          ({c : G.TwoColorComponent F color a b // c ≠ component} → Bool) := by
        simp
  rw [hcard]
  have hrest :
      (Fintype.card
        ({c : G.TwoColorComponent F color a b // c ≠ component} → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  field_simp
  ring

end
end WeightedMultigraph
end WeightedEdgeColoring
