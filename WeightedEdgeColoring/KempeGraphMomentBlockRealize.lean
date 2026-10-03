import WeightedEdgeColoring.KempeGraphMomentBlockDecode

/-!
# Realizing one ideal pairing block with controlled graph-moment errors

This is the direct specialization of the finite component-coin selector to
the normalized graph rows.  The hypotheses are explicit numerical bounds on
the concrete caps; `KempeGraphMomentBlockBounds` supplies them from the
global `alpha,C,L,n` assumptions.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators
open WeightedEdgeColoring.FiniteCategoricalSelection
open WeightedEdgeColoring.FinitePartialResamplingNumerics
open WeightedEdgeColoring.FiniteColorPairBlockOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

theorem exists_kempeBoolSwitch_realizing_momentBlock_of_bounds {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (M D B : ℝ) (hM : 0 < M) (hD : 0 ≤ D) (hB : 0 < B)
    (hDB1 : 1 ≤ D / B)
    (K : ℕ) (hK : 0 < K) (hMK : M / B ≤ K)
    (hvertexCapRow : ∀ w row,
      G.momentBlockVertexCap (n := n) R charge F color a b w row ≤ B / 2)
    (hvertexCapTotal : ∀ w,
      ∑ row : MomentBlockRow G.V q,
        G.momentBlockVertexCap (n := n) R charge F color a b w row ≤ D / 2)
    (hmeanUpper : ∀ row,
      rowMean (fun (_component : G.TwoColorComponent F color a b)
        (_bit : Bool) ↦ (1 : ℝ) / 2)
        (G.momentBlockUse (n := n) R charge F color a b) row ≤ M)
    (hmeanLower : ∀ row,
      (∑ component : G.TwoColorComponent F color a b,
        G.componentInfluenceCap F color a b
          (G.momentBlockVertexCap (n := n) R charge F color a b) component row) -
        rowMean (fun (_component : G.TwoColorComponent F color a b)
          (_bit : Bool) ↦ (1 : ℝ) / 2)
          (G.momentBlockUse (n := n) R charge F color a b) row ≤ M) :
    ∃ coin : G.TwoColorComponent F color a b → Bool,
      G.IsProperOn F (G.kempeBoolSwitch F color a b coin) ∧
      (∀ v side,
        |G.graphFirstMoment R charge F
            (G.kempeBoolSwitch F color a b coin) v
            (blockSideColor a b side) -
          singleBlockAverage a b
            (G.graphFirstMoment R charge F color v)
            (blockSideColor a b side)| <
          B * packingDeviation (M / B) (D / B)) ∧
      (∀ v side,
        |(n : ℝ) *
          (G.graphDiagonalMoment R charge F
              (G.kempeBoolSwitch F color a b coin) v
              (blockSideColor a b side) -
            singleBlockAverage a b
              (G.graphDiagonalMoment R charge F color v)
              (blockSideColor a b side))| <
          B * packingDeviation (M / B) (D / B)) ∧
      ∀ v side d, d ≠ a → d ≠ b →
        |(n : ℝ) *
          (G.graphPairMoment R charge F
              (G.kempeBoolSwitch F color a b coin) v
              (blockSideColor a b side) d -
            pairBlockAverage a b
              (G.graphPairMoment R charge F color v)
              (blockSideColor a b side) d)| <
          B * packingDeviation (M / B) (D / B) := by
  have hcap0 : ∀ w row,
      0 ≤ G.momentBlockVertexCap (n := n) R charge F color a b w row := by
    intro w row
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
  obtain ⟨coin, hcoin⟩ :=
    G.exists_componentCoins_abs_rowLoad_sub_mean_lt_scaledDeviation
      F color hproper a b
      (G.momentBlockUse (n := n) R charge F color a b)
      (G.momentBlockVertexCap (n := n) R charge F color a b)
      M D B hM hD hB hDB1 K hK hMK
      (G.momentBlockUse_nonneg (n := n) R charge F color a b hcharge)
      (G.momentBlockUse_le_componentInfluenceCap (n := n)
        R charge F color a b hcharge)
      hcap0 hvertexCapRow hvertexCapTotal hmeanUpper hmeanLower
  refine ⟨coin, ?_, ?_, ?_, ?_⟩
  · simpa [kempeBoolSwitch] using
      G.isProperOn_kempeComponentSwitch F color hproper a b
        (fun component ↦ coin component = true)
  · intro v side
    rw [G.graphFirstMoment_blockDeviation_eq_rowDeviation (n := n)
      R charge F color hproper a b coin v side]
    exact hcoin (.first v side)
  · intro v side
    rw [G.graphDiagonalMoment_blockDeviation_eq_rowDeviation (n := n)
      R charge F color hproper a b coin v side]
    exact hcoin (.diagonal v side)
  · intro v side d hda hdb
    rw [G.graphPairMoment_blockDeviation_eq_rowDeviation (n := n)
      R charge F color hproper a b d hda hdb coin v side]
    exact hcoin (.pair v side d)

/-- Unscaled form of the second-moment conclusions. -/
theorem exists_kempeBoolSwitch_realizing_momentBlock_unscaled_of_bounds
    {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e) (hn : 0 < n)
    (M D B : ℝ) (hM : 0 < M) (hD : 0 ≤ D) (hB : 0 < B)
    (hDB1 : 1 ≤ D / B)
    (K : ℕ) (hK : 0 < K) (hMK : M / B ≤ K)
    (hvertexCapRow : ∀ w row,
      G.momentBlockVertexCap (n := n) R charge F color a b w row ≤ B / 2)
    (hvertexCapTotal : ∀ w,
      ∑ row : MomentBlockRow G.V q,
        G.momentBlockVertexCap (n := n) R charge F color a b w row ≤ D / 2)
    (hmeanUpper : ∀ row,
      rowMean (fun (_component : G.TwoColorComponent F color a b)
        (_bit : Bool) ↦ (1 : ℝ) / 2)
        (G.momentBlockUse (n := n) R charge F color a b) row ≤ M)
    (hmeanLower : ∀ row,
      (∑ component : G.TwoColorComponent F color a b,
        G.componentInfluenceCap F color a b
          (G.momentBlockVertexCap (n := n) R charge F color a b) component row) -
        rowMean (fun (_component : G.TwoColorComponent F color a b)
          (_bit : Bool) ↦ (1 : ℝ) / 2)
          (G.momentBlockUse (n := n) R charge F color a b) row ≤ M) :
    ∃ coin : G.TwoColorComponent F color a b → Bool,
      G.IsProperOn F (G.kempeBoolSwitch F color a b coin) ∧
      (∀ v side,
        |G.graphFirstMoment R charge F
            (G.kempeBoolSwitch F color a b coin) v
            (blockSideColor a b side) -
          singleBlockAverage a b
            (G.graphFirstMoment R charge F color v)
            (blockSideColor a b side)| <
          B * packingDeviation (M / B) (D / B)) ∧
      (∀ v side,
        |G.graphDiagonalMoment R charge F
            (G.kempeBoolSwitch F color a b coin) v
            (blockSideColor a b side) -
          singleBlockAverage a b
            (G.graphDiagonalMoment R charge F color v)
            (blockSideColor a b side)| <
          (B * packingDeviation (M / B) (D / B)) / n) ∧
      ∀ v side d, d ≠ a → d ≠ b →
        |G.graphPairMoment R charge F
            (G.kempeBoolSwitch F color a b coin) v
            (blockSideColor a b side) d -
          pairBlockAverage a b
            (G.graphPairMoment R charge F color v)
            (blockSideColor a b side) d| <
          (B * packingDeviation (M / B) (D / B)) / n := by
  rcases G.exists_kempeBoolSwitch_realizing_momentBlock_of_bounds
      R charge F color hproper a b hcharge M D B hM hD hB hDB1
      K hK hMK hvertexCapRow hvertexCapTotal hmeanUpper hmeanLower with
    ⟨coin, hproperCoin, hfirst, hdiag, hpair⟩
  refine ⟨coin, hproperCoin, hfirst, ?_, ?_⟩
  · intro v side
    have h := hdiag v side
    rw [abs_mul, abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)] at h
    exact (lt_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).2 (by
      simpa [mul_comm] using h)
  · intro v side d hda hdb
    have h := hpair v side d hda hdb
    rw [abs_mul, abs_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)] at h
    exact (lt_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).2 (by
      simpa [mul_comm] using h)

end

end WeightedMultigraph
end WeightedEdgeColoring
