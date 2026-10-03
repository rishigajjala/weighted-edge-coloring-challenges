import WeightedEdgeColoring.SimpleRoundingReduction

/-!
# A bounded amount of palette padding is asymptotically free

The block construction groups colors into blocks of a fixed size.  It is
convenient to enlarge an `n`-color palette to the next multiple of that block
size.  This file gives the exact partial-rounding interface and proves that a
bounded number of added colors does not change the coefficient-one theorem.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

universe u

/-- Uniform partial rounding in a palette obtained from `n` by adding at
most `K` empty colors.  The bound `K` may depend on the requested accuracy,
but not on the graph or on `n`. -/
def SimpleUniformPaddedPartialRounding : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ N K : ℕ,
    ∀ (G : WeightedSimpleGraph.{u}) (n : ℕ), N ≤ n → G.LocallyPacksInto n →
      ∃ (palette : ℕ),
        n ≤ palette ∧ palette ≤ n + K ∧
        ∃ (P : Finset G.E) (color : G.E → Fin palette),
          G.asMultigraph.IsFeasibleOn P color ∧
          ∀ v,
            (∑ e ∈ Finset.univ \ P,
              if G.Inc v e then G.weight e else 0) ≤ eta * n

/-- The exact-product form delivered by a fixed-block construction.  For
each requested accuracy it may choose one positive block width `k`; it then
rounds every palette whose size is a multiple `B*k`. -/
def SimpleUniformMultiplePartialRounding : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ N k : ℕ, 0 < k ∧
    ∀ (G : WeightedSimpleGraph.{u}) (B : ℕ),
      N ≤ B * k → G.LocallyPacksInto (B * k) →
        ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
          G.asMultigraph.IsFeasibleOn P color ∧
          ∀ v,
            (∑ e ∈ Finset.univ \ P,
              if G.Inc v e then G.weight e else 0) ≤ eta * (B * k)

/-- Passing to the next strictly larger multiple of a fixed block width adds
at most `k` colors. -/
theorem simpleUniformPaddedPartialRounding_of_multiple
    (hround : SimpleUniformMultiplePartialRounding.{u}) :
    SimpleUniformPaddedPartialRounding.{u} := by
  intro eta heta
  have heta2 : 0 < eta / 2 := div_pos heta (by norm_num)
  rcases hround (eta / 2) heta2 with ⟨N, k, hk, hN⟩
  refine ⟨max N k, k, ?_⟩
  intro G n hn hpack
  have hnN : N ≤ n := (le_max_left N k).trans hn
  have hnk : k ≤ n := (le_max_right N k).trans hn
  let B : ℕ := n / k + 1
  let palette : ℕ := B * k
  have hnpalette : n ≤ palette := by
    have hlt : n < (n / k + 1) * k := by
      exact (Nat.div_lt_iff_lt_mul hk).mp (Nat.lt_succ_self (n / k))
    exact hlt.le
  have hpaletteK : palette ≤ n + k := by
    dsimp [palette, B]
    calc
      (n / k + 1) * k = (n / k) * k + k := by
        simp [Nat.add_mul]
      _ ≤ n + k := Nat.add_le_add_right (Nat.div_mul_le_self n k) k
  have hpackPalette : G.LocallyPacksInto palette :=
    G.locallyPacksInto_mono hnpalette hpack
  have hNpalette : N ≤ palette := hnN.trans hnpalette
  rcases hN G B (by simpa [palette] using hNpalette)
      (by simpa [palette] using hpackPalette) with
    ⟨P, color, hfeasible, hresidual⟩
  change G.E → Fin palette at color
  refine ⟨palette, hnpalette, hpaletteK, P, color, hfeasible, ?_⟩
  · intro v
    have h := hresidual v
    have hpalReal : (palette : ℝ) ≤ (n : ℝ) + k := by
      exact_mod_cast hpaletteK
    have hkReal : (k : ℝ) ≤ n := by exact_mod_cast hnk
    calc
      (∑ e ∈ Finset.univ \ P,
          if G.Inc v e then G.weight e else 0) ≤ (eta / 2) * palette := by
        simpa [palette] using h
      _ ≤ (eta / 2) * ((n : ℝ) + k) :=
        mul_le_mul_of_nonneg_left hpalReal heta2.le
      _ ≤ eta * n := by
        nlinarith


/-- Bounded palette padding plus an `o(n)` residual implies the uniform
coefficient-one theorem. -/
theorem simpleVizingAsymptotic_of_paddedPartialRounding
    (hround : SimpleUniformPaddedPartialRounding.{u}) :
    SimpleVizingAsymptotic.{u} := by
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 8
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  rcases hround eta heta with ⟨Nround, K, hroundN⟩
  let Ngrowth : ℕ := Nat.ceil (2 * ((K : ℝ) + 5) / epsilon)
  refine ⟨max Nround Ngrowth, ?_⟩
  intro G hN
  let n := G.localBinNumber
  have hNround : Nround ≤ n :=
    (le_max_left Nround Ngrowth).trans hN
  have hNgrowth : Ngrowth ≤ n :=
    (le_max_right Nround Ngrowth).trans hN
  rcases hroundN G n hNround G.locallyPacksInto_localBinNumber with
    ⟨palette, hnpalette, hpaletteK, P, partColor, hpartColor, hresidual⟩
  let M := G.asMultigraph
  have hx : 0 ≤ eta * (n : ℝ) :=
    mul_nonneg heta.le (Nat.cast_nonneg n)
  have hresidualM : ∀ v,
      (∑ e ∈ Finset.univ \ P,
        if M.Inc v e then M.weight e else 0) ≤ eta * n := by
    intro v
    simpa [M] using hresidual v
  have hcomplete : M.HasWeightedColoring
      (palette + (4 * Nat.ceil (eta * n) + 1)) :=
    M.complete_partial_with_four_ceil P partColor hpartColor
      (eta * n) hx hresidualM
  have hcompleteSimple : G.HasWeightedColoring
      (palette + (4 * Nat.ceil (eta * n) + 1)) := by
    simpa [M] using hcomplete
  have hchiNat : G.weightedChromaticIndex ≤
      palette + (4 * Nat.ceil (eta * n) + 1) :=
    G.weightedChromaticIndex_le_of_hasWeightedColoring hcompleteSimple
  have hgrowthReal : 2 * ((K : ℝ) + 5) / epsilon ≤ (n : ℝ) := by
    calc
      2 * ((K : ℝ) + 5) / epsilon ≤ (Ngrowth : ℝ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast hNgrowth
  have hgrowth : 2 * ((K : ℝ) + 5) ≤ epsilon * n := by
    simpa [mul_comm] using (div_le_iff₀ hepsilon).mp hgrowthReal
  have hceil : ((Nat.ceil (eta * n) : ℕ) : ℝ) ≤ eta * n + 1 :=
    (Nat.ceil_lt_add_one hx).le
  have hpaletteReal : (palette : ℝ) ≤ (n : ℝ) + K := by
    exact_mod_cast hpaletteK
  calc
    (G.weightedChromaticIndex : ℝ) ≤
        (palette + (4 * Nat.ceil (eta * n) + 1) : ℕ) := by
      exact_mod_cast hchiNat
    _ = (palette : ℝ) + 4 * (Nat.ceil (eta * n) : ℝ) + 1 := by
      push_cast
      ring
    _ ≤ ((n : ℝ) + K) + 4 * (eta * n + 1) + 1 := by
      gcongr
    _ ≤ (1 + epsilon) * (n : ℝ) := by
      dsimp [eta]
      nlinarith

end WeightedEdgeColoring
