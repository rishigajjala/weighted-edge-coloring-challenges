import WeightedEdgeColoring.KempeGraphMomentBlockBounds
import WeightedEdgeColoring.KempeGraphMomentBlockRealize

/-!
# Concrete realization of one Kempe moment block

This file chooses the row, column, and pointwise parameters required by the
finite component-coin selector.  The resulting error is named explicitly so
that successive color blocks and successive pairing stages can reuse it.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open WeightedEdgeColoring.FinitePartialResamplingNumerics
open WeightedEdgeColoring.FiniteColorPairBlockOperators

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

def momentBlockM (_G : WeightedMultigraph.{u}) (alpha : ℝ) : ℝ :=
  1 / alpha + 1 / alpha ^ 2

def momentBlockB (_G : WeightedMultigraph.{u})
    (alpha L : ℝ) (n : ℕ) : ℝ :=
  2 * (L / alpha + L / alpha ^ 2) / n

def momentBlockD (G : WeightedMultigraph.{u})
    (alpha L : ℝ) (n q : ℕ) : ℝ :=
  G.momentBlockB alpha L n +
    4 * (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2)

def momentBlockK (G : WeightedMultigraph.{u})
    (alpha L : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (G.momentBlockM alpha / G.momentBlockB alpha L n)

def momentBlockError (G : WeightedMultigraph.{u})
    (alpha L : ℝ) (n q : ℕ) : ℝ :=
  G.momentBlockB alpha L n *
    packingDeviation
      (G.momentBlockM alpha / G.momentBlockB alpha L n)
      (G.momentBlockD alpha L n q / G.momentBlockB alpha L n)

theorem exists_kempeBoolSwitch_realizing_momentBlock_concrete
    {q n : ℕ}
    (R : Finset G.E) (charge : G.E → ℝ)
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (alpha L : ℝ) (halpha : 0 < alpha) (hL : 0 < L) (hn : 0 < n)
    (hcharge : ∀ e ∈ R, 0 ≤ charge e)
    (hmissing : ∀ w, alpha * n ≤ G.momentMissingSize F color w)
    (hrestricted : ∀ w, G.restrictedCharge R charge w ≤ n)
    (hpair : ∀ v w, G.pairCharge R charge v w ≤ L) :
    ∃ coin : G.TwoColorComponent F color a b → Bool,
      G.IsProperOn F (G.kempeBoolSwitch F color a b coin) ∧
      (∀ v side,
        |G.graphFirstMoment R charge F
            (G.kempeBoolSwitch F color a b coin) v
            (blockSideColor a b side) -
          singleBlockAverage a b
            (G.graphFirstMoment R charge F color v)
            (blockSideColor a b side)| <
          G.momentBlockError alpha L n q) ∧
      (∀ v side,
        |G.graphDiagonalMoment R charge F
            (G.kempeBoolSwitch F color a b coin) v
            (blockSideColor a b side) -
          singleBlockAverage a b
            (G.graphDiagonalMoment R charge F color v)
            (blockSideColor a b side)| <
          G.momentBlockError alpha L n q / n) ∧
      ∀ v side d, d ≠ a → d ≠ b →
        |G.graphPairMoment R charge F
            (G.kempeBoolSwitch F color a b coin) v
            (blockSideColor a b side) d -
          pairBlockAverage a b
            (G.graphPairMoment R charge F color v)
            (blockSideColor a b side) d| <
          G.momentBlockError alpha L n q / n := by
  let M := G.momentBlockM alpha
  let B := G.momentBlockB alpha L n
  let D := G.momentBlockD alpha L n q
  let K := G.momentBlockK alpha L n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 < M := by
    dsimp [M, momentBlockM]
    positivity
  have hB : 0 < B := by
    dsimp [B, momentBlockB]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D, momentBlockD]
    positivity
  have hDB1 : 1 ≤ D / B := by
    apply (le_div_iff₀ hB).2
    dsimp [D, momentBlockD]
    have htail : 0 ≤
        4 * (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2) := by
      positivity
    linarith
  have hK : 0 < K := by
    dsimp [K, momentBlockK]
    exact Nat.ceil_pos.mpr (div_pos hM hB)
  have hMK : M / B ≤ K := by
    dsimp [K, momentBlockK]
    exact Nat.le_ceil _
  have hvertexCapRow : ∀ w row,
      G.momentBlockVertexCap (n := n) R charge F color a b w row ≤ B / 2 := by
    intro w row
    calc
      G.momentBlockVertexCap (n := n) R charge F color a b w row ≤
          (L / alpha + L / alpha ^ 2) / n :=
        G.momentBlockVertexCap_le_inv_linear (n := n)
          R charge F color a b alpha L halpha hL.le hn hcharge
          hmissing hpair w row
      _ = B / 2 := by
        dsimp [B, momentBlockB]
        ring
  have hvertexCapTotal : ∀ w,
      ∑ row : MomentBlockRow G.V q,
        G.momentBlockVertexCap (n := n) R charge F color a b w row ≤ D / 2 := by
    intro w
    have hcolumn := G.sum_momentBlockVertexCap_le_columnMass (n := n)
      R charge F color a b alpha halpha hn hcharge hmissing
      hrestricted w
    calc
      (∑ row : MomentBlockRow G.V q,
        G.momentBlockVertexCap (n := n) R charge F color a b w row) ≤
          2 * (1 / alpha + ((q : ℝ) + 1) / alpha ^ 2) := hcolumn
      _ ≤ D / 2 := by
        dsimp [D, momentBlockD]
        have hB0 : 0 ≤ G.momentBlockB alpha L n := hB.le
        linarith
  have hmeanUpper : ∀ row,
      WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
        (fun (_component : G.TwoColorComponent F color a b)
          (_bit : Bool) ↦ (1 : ℝ) / 2)
        (G.momentBlockUse (n := n) R charge F color a b) row ≤ M := by
    intro row
    exact G.rowMean_momentBlockUse_le_rowMass (n := n)
      R charge F color a b alpha halpha hn hcharge hmissing
      hrestricted row
  have hmeanLower : ∀ row,
      (∑ component : G.TwoColorComponent F color a b,
        G.componentInfluenceCap F color a b
          (G.momentBlockVertexCap (n := n) R charge F color a b) component row) -
        WeightedEdgeColoring.FiniteCategoricalSelection.rowMean
          (fun (_component : G.TwoColorComponent F color a b)
            (_bit : Bool) ↦ (1 : ℝ) / 2)
          (G.momentBlockUse (n := n) R charge F color a b) row ≤ M := by
    intro row
    exact G.componentCap_sub_rowMean_momentBlockUse_le_rowMass (n := n)
      R charge F color a b alpha halpha hn hcharge hmissing
      hrestricted row
  simpa [M, D, B, K, momentBlockError] using
    (G.exists_kempeBoolSwitch_realizing_momentBlock_unscaled_of_bounds (n := n)
      R charge F color hproper a b hcharge hn M D B hM hD hB hDB1
      K hK hMK hvertexCapRow hvertexCapTotal hmeanUpper hmeanLower)

end

end WeightedMultigraph
end WeightedEdgeColoring
