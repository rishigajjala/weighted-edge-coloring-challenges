import WeightedEdgeColoring.PartialCompletion
import WeightedEdgeColoring.MainTheorems

open scoped BigOperators

namespace WeightedEdgeColoring

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph)

/-- Forget simplicity while retaining the same indexed edges and weights. -/
abbrev asMultigraph : WeightedMultigraph where
  V := G.V
  E := G.E
  instFintypeV := inferInstance
  instFintypeE := inferInstance
  instDecidableEqV := inferInstance
  instDecidableEqE := inferInstance
  fst := G.fst
  snd := G.snd
  noLoop := G.noLoop
  weight := G.weight
  weight_pos := G.weight_pos
  weight_le_one := G.weight_le_one

@[simp] theorem asMultigraph_inc (v : G.V) (e : G.E) :
    G.asMultigraph.Inc v e ↔ G.Inc v e := by
  rfl

@[simp] theorem asMultigraph_colorLoad {q : ℕ} (color : G.E → Fin q)
    (v : G.V) (i : Fin q) :
    G.asMultigraph.colorLoad color v i = G.colorLoad color v i := by
  rfl

@[simp] theorem asMultigraph_isWeightedColoring {q : ℕ}
    (color : G.E → Fin q) :
    G.asMultigraph.IsWeightedColoring color ↔ G.IsWeightedColoring color := by
  rfl

@[simp] theorem asMultigraph_hasWeightedColoring (q : ℕ) :
    G.asMultigraph.HasWeightedColoring q ↔ G.HasWeightedColoring q := by
  rfl

end WeightedSimpleGraph

universe u

/-- The precise whole-edge rounding statement needed for the simple-graph
coefficient-one theorem.  It says that `n` local bins can be coordinated into
`n` actual global colors while leaving only an arbitrarily small fraction of
the star weight uncolored.  Its threshold is uniform in the number of
vertices and in the edge weights.

This is a deliberately smaller interface than the manuscript's profile and
hypergraph theorem: it records exactly the output consumed by the final
cleanup argument. -/
def SimpleUniformPartialRounding : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ,
    ∀ (G : WeightedSimpleGraph.{u}) (n : ℕ), N ≤ n → G.LocallyPacksInto n →
      ∃ (P : Finset G.E) (color : G.E → Fin n),
        G.asMultigraph.IsFeasibleOn P color ∧
        ∀ v,
          (∑ e ∈ Finset.univ \ P,
            if G.Inc v e then G.weight e else 0) ≤ η * n

/-- Once whole-edge partial rounding is available, the coefficient-one
simple-graph theorem follows by the fully formalized descending-weight
cleanup.  This proof includes all ceiling and uniform little-oh bookkeeping. -/
theorem simpleVizingAsymptotic_of_partialRounding
    (hround : SimpleUniformPartialRounding.{u}) :
    SimpleVizingAsymptotic.{u} := by
  intro ε hε
  let η : ℝ := ε / 8
  have hη : 0 < η := div_pos hε (by norm_num)
  rcases hround η hη with ⟨Nround, hroundN⟩
  let Ngrowth : ℕ := Nat.ceil (10 / ε)
  refine ⟨max Nround Ngrowth, ?_⟩
  intro G hN
  let n := G.localBinNumber
  have hNround : Nround ≤ n :=
    (le_max_left Nround Ngrowth).trans hN
  have hNgrowth : Ngrowth ≤ n :=
    (le_max_right Nround Ngrowth).trans hN
  rcases hroundN G n hNround G.locallyPacksInto_localBinNumber with
    ⟨P, partColor, hpartColor, hresidual⟩
  let M := G.asMultigraph
  have hx : 0 ≤ η * (n : ℝ) := mul_nonneg hη.le (Nat.cast_nonneg n)
  have hresidualM : ∀ v,
      (∑ e ∈ Finset.univ \ P,
        if M.Inc v e then M.weight e else 0) ≤ η * n := by
    intro v
    simpa [M] using hresidual v
  have hcomplete : M.HasWeightedColoring
      (n + (4 * Nat.ceil (η * n) + 1)) :=
    M.complete_partial_with_four_ceil P partColor hpartColor
      (η * n) hx hresidualM
  have hcompleteSimple : G.HasWeightedColoring
      (n + (4 * Nat.ceil (η * n) + 1)) := by
    simpa [M] using hcomplete
  have hchiNat : G.weightedChromaticIndex ≤
      n + (4 * Nat.ceil (η * n) + 1) :=
    G.weightedChromaticIndex_le_of_hasWeightedColoring hcompleteSimple
  have htenDiv : 10 / ε ≤ (n : ℝ) := by
    calc
      10 / ε ≤ (Ngrowth : ℝ) := Nat.le_ceil (10 / ε)
      _ ≤ n := by exact_mod_cast hNgrowth
  have hten : 10 ≤ ε * (n : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp htenDiv
  have hceil : ((Nat.ceil (η * n) : ℕ) : ℝ) ≤ η * n + 1 :=
    (Nat.ceil_lt_add_one hx).le
  calc
    (G.weightedChromaticIndex : ℝ) ≤
        (n + (4 * Nat.ceil (η * n) + 1) : ℕ) := by
      exact_mod_cast hchiNat
    _ = (n : ℝ) + 4 * (Nat.ceil (η * n) : ℝ) + 1 := by
      push_cast
      ring
    _ ≤ (n : ℝ) + 4 * (η * n + 1) + 1 := by
      gcongr
    _ ≤ (1 + ε) * (n : ℝ) := by
      dsimp [η]
      nlinarith

end WeightedEdgeColoring
