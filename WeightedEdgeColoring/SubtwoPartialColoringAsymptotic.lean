import WeightedEdgeColoring.SubtwoAsymptotic
import WeightedEdgeColoring.SamePaletteResidualAdapter

/-!
# Completing a uniform almost-full physical coloring

The final global construction only needs to color all but eta*bp weight
at each vertex. The proved fresh-palette completion absorbs that loss and
its constant into the epsilon in the unrestricted asymptotic statement.
The construction of that partial coloring is still a substantive input.
-/

open scoped BigOperators
namespace WeightedEdgeColoring
universe u

/-- Uniform partial physical colorings with arbitrarily small weighted
leftovers imply the concrete `bp`/`chiW` asymptotic theorem. -/
theorem generalBPAsymptoticAt_of_uniform_partialColorings
    (c : ℝ)
    (h : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
      N ≤ G.bp → ∃ (F : Finset G.E) (q : ℕ) (color : G.E → Fin q),
        G.IsFeasibleOn F color ∧
        (q : ℝ) ≤ (c+η)*(G.bp : ℝ) ∧
        ∀ v, (∑ e ∈ Finset.univ \ F, if G.Inc v e then G.weight e else 0) ≤
          η*(G.bp : ℝ)) :
    GeneralBPAsymptoticAt.{u} c := by
  intro ε hε
  have hη : 0 < ε/10 := by positivity
  obtain ⟨N, hN⟩ := h (ε/10) hη
  refine ⟨max N (Nat.ceil (10/ε)), ?_⟩
  intro G hn
  obtain ⟨F, q, color, hfeasible, hpalette, hleft⟩ :=
    hN G ((le_max_left _ _).trans hn)
  have hlarge : 10/ε ≤ (G.bp : ℝ) := by
    calc
      10/ε ≤ (Nat.ceil (10/ε) : ℝ) := Nat.le_ceil _
      _ ≤ (G.bp : ℝ) := by exact_mod_cast (le_max_right _ _).trans hn
  have hten : 10 ≤ (G.bp : ℝ)*ε := (div_le_iff₀ hε).mp hlarge
  let loss : ℝ := (ε/10)*(G.bp : ℝ)
  have hloss : 0 ≤ loss := mul_nonneg hη.le (Nat.cast_nonneg _)
  have hcolor := G.complete_partial_with_four_ceil F color hfeasible loss hloss hleft
  have hchi := G.chiW_le_of_hasWeightedColoring hcolor
  have hchiR : (G.chiW : ℝ) ≤ (q : ℝ)+4*(Nat.ceil loss : ℝ)+1 := by
    exact_mod_cast hchi
  have hceil : (Nat.ceil loss : ℝ) < loss+1 := Nat.ceil_lt_add_one hloss
  dsimp [loss] at hceil
  nlinarith

/-- The exact final target follows once the graph-wide physical partial
coloring has been constructed with uniform thresholds. This implication
is proved; its partial-coloring hypothesis is not asserted here. -/
theorem subtwoBPAsymptotic_of_uniform_partialColorings
    (h : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ G : WeightedMultigraph.{u},
      N ≤ G.bp → ∃ (F : Finset G.E) (q : ℕ) (color : G.E → Fin q),
        G.IsFeasibleOn F color ∧
        (q : ℝ) ≤ ((1999/1000 : ℝ)+η)*(G.bp : ℝ) ∧
        ∀ v, (∑ e ∈ Finset.univ \ F, if G.Inc v e then G.weight e else 0) ≤
          η*(G.bp : ℝ)) :
    SubtwoBPAsymptotic.{u} :=
  generalBPAsymptoticAt_of_uniform_partialColorings (1999/1000 : ℝ) h

end WeightedEdgeColoring
