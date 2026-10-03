import WeightedEdgeColoring.BipartiteLightExact
import WeightedEdgeColoring.MainTheorems

namespace WeightedEdgeColoring

universe u

/-- The natural exact strengthening of the coefficient-two bipartite
theorem.  The small `39/20` counterexample in the manuscript attains this
bound (`chiW = 4`) but does not disprove it. -/
def BipartiteMultigraphTwoCeil : Prop :=
  ∀ G : WeightedMultigraph.{u},
    G.IsBipartite → G.chiW ≤ 2 * Nat.ceil G.deltaW

/-- The exact `2 * ceil Delta_w` statement would immediately imply the
uniform asymptotic coefficient-two theorem. -/
theorem bipartiteMultigraphDeltaAsymptotic_of_twoCeil
    (h : BipartiteMultigraphTwoCeil.{u}) :
    BipartiteMultigraphDeltaAsymptotic.{u} := by
  intro ε hε
  let N : ℕ := Nat.ceil (2 / ε)
  refine ⟨N, ?_⟩
  intro G hbip hN
  have htwo_div : 2 / ε ≤ G.deltaW := by
    calc
      2 / ε ≤ (N : ℝ) := Nat.le_ceil (2 / ε)
      _ ≤ G.deltaW := hN
  have htwo : 2 ≤ ε * G.deltaW := by
    simpa [mul_comm] using (div_le_iff₀ hε).mp htwo_div
  have hceil : ((Nat.ceil G.deltaW : ℕ) : ℝ) ≤ G.deltaW + 1 :=
    (Nat.ceil_lt_add_one G.deltaW_nonneg).le
  calc
    (G.chiW : ℝ) ≤ (2 * Nat.ceil G.deltaW : ℕ) := by
      exact_mod_cast h G hbip
    _ = 2 * (Nat.ceil G.deltaW : ℝ) := by norm_num
    _ ≤ 2 * (G.deltaW + 1) := by gcongr
    _ = 2 * G.deltaW + 2 := by ring
    _ ≤ 2 * G.deltaW + ε * G.deltaW := by gcongr
    _ = (2 + ε) * G.deltaW := by ring

/-- The exact coefficient-two bound holds in the ordinary-edge-coloring
regime: if every edge has weight at least one half, Kőnig's theorem colors
the whole bipartite multigraph with `2 * ceil Δₓ` colors.  Equality at one
half is allowed. -/
theorem WeightedMultigraph.chiW_le_two_ceil_of_half_le
    (G : WeightedMultigraph.{u}) (hbip : G.IsBipartite)
    (hhalf : ∀ e, (1 / 2 : ℝ) ≤ G.weight e) :
    G.chiW ≤ 2 * Nat.ceil G.deltaW := by
  let n := Nat.ceil G.deltaW
  have hdelta : G.deltaW ≤ n := Nat.le_ceil G.deltaW
  by_cases hn0 : n = 0
  · have hzero : G.deltaW = 0 := by
      apply le_antisymm
      · simpa [n, hn0] using hdelta
      · exact G.deltaW_nonneg
    have hz := G.hasWeightedColoring_zero_of_deltaW_eq_zero hzero
    have hchi : G.chiW ≤ 0 := G.chiW_le_of_hasWeightedColoring hz
    simpa [n, hn0] using hchi
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rcases hbip with ⟨b⟩
    have hdegree : ∀ v, G.degreeOn Finset.univ v ≤ 2 * n := by
      intro v
      have hweighted :=
        G.degreeOn_cast_le_two_mul_restrictedWeight Finset.univ
          (fun e _he ↦ hhalf e) v
      have hrestricted := G.restrictedStarWeight_le_starWeight Finset.univ v
      have hstar := (G.starWeight_le_deltaW v).trans hdelta
      have hreal : (G.degreeOn Finset.univ v : ℝ) ≤ (2 * n : ℕ) := by
        push_cast
        nlinarith
      exact_mod_cast hreal
    rcases G.exists_isProperOn_bipartite_of_degreeOn_le b Finset.univ
      (2 * n) (Nat.mul_pos (by decide) hn) hdegree with ⟨color, hproper⟩
    have hfeasible := G.isFeasibleOn_of_isProperOn Finset.univ color hproper
    apply G.chiW_le_of_hasWeightedColoring
    exact ⟨color, (G.isWeightedColoring_iff_feasibleOn_univ color).2 hfeasible⟩

end WeightedEdgeColoring
