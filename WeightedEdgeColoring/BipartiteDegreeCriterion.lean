import WeightedEdgeColoring.ExactBipartiteTwo
import WeightedEdgeColoring.GreedyCleanup

/-!
# A degree criterion for the bipartite coefficient-two bound

This file isolates the elementary part of the minimal-counterexample
argument.  A positive lower bound on the weights converts weighted degree
into ordinary degree.  If it makes every ordinary star have at most
`2 * ceil deltaW` edges, Kőnig's theorem gives the desired weighted coloring
because a proper coloring is automatically feasible.

The result does not settle the mixed-weight case: there is no uniform
positive lower bound in the asymptotic theorem.  It is nevertheless the
exact deterministic endpoint of any reduction which proves that a minimal
counterexample has no sufficiently small edge.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/-- A uniform weight floor converts the cardinality of a restricted star
into a lower bound for its total weight. -/
theorem degreeOn_mul_le_restrictedWeight
    (F : Finset G.E) (a : ℝ)
    (hlower : ∀ e ∈ F, a ≤ G.weight e) (v : G.V) :
    (G.degreeOn F v : ℝ) * a ≤
      ∑ e ∈ F, if G.Inc v e then G.weight e else 0 := by
  classical
  let S := F.filter (G.Inc v)
  have hsum : ∑ _e ∈ S, a ≤ ∑ e ∈ S, G.weight e := by
    exact Finset.sum_le_sum fun e he ↦
      hlower e (Finset.mem_filter.mp he).1
  have hload :
      (∑ e ∈ F, if G.Inc v e then G.weight e else 0) =
        ∑ e ∈ S, G.weight e := by
    simp [S, Finset.sum_filter]
  have hcard : ∑ _e ∈ S, a = (S.card : ℝ) * a := by
    simp
  rw [hcard, ← hload] at hsum
  exact hsum

/-- Strict version of `degreeOn_mul_le_restrictedWeight` for a nonempty
restricted star and a strict weight floor. -/
theorem degreeOn_mul_lt_restrictedWeight
    (F : Finset G.E) (a : ℝ)
    (hlower : ∀ e ∈ F, a < G.weight e) (v : G.V)
    (hnonempty : (F.filter (G.Inc v)).Nonempty) :
    (G.degreeOn F v : ℝ) * a <
      ∑ e ∈ F, if G.Inc v e then G.weight e else 0 := by
  classical
  let S := F.filter (G.Inc v)
  have hsum : ∑ _e ∈ S, a < ∑ e ∈ S, G.weight e := by
    exact Finset.sum_lt_sum_of_nonempty (by simpa [S] using hnonempty) fun e he ↦
      hlower e (Finset.mem_filter.mp he).1
  have hload :
      (∑ e ∈ F, if G.Inc v e then G.weight e else 0) =
        ∑ e ∈ S, G.weight e := by
    simp [S, Finset.sum_filter]
  have hcard : ∑ _e ∈ S, a = (S.card : ℝ) * a := by simp
  rw [hcard, ← hload] at hsum
  exact hsum

/-- Kőnig's theorem gives a `q`-color weighted coloring as soon as every
ordinary star has degree at most `q`. -/
theorem chiW_le_of_bipartite_degreeOn_le
    (hbip : G.IsBipartite) (q : ℕ) (hq : 0 < q)
    (hdegree : ∀ v, G.degreeOn Finset.univ v ≤ q) :
    G.chiW ≤ q := by
  rcases hbip with ⟨b⟩
  rcases G.exists_isProperOn_bipartite_of_degreeOn_le b Finset.univ q hq
      hdegree with ⟨color, hproper⟩
  have hfeasible : G.IsFeasibleOn Finset.univ color :=
    G.isFeasibleOn_of_isProperOn Finset.univ color hproper
  apply G.chiW_le_of_hasWeightedColoring
  exact ⟨color, (G.isWeightedColoring_iff_feasibleOn_univ color).2 hfeasible⟩

/-- A quantitative weight floor forcing ordinary degree below
`2 * ceil deltaW + 1` proves the exact coefficient-two bound.

This is the form used after a small-edge exclusion: if every edge has weight
at least `a` and `deltaW < (2 * ceil deltaW + 1) * a`, then a star with
`2 * ceil deltaW + 1` edges would already have weight greater than `deltaW`.
-/
theorem chiW_le_two_ceil_of_weight_floor
    (hbip : G.IsBipartite) (a : ℝ)
    (ha : 0 < a)
    (hlower : ∀ e, a ≤ G.weight e)
    (hgap : G.deltaW < (2 * Nat.ceil G.deltaW + 1 : ℕ) * a) :
    G.chiW ≤ 2 * Nat.ceil G.deltaW := by
  let n := Nat.ceil G.deltaW
  by_cases hn0 : n = 0
  · have hzero : G.deltaW = 0 := by
      apply le_antisymm
      · have hceil : G.deltaW ≤ n := Nat.le_ceil G.deltaW
        simpa [n, hn0] using hceil
      · exact G.deltaW_nonneg
    have hz := G.hasWeightedColoring_zero_of_deltaW_eq_zero hzero
    have hchi : G.chiW ≤ 0 := G.chiW_le_of_hasWeightedColoring hz
    simpa [n, hn0] using hchi
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    apply G.chiW_le_of_bipartite_degreeOn_le hbip (2 * n)
      (Nat.mul_pos (by decide) hn)
    intro v
    have hweighted := G.degreeOn_mul_le_restrictedWeight
      Finset.univ a (fun e _he ↦ hlower e) v
    have hrestricted := G.restrictedStarWeight_le_starWeight Finset.univ v
    have hstar := G.starWeight_le_deltaW v
    by_contra hdegree
    have hlarge : 2 * n + 1 ≤ G.degreeOn Finset.univ v := by omega
    have hlargeReal : ((2 * n + 1 : ℕ) : ℝ) ≤
        G.degreeOn Finset.univ v := by exact_mod_cast hlarge
    have hmul : ((2 * n + 1 : ℕ) : ℝ) * a ≤
        (G.degreeOn Finset.univ v : ℝ) * a := by
      exact mul_le_mul_of_nonneg_right hlargeReal ha.le
    have hcontra : ((2 * n + 1 : ℕ) : ℝ) * a ≤ G.deltaW :=
      hmul.trans (hweighted.trans (hrestricted.trans hstar))
    have hgap' : G.deltaW < ((2 * n + 1 : ℕ) : ℝ) * a := by
      simpa [n] using hgap
    exact (not_lt_of_ge hcontra) hgap'

/-- Removing an incident edge from a restricted coloring saves its full
weight in the sum of the color loads at either endpoint. -/
theorem sum_colorLoadOn_add_weight_le_deltaW_of_not_mem
    {q : ℕ} (P : Finset G.E) (color : G.E → Fin q)
    (e : G.E) (heP : e ∉ P) (v : G.V) (hve : G.Inc v e) :
    (∑ i, G.colorLoadOn P color v i) + G.weight e ≤ G.deltaW := by
  have hrestricted := G.restrictedStarWeight_le_starWeight (insert e P) v
  rw [Finset.sum_insert heP] at hrestricted
  simp only [hve, if_true] at hrestricted
  rw [G.sum_colorLoadOn]
  nlinarith [hrestricted.trans (G.starWeight_le_deltaW v)]

/-- Insert one omitted edge whenever the total two-endpoint residual capacity
dominates the two endpoint loads.  If no color accepted `e`, every color
would have combined endpoint load strictly larger than `1 - weight e`; after
summing over the palette this contradicts `hnumeric`.

Unlike the descending-weight insertion lemma, this statement uses no order
on the already colored edges. -/
theorem extend_feasibleOn_of_two_residual_capacity
    (q : ℕ) (hq : 0 < q) (P : Finset G.E)
    (color : G.E → Fin q) (hfeasible : G.IsFeasibleOn P color)
    (e : G.E) (heP : e ∉ P)
    (hnumeric :
      2 * (G.deltaW - G.weight e) ≤
        (q : ℝ) * (1 - G.weight e)) :
    ∃ color' : G.E → Fin q,
      G.IsFeasibleOn (insert e P) color' ∧
      ∀ f ∈ P, color' f = color f := by
  classical
  have hsumFst := G.sum_colorLoadOn_add_weight_le_deltaW_of_not_mem
    P color e heP (G.fst e) (Or.inl rfl)
  have hsumSnd := G.sum_colorLoadOn_add_weight_le_deltaW_of_not_mem
    P color e heP (G.snd e) (Or.inr rfl)
  have hroom : ∃ i : Fin q,
      G.colorLoadOn P color (G.fst e) i + G.weight e ≤ 1 ∧
      G.colorLoadOn P color (G.snd e) i + G.weight e ≤ 1 := by
    by_contra hnone
    push_neg at hnone
    have hpoint : ∀ i : Fin q,
        1 - G.weight e <
          G.colorLoadOn P color (G.fst e) i +
            G.colorLoadOn P color (G.snd e) i := by
      intro i
      by_cases hfst :
          G.colorLoadOn P color (G.fst e) i + G.weight e ≤ 1
      · have hsnd := hnone i hfst
        have hnonneg := G.colorLoadOn_nonneg P color (G.fst e) i
        linarith
      · have hnonneg := G.colorLoadOn_nonneg P color (G.snd e) i
        linarith
    have huniv : (Finset.univ : Finset (Fin q)).Nonempty := by
      exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩
    have hsumStrict :
        ∑ _i : Fin q, (1 - G.weight e) <
          ∑ i : Fin q,
            (G.colorLoadOn P color (G.fst e) i +
              G.colorLoadOn P color (G.snd e) i) := by
      exact Finset.sum_lt_sum_of_nonempty huniv fun i _hi ↦ hpoint i
    have hloads :
        (∑ i : Fin q, G.colorLoadOn P color (G.fst e) i) +
            ∑ i : Fin q, G.colorLoadOn P color (G.snd e) i ≤
          2 * (G.deltaW - G.weight e) := by
      linarith
    have hcontradiction :
        (q : ℝ) * (1 - G.weight e) <
          2 * (G.deltaW - G.weight e) := by
      rw [Finset.sum_add_distrib] at hsumStrict
      simpa [mul_sub] using hsumStrict.trans_le hloads
    exact (not_lt_of_ge hnumeric) hcontradiction
  rcases hroom with ⟨i, hiFst, hiSnd⟩
  let color' : G.E → Fin q := Function.update color e i
  refine ⟨color', ?_, ?_⟩
  · intro v j
    dsimp only [color']
    rw [G.colorLoadOn_insert_update P color e i heP v j]
    by_cases hinc : G.Inc v e
    · rcases hinc with hfst | hsnd
      · subst v
        by_cases hij : i = j
        · subst j
          simpa [Inc] using hiFst
        · simp [hij]
          exact hfeasible _ _
      · subst v
        by_cases hij : i = j
        · subst j
          simpa [Inc] using hiSnd
        · simp [hij]
          exact hfeasible _ _
    · simp [hinc]
      exact hfeasible _ _
  · intro f hf
    dsimp only [color']
    apply Function.update_of_ne
    intro hfe
    exact heP (hfe ▸ hf)

/-- The explicit small-edge extension threshold.  For `n ≥ 2`, every
feasible `2n`-coloring of the other edges extends across an edge of weight at
most `(n - deltaW) / (n - 1)`. -/
theorem extend_feasibleOn_two_of_small_edge
    (n : ℕ) (hn : 2 ≤ n) (P : Finset G.E)
    (color : G.E → Fin (2 * n)) (hfeasible : G.IsFeasibleOn P color)
    (e : G.E) (heP : e ∉ P)
    (hsmall :
      G.weight e ≤ ((n : ℝ) - G.deltaW) / ((n : ℝ) - 1)) :
    ∃ color' : G.E → Fin (2 * n),
      G.IsFeasibleOn (insert e P) color' ∧
      ∀ f ∈ P, color' f = color f := by
  have hnreal : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hden : 0 < (n : ℝ) - 1 := by linarith
  have hmul : G.weight e * ((n : ℝ) - 1) ≤
      (n : ℝ) - G.deltaW := by
    exact (le_div_iff₀ hden).mp hsmall
  apply G.extend_feasibleOn_of_two_residual_capacity (2 * n)
    (Nat.mul_pos (by decide) (by omega)) P color hfeasible e heP
  push_cast
  nlinarith

/-- Consequently, an edge-minimal obstruction to a `2n` coloring contains
no edge at or below the small-edge threshold.  Minimality is expressed
directly on the partial coloring of `univ.erase e`, so this lemma introduces
no restricted graph type and no choice principle beyond the finite model
already used by the development. -/
theorem weight_gt_small_edge_threshold_of_minimal_obstruction
    (n : ℕ) (hn : 2 ≤ n)
    (hbad : ¬ G.HasWeightedColoring (2 * n))
    (hminimal : ∀ e : G.E,
      ∃ color : G.E → Fin (2 * n),
        G.IsFeasibleOn (Finset.univ.erase e) color) :
    ∀ e : G.E,
      ((n : ℝ) - G.deltaW) / ((n : ℝ) - 1) < G.weight e := by
  intro e
  by_contra hsmall
  push_neg at hsmall
  rcases hminimal e with ⟨color, hfeasible⟩
  have heP : e ∉ (Finset.univ.erase e : Finset G.E) := by simp
  rcases G.extend_feasibleOn_two_of_small_edge n hn
      (Finset.univ.erase e) color hfeasible e heP hsmall with
    ⟨color', hfull, _hpreserve⟩
  apply hbad
  refine ⟨color', (G.isWeightedColoring_iff_feasibleOn_univ color').2 ?_⟩
  simpa using hfull

/-- Exact coefficient two in the first mixed-weight range.  The proof is a
finite strong induction on the colored edge set.  A small edge is reinserted
by `extend_feasibleOn_two_of_small_edge`; if there is no small edge, its
strict weight floor forces ordinary degree at most `2n`, and Kőnig colors the
whole current set properly.

For `n = ceil deltaW`, this gives the concrete ranges `deltaW ≤ 5/3` when
`n = 2`, `deltaW ≤ 7/3` when `n = 3`, and their general analogue. -/
theorem hasWeightedColoring_two_of_delta_le_two_n_add_one_div_three
    (hbip : G.IsBipartite) (n : ℕ) (hn : 2 ≤ n)
    (hdelta : G.deltaW ≤ (2 * (n : ℝ) + 1) / 3) :
    G.HasWeightedColoring (2 * n) := by
  classical
  rcases hbip with ⟨b⟩
  have hq : 0 < 2 * n := Nat.mul_pos (by decide) (by omega)
  have hnreal : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hdeltaLt : G.deltaW < n := by
    have hbound : (2 * (n : ℝ) + 1) / 3 < n := by nlinarith
    exact hdelta.trans_lt hbound
  let a : ℝ := ((n : ℝ) - G.deltaW) / ((n : ℝ) - 1)
  have hden : 0 < (n : ℝ) - 1 := sub_pos.mpr hnreal
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (sub_pos.mpr hdeltaLt) hden
  have hthreshold :
      G.deltaW ≤ ((2 * n + 1 : ℕ) : ℝ) * a := by
    have hthree : 3 * G.deltaW ≤ 2 * (n : ℝ) + 1 := by
      nlinarith
    dsimp [a]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).2
    push_cast
    nlinarith
  have hsub : ∀ S : Finset G.E,
      ∃ color : G.E → Fin (2 * n), G.IsFeasibleOn S color := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
        by_cases hsmall : ∃ e ∈ S, G.weight e ≤ a
        · rcases hsmall with ⟨e, heS, heSmall⟩
          let P := S.erase e
          have hPsub : P ⊂ S := Finset.erase_ssubset heS
          rcases ih P hPsub with ⟨color, hcolor⟩
          have heP : e ∉ P := by simp [P]
          have heSmall' :
              G.weight e ≤ ((n : ℝ) - G.deltaW) / ((n : ℝ) - 1) := by
            simpa [a] using heSmall
          rcases G.extend_feasibleOn_two_of_small_edge n hn P color hcolor
              e heP heSmall' with ⟨color', hcolor', _hpreserve⟩
          refine ⟨color', ?_⟩
          simpa [P, Finset.insert_erase heS] using hcolor'
        · have hlargeWeight : ∀ e ∈ S, a < G.weight e := by
            intro e he
            have : ¬G.weight e ≤ a := by
              intro h
              exact hsmall ⟨e, he, h⟩
            exact lt_of_not_ge this
          have hdegree : ∀ v, G.degreeOn S v ≤ 2 * n := by
            intro v
            by_contra hd
            have hdLarge : 2 * n + 1 ≤ G.degreeOn S v := by omega
            have hnonempty : (S.filter (G.Inc v)).Nonempty := by
              apply Finset.card_pos.mp
              change 0 < G.degreeOn S v
              omega
            have hstrict := G.degreeOn_mul_lt_restrictedWeight
              S a hlargeWeight v hnonempty
            have hrestricted := G.restrictedStarWeight_le_starWeight S v
            have hstar := G.starWeight_le_deltaW v
            have hdReal : ((2 * n + 1 : ℕ) : ℝ) ≤
                G.degreeOn S v := by exact_mod_cast hdLarge
            have hmul : ((2 * n + 1 : ℕ) : ℝ) * a ≤
                (G.degreeOn S v : ℝ) * a :=
              mul_le_mul_of_nonneg_right hdReal ha.le
            linarith
          rcases G.exists_isProperOn_bipartite_of_degreeOn_le b S
              (2 * n) hq hdegree with ⟨color, hproper⟩
          exact ⟨color, G.isFeasibleOn_of_isProperOn S color hproper⟩
  rcases hsub Finset.univ with ⟨color, hcolor⟩
  exact ⟨color, (G.isWeightedColoring_iff_feasibleOn_univ color).2 hcolor⟩

/-- Optimum form of the preceding mixed-range theorem. -/
theorem chiW_le_two_of_delta_le_two_n_add_one_div_three
    (hbip : G.IsBipartite) (n : ℕ) (hn : 2 ≤ n)
    (hdelta : G.deltaW ≤ (2 * (n : ℝ) + 1) / 3) :
    G.chiW ≤ 2 * n := by
  exact G.chiW_le_of_hasWeightedColoring
    (G.hasWeightedColoring_two_of_delta_le_two_n_add_one_div_three
      hbip n hn hdelta)

/-- Ceiling-normalized form of the exact mixed-range result. -/
theorem chiW_le_two_ceil_of_delta_le_two_ceil_add_one_div_three
    (hbip : G.IsBipartite) (hn : 2 ≤ Nat.ceil G.deltaW)
    (hdelta :
      G.deltaW ≤ (2 * (Nat.ceil G.deltaW : ℝ) + 1) / 3) :
    G.chiW ≤ 2 * Nat.ceil G.deltaW := by
  exact G.chiW_le_two_of_delta_le_two_n_add_one_div_three hbip
    (Nat.ceil G.deltaW) hn hdelta

end WeightedMultigraph
end WeightedEdgeColoring
