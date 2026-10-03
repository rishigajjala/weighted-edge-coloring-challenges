import WeightedEdgeColoring.BipartiteDegreeCriterion

/-!
# Degree bound for finitely many harmonic classes

For a fixed cutoff `T`, every edge in one of the first `T` harmonic
classes has weight strictly larger than `1 / (T + 1)`.  Consequently an
`n`-bin local packing contains at most `n (T + 1)` such edges at any
vertex.  This is the counting estimate used to show that the first groups
discarded by linear grouping have `o(n)` ordinary degree.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Edges belonging to one of the harmonic classes with index at most `T`.
Equivalently, their harmonic denominator `floor (1 / w)` is at most `T`. -/
def finiteHarmonicHeadEdges (T : ℕ) : Finset G.E :=
  Finset.univ.filter fun e ↦ Nat.floor (1 / G.weight e) ≤ T

@[simp] theorem mem_finiteHarmonicHeadEdges (T : ℕ) (e : G.E) :
    e ∈ G.finiteHarmonicHeadEdges T ↔
      Nat.floor (1 / G.weight e) ≤ T := by
  simp [finiteHarmonicHeadEdges]

/-- An edge in the first `T` harmonic classes has a uniform strict weight
floor. -/
theorem inv_succ_lt_weight_of_mem_finiteHarmonicHeadEdges
    (T : ℕ) {e : G.E} (he : e ∈ G.finiteHarmonicHeadEdges T) :
    (1 : ℝ) / (T + 1) < G.weight e := by
  have hfloor : Nat.floor (1 / G.weight e) ≤ T :=
    (G.mem_finiteHarmonicHeadEdges T e).mp he
  have hltFloor :
      (1 : ℝ) / G.weight e <
        (Nat.floor (1 / G.weight e) : ℝ) + 1 :=
    Nat.lt_floor_add_one ((1 : ℝ) / G.weight e)
  have hfloorReal :
      (Nat.floor (1 / G.weight e) : ℝ) ≤ T := by
    exact_mod_cast hfloor
  have hrecip : (1 : ℝ) / G.weight e < (T : ℝ) + 1 := by
    linarith
  have hprod : (1 : ℝ) < ((T : ℝ) + 1) * G.weight e := by
    have := (div_lt_iff₀ (G.weight_pos e)).mp hrecip
    simpa [one_div, mul_comm] using this
  have hden : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  exact (div_lt_iff₀ hden).2 (by simpa [mul_comm] using hprod)

/-- Under an `n`-bin local packing, at most `n (T+1)` edges from the first
`T` harmonic classes are incident with any vertex. -/
theorem degreeOn_finiteHarmonicHeadEdges_le
    {n : ℕ} (T : ℕ) (hlocal : G.LocallyPacksInto n) (v : G.V) :
    G.degreeOn (G.finiteHarmonicHeadEdges T) v ≤ n * (T + 1) := by
  classical
  by_cases hnonempty :
      ((G.finiteHarmonicHeadEdges T).filter (G.Inc v)).Nonempty
  · have hweighted := G.degreeOn_mul_lt_restrictedWeight
      (G.finiteHarmonicHeadEdges T) ((1 : ℝ) / (T + 1))
      (fun e he ↦
        G.inv_succ_lt_weight_of_mem_finiteHarmonicHeadEdges T he)
      v hnonempty
    have hrestricted :=
      G.restrictedStarWeight_le_starWeight (G.finiteHarmonicHeadEdges T) v
    have hstar := G.starWeight_le_of_packsStarInto (hlocal v)
    have hdiv :
        (G.degreeOn (G.finiteHarmonicHeadEdges T) v : ℝ) /
            ((T : ℝ) + 1) < (n : ℝ) := by
      have h := hweighted.trans_le (hrestricted.trans hstar)
      simpa [div_eq_mul_inv] using h
    have hden : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have hltReal :
        (G.degreeOn (G.finiteHarmonicHeadEdges T) v : ℝ) <
          (n : ℝ) * ((T : ℝ) + 1) :=
      (div_lt_iff₀ hden).mp hdiv
    have hltNat :
        G.degreeOn (G.finiteHarmonicHeadEdges T) v < n * (T + 1) := by
      exact_mod_cast hltReal
    exact Nat.le_of_lt hltNat
  · have hempty :
        (G.finiteHarmonicHeadEdges T).filter (G.Inc v) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [degreeOn, hempty]

/-- Restricting an edge set cannot increase its ordinary degree at a
vertex. -/
theorem degreeOn_mono {F H : Finset G.E} (hFH : F ⊆ H) (v : G.V) :
    G.degreeOn F v ≤ G.degreeOn H v := by
  unfold degreeOn
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr
    ⟨hFH (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

/-- The same finite-class degree bound applies to every selected subset of
the first `T` harmonic classes. -/
theorem degreeOn_le_mul_succ_of_subset_finiteHarmonicHeadEdges
    {n T : ℕ} {F : Finset G.E}
    (hlocal : G.LocallyPacksInto n)
    (hF : F ⊆ G.finiteHarmonicHeadEdges T) (v : G.V) :
    G.degreeOn F v ≤ n * (T + 1) :=
  (G.degreeOn_mono hF v).trans
    (G.degreeOn_finiteHarmonicHeadEdges_le T hlocal v)

end

end WeightedMultigraph
end WeightedEdgeColoring
