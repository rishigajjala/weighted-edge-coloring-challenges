import WeightedEdgeColoring.BPOrdinaryFiveFourthObstructionProof

/-!
# The ordinary edge-coloring input at the sub-two quotient

The sub-two manuscript constructs an ordinary quotient packet graph with
degree at most `M n` and odd-set density at most `κ n`, where
`M = 1691031/1000000` and `κ = 1999/1000`.  Its ordinary-coloring step
requires `κ n + o(n)` colors uniformly in graph order.

This file states the numerical quotient input and proves two implications:
the near-fractional ordinary theorem supplies it, and the five-fourths
obstruction theorem supplies it in the smaller degree range
`Δ ≤ (4/5) κ n`. The actual quotient degree cap `M n` lies strictly above
that range. The unconditional proof of the quotient input is in
`SubtwoOrdinaryQuotientProved`.
-/

namespace WeightedEdgeColoring.Subtwo

universe u

noncomputable def ordinaryDegreeCoefficient : ℝ := 1691031 / 1000000
noncomputable def ordinaryTargetCoefficient : ℝ := 1999 / 1000

theorem ordinaryDegreeCoefficient_pos :
    0 < ordinaryDegreeCoefficient := by
  norm_num [ordinaryDegreeCoefficient]

theorem ordinaryDegreeCoefficient_lt_target :
    ordinaryDegreeCoefficient < ordinaryTargetCoefficient := by
  norm_num [ordinaryDegreeCoefficient, ordinaryTargetCoefficient]

/-- The degree cap from the sub-two quotient is too large for the existing
five-fourths ordinary theorem to reach `κ n`. -/
theorem ordinaryTarget_lt_fiveFourths_degree :
    ordinaryTargetCoefficient <
      (5 / 4 : ℝ) * ordinaryDegreeCoefficient := by
  norm_num [ordinaryDegreeCoefficient, ordinaryTargetCoefficient]

/-- Uniform ordinary coloring from the quotient's degree and odd-set
certificates. Its proof is `quotientOrdinaryColoring_proved` in
`SubtwoOrdinaryQuotientProved`. -/
def QuotientOrdinaryColoring : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ,
    ∀ (G : WeightedMultigraph.{u}) (F : Finset G.E) (n : ℕ),
      N ≤ n →
      (∀ v, (G.degreeOn F v : ℝ) ≤ ordinaryDegreeCoefficient * n) →
      G.OddSetDensityAtMost F (ordinaryTargetCoefficient * n) →
      ∃ q : ℕ, 0 < q ∧
        (q : ℝ) ≤ (ordinaryTargetCoefficient + η) * n ∧
        ∃ color : G.E → Fin q, G.IsProperOn F color

/-- The global near-fractional theorem implies the precise numerical
ordinary input at the sub-two quotient.  The converse is not asserted. -/
theorem quotientOrdinaryColoring_of_nearFractional
    (hnear : OrdinaryMultigraphNearFractionalColoring.{u}) :
    QuotientOrdinaryColoring.{u} := by
  intro η hη
  obtain ⟨N, hN⟩ := hnear ordinaryTargetCoefficient η
    (by norm_num [ordinaryTargetCoefficient]) hη
  refine ⟨N, ?_⟩
  intro G F n hn hdegree hodd
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL0 : 0 ≤ ordinaryTargetCoefficient * (n : ℝ) := by
    have hκ : 0 ≤ ordinaryTargetCoefficient := by
      norm_num [ordinaryTargetCoefficient]
    positivity
  have hdegree' : ∀ v,
      (G.degreeOn F v : ℝ) ≤ ordinaryTargetCoefficient * n := by
    intro v
    calc
      (G.degreeOn F v : ℝ) ≤ ordinaryDegreeCoefficient * n := hdegree v
      _ ≤ ordinaryTargetCoefficient * n :=
        mul_le_mul_of_nonneg_right ordinaryDegreeCoefficient_lt_target.le hn0
  obtain ⟨q, hq, hqbound, color, hproper⟩ :=
    hN G F n (ordinaryTargetCoefficient * n) hn hL0 le_rfl
      hdegree' hodd
  exact ⟨q, hq, by nlinarith, color, hproper⟩

/-- The proved five-fourths obstruction theorem does reach the sub-two
target if the quotient degree is at most `(4/5) κ n`.  This degree
hypothesis is strictly stronger than the manuscript's `M n` bound. -/
theorem exists_ordinaryColoring_of_degree_le_fourFifths_target
    (G : WeightedMultigraph.{u}) (F : Finset G.E) (n : ℕ)
    (hdegree : ∀ v, (G.degreeOn F v : ℝ) ≤
      (4 / 5 : ℝ) * ordinaryTargetCoefficient * n)
    (hodd : G.OddSetDensityAtMost F
      (ordinaryTargetCoefficient * n)) :
    ∃ q : ℕ, 0 < q ∧
      (q : ℝ) ≤ ordinaryTargetCoefficient * n + 1 ∧
      ∃ color : G.E → Fin q, G.IsProperOn F color := by
  let A : ℝ := (4 / 5 : ℝ) * ordinaryTargetCoefficient * n
  let L : ℝ := ordinaryTargetCoefficient * n
  have hA : 0 ≤ A := by
    dsimp [A, ordinaryTargetCoefficient]
    positivity
  have hL : 0 ≤ L := by
    dsimp [L, ordinaryTargetCoefficient]
    positivity
  have hdegreeA : ∀ v, (G.degreeOn F v : ℝ) ≤ A := hdegree
  obtain ⟨q, hq, hbound, color, hproper⟩ :=
    (ordinaryMultigraphFiveFourthDensityColoring_of_obstruction
      ordinaryMultigraphFiveFourthObstructionColoring_proved)
      G F A L hA hL hdegreeA hodd
  have hfive : (5 / 4 : ℝ) * A = L := by
    dsimp [A, L]
    ring
  rw [hfive, max_self] at hbound
  exact ⟨q, hq, by simpa [L] using hbound, color, hproper⟩

/-- The proved five-fourths range stops before the actual quotient cap. -/
theorem fourFifths_target_lt_ordinaryDegree :
    (4 / 5 : ℝ) * ordinaryTargetCoefficient <
      ordinaryDegreeCoefficient := by
  norm_num [ordinaryDegreeCoefficient, ordinaryTargetCoefficient]

end WeightedEdgeColoring.Subtwo
