import WeightedEdgeColoring.SubtwoOrdinarySevenSixthsObstruction

/-!
# Uniform ordinary coloring at the sub-two quotient parameters

The seven-sixths critical obstruction theorem colors every sufficiently
large quotient packet graph with at most `(1.999 + η)n` colors, using its
actual degree cap `1.691031n` and odd-set cap `1.999n`.
-/

namespace WeightedEdgeColoring

universe u

theorem exists_ordinaryColoring_subtwo_quotient
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ,
      ∀ (G : WeightedMultigraph.{u}) (F : Finset G.E) (n : ℕ),
        N ≤ n →
        (∀ v, (G.degreeOn F v : ℝ) ≤
          (1691031 / 1000000 : ℝ) * n) →
        G.OddSetDensityAtMost F ((1999 / 1000 : ℝ) * n) →
        ∃ q : ℕ, 0 < q ∧
          (q : ℝ) ≤ ((1999 / 1000 : ℝ) + η) * n ∧
          ∃ color : G.E → Fin q, G.IsProperOn F color := by
  let N : ℕ := max 7 (Nat.ceil (1 / η))
  refine ⟨N, ?_⟩
  intro G F n hn hdegree hodd
  have hn7 : 7 ≤ n := (le_max_left 7 _).trans hn
  have hnReal : (7 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn7
  let A : ℝ := (1691031 / 1000000 : ℝ) * n
  let L : ℝ := (1999 / 1000 : ℝ) * n
  let q : ℕ := Nat.ceil L
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hLle : L ≤ (q : ℝ) := Nat.le_ceil L
  have hq : 0 < q := by
    by_contra h
    have hzero : q = 0 := by omega
    simp [hzero] at hLle
    linarith
  have hqUpper : (q : ℝ) ≤ L + 1 :=
    (Nat.ceil_lt_add_one hL).le
  have hgap : A + 2 ≤ (q : ℝ) := by
    have hdiff : A + 2 ≤ L := by
      dsimp [A, L]
      nlinarith
    exact hdiff.trans hLle
  have hthreshold : 7 * A < 6 * (q : ℝ) + 2 := by
    have hcoeff : 7 * A < 6 * L + 2 := by
      dsimp [A, L]
      nlinarith
    linarith
  have hoddq : G.OddSetDensityAtMost F (q : ℝ) := by
    intro S hSodd hS3
    have hbase := hodd S hSodd hS3
    have hfactor : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by
      exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ S.card by omega))
    exact hbase.trans (mul_le_mul_of_nonneg_right hLle hfactor)
  obtain ⟨color, hproper⟩ :=
    ordinaryMultigraphSevenSixthsObstructionColoring_of_gap
      G F A q hA hq hgap hthreshold hdegree hoddq
  have hNreal : (1 : ℝ) / η ≤ n := by
    calc
      (1 : ℝ) / η ≤ (Nat.ceil (1 / η) : ℕ) := Nat.le_ceil _
      _ ≤ (N : ℕ) := by exact_mod_cast (le_max_right 7 _)
      _ ≤ (n : ℕ) := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ η * n := by
    have := (div_le_iff₀ hη).mp hNreal
    simpa [mul_comm] using this
  refine ⟨q, hq, ?_, color, hproper⟩
  dsimp [L] at hqUpper
  nlinarith

end WeightedEdgeColoring
