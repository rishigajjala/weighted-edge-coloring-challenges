import WeightedEdgeColoring.SubtwoOrdinaryTriangleShortSaturation

/-!
# The ordinary seven-sixths obstruction theorem

The critical-graph theorem gives a coloring result at every palette
size at least two above the degree bound. This is the range needed by the
asymptotic sub-two quotient.
-/

namespace WeightedEdgeColoring

universe u

theorem ordinaryMultigraphSevenSixthsObstructionColoring_of_gap
    (G : WeightedMultigraph.{u}) (F : Finset G.E) (A : ℝ) (k : ℕ)
    (hA : 0 ≤ A) (hk : 0 < k)
    (hgap : A + 2 ≤ (k : ℝ))
    (hthreshold : 7 * A < 6 * (k : ℝ) + 2)
    (hdegree : ∀ v, (G.degreeOn F v : ℝ) ≤ A)
    (hodd : G.OddSetDensityAtMost F (k : ℝ)) :
    ∃ color : G.E → Fin k, G.IsProperOn F color := by
  by_contra hnoColor
  obtain ⟨C, hCF, hcritical⟩ := G.exists_colorCritical_subset hnoColor
  let d : ℕ := Nat.floor A
  have hfloorBounds := (Nat.floor_eq_iff (n := d) hA).mp (by rfl)
  have hdegreeC : ∀ v, G.degreeOn C v ≤ d := by
    intro v
    have hmono := G.degreeOn_mono_critical hCF v
    have hmonoReal :
        (G.degreeOn C v : ℝ) ≤ (G.degreeOn F v : ℝ) := by
      exact_mod_cast hmono
    have hCA : (G.degreeOn C v : ℝ) ≤ A :=
      hmonoReal.trans (hdegree v)
    by_contra hnot
    have hsucc : d + 1 ≤ G.degreeOn C v := by omega
    have hsuccReal : (d : ℝ) + 1 ≤ (G.degreeOn C v : ℝ) := by
      exact_mod_cast hsucc
    linarith [hfloorBounds.2]
  have hdA : (d : ℝ) ≤ A := by
    simpa [d] using hfloorBounds.1
  have hdk : d + 1 < k := by
    have hd2 : (d : ℝ) + 2 ≤ (k : ℝ) := by linarith
    have hd2Nat : d + 2 ≤ k := by exact_mod_cast hd2
    omega
  have hthresholdNat : 7 * d < 6 * k + 2 := by
    have hreal : ((7 * d : ℕ) : ℝ) < ((6 * k + 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  have hoddC :=
    WeightedMultigraph.OddSetDensityAtMost.mono_edges G hodd hCF
  have hno : G.NoOddSetCertificateAt C k := by
    intro hcert
    obtain ⟨S, hSodd, hS3, hviolate⟩ := hcert
    have hbound := hoddC S hSodd hS3
    linarith
  exact G.false_of_colorCritical_noOddSetCertificate_sevenSixths
    hcritical hk hdk hdegreeC hthresholdNat hno

end WeightedEdgeColoring
