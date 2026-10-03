import WeightedEdgeColoring.BPOrdinaryCriticalTriangleSaturation
import WeightedEdgeColoring.BPOrdinaryFiveFourthDensity

/-!
# The five-fourths ordinary obstruction theorem

Andersen's critical-graph argument proves the ordinary obstruction theorem
used by the packet construction.
-/

namespace WeightedEdgeColoring

universe u

/-- The Andersen three-vertex argument proves the exact obstruction
statement used by the packet construction. -/
theorem ordinaryMultigraphFiveFourthObstructionColoring_proved :
    OrdinaryMultigraphFiveFourthObstructionColoring.{u} := by
  intro G F A k hA hk hdegree hthreshold hodd
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
  have hthresholdNat : 5 * d < 4 * k + 2 := by
    have hreal : ((5 * d : ℕ) : ℝ) < ((4 * k + 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast hreal
  by_cases hdk : d < k
  · obtain ⟨S, hSodd, hS3, hviolate⟩ :=
      G.exists_oddSetCertificate_of_colorCritical_fiveFourth
        hcritical hk hdk hdegreeC hthresholdNat
    have hoddC :=
      WeightedMultigraph.OddSetDensityAtMost.mono_edges G hodd hCF
    have hbound := hoddC S hSodd hS3
    linarith
  · have hkd : k ≤ d := Nat.le_of_not_gt hdk
    have hkOne : k = 1 := by omega
    have hdOne : d = 1 := by omega
    subst k
    let oneColor : G.E → Fin 1 := fun _ ↦ 0
    have hproperOne : G.IsProperOn C oneColor := by
      intro v e he f hf _hsame
      have hcard : (C.filter (G.Inc v)).card ≤ 1 := by
        simpa [WeightedMultigraph.degreeOn, hdOne] using hdegreeC v
      apply Finset.card_le_one.mp hcard
      · exact Finset.mem_coe.mp he
      · exact Finset.mem_coe.mp hf
    exact hcritical.1 ⟨oneColor, hproperOne⟩

end WeightedEdgeColoring
