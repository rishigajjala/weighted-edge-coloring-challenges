import WeightedEdgeColoring.SubtwoMixedGraphDyadicCodegreeBudget

/-! The mixed option support and quantization choices fit fixed dyadic budgets. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_dyadicSupportCaps
    {m n palette places : ℕ} {β extraGamma : ℝ}
    (hm : 1 ≤ m)
    (hβ : 0 < β) (hextraGamma : extraGamma < 1)
    (hnUpper : n ≤ 2 ^ 20 * m ^ 20)
    (hpalette : palette ≤ 4 * n) :
    let Ecoef := boundedMultiplicityDyadicSupportCoefficient β extraGamma
    let Ccoef := 4 * boundedMultiplicityDyadicChoiceCoefficient
      places β extraGamma
    let reserve := dyadicSimpleReserveScale m
    let E := Ecoef * m ^ 20
    let C := Ccoef * m ^ 20
    2 * ((n : ℝ) / β / (1 - extraGamma) + 1 + reserve) ≤ E ∧
      palette * places * places + E ≤ C := by
  let Ecoef := boundedMultiplicityDyadicSupportCoefficient β extraGamma
  let Ccoef := 4 * boundedMultiplicityDyadicChoiceCoefficient
    places β extraGamma
  let reserve := dyadicSimpleReserveScale m
  let E := Ecoef * m ^ 20
  let C := Ccoef * m ^ 20
  have hsupport :
      2 * ((n : ℝ) / β / (1 - extraGamma) + 1 + reserve) ≤ E := by
    simpa [E, reserve, Ecoef] using
      boundedMultiplicityDyadic_support_budget hm hβ hextraGamma hnUpper
  have hpaletteEnvelope : palette ≤ 4 * (2 ^ 20 * m ^ 20) :=
    hpalette.trans (Nat.mul_le_mul_left 4 hnUpper)
  have hchoice : palette * places * places + E ≤ C := by
    dsimp [C, Ccoef, E, Ecoef,
      boundedMultiplicityDyadicChoiceCoefficient]
    calc
      palette * places * places +
          boundedMultiplicityDyadicSupportCoefficient β extraGamma * m ^ 20 ≤
        (4 * (2 ^ 20 * m ^ 20)) * places * places +
          4 * boundedMultiplicityDyadicSupportCoefficient β extraGamma * m ^ 20 := by
        gcongr
        omega
      _ = (4 * (2 ^ 20 * places ^ 2 +
          boundedMultiplicityDyadicSupportCoefficient β extraGamma)) *
            m ^ 20 := by ring
  exact ⟨hsupport, hchoice⟩

end WeightedMultigraph

end

end WeightedEdgeColoring
