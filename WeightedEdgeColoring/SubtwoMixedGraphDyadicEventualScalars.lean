import WeightedEdgeColoring.SubtwoMixedGraphDyadicClosedScalars

/-! A graph-independent threshold for the explicit mixed masked-round scalars. -/

namespace WeightedEdgeColoring

open RankThreeOptionSystem.OriginalIterationState

noncomputable section

theorem mixedGraph_eventually_dyadicClosedScalars
    {β alpha gamma delta traceEps : ℝ} {A Ccoef L : ℕ}
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (hA : 0 < A)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (halphaDelta : alpha ≤ delta / 96)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaHalf : delta = 1 / 2)
    (htraceEps0 : 0 < traceEps) (htraceEps1 : traceEps ≤ 1) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      let m := dyadicSimpleRoot n
      let N := dyadicSimpleQuantizationScale m
      let C := Ccoef * m ^ 20
      let d0 := N - C
      let S0 := fixedSlackPaddedSlotTarget gamma d0
      let lambda := dyadicSimpleCodegreeScale A m
      let K := dyadicSimpleEndpointBlockScale 1 m
      let steps := variableSlackSteps alpha gamma traceEps lambda
      MixedMaskedClosedScalars β alpha gamma delta N C S0 lambda L K steps ∧
        (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^
          steps ≤ traceEps := by
  let T := variableSlackStepMultiplier alpha gamma traceEps
  let decayBudget : ℝ := 3 * alpha * gamma * T
  let cfrac : ℝ := Real.exp (-2 * decayBudget) / 4
  obtain ⟨M0, hM0⟩ := mixedGraph_dyadicEventualEnvelope
    (A := A) (Ccoef := Ccoef) (L := L) (scale := (0 : ℝ))
    hA halpha hgamma0 hdelta0 htraceEps0
  refine ⟨max 1 (M0 ^ 20), ?_⟩
  intro n hn
  let m := dyadicSimpleRoot n
  have hMpow : M0 ^ 20 ≤ n := (le_max_right 1 (M0 ^ 20)).trans hn
  have hmM : M0 ≤ m := le_dyadicSimpleRoot_of_pow_le hMpow
  rcases hM0 m hmM with
    ⟨hclosed, _hboundary, hloss, _hscale, hmarginGrowth, hfloorGrowth, hm⟩
  exact mixedGraph_dyadicClosedScalars_of_envelope
    (β := β) (alpha := alpha) (gamma := gamma) (delta := delta)
    (traceEps := traceEps) (cfrac := cfrac) (decayBudget := decayBudget)
    (A := A) (Ccoef := Ccoef) (L := L) (m := m)
    hdyadicCover hA hm halpha halphaSmall halphaDelta
    hgamma0 hgammaHalf hdelta0 hdelta1 hdeltaHalf
    htraceEps0 htraceEps1 rfl rfl hclosed hloss hmarginGrowth hfloorGrowth

end

end WeightedEdgeColoring
