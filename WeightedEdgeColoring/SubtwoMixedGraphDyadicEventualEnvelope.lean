import WeightedEdgeColoring.SubtwoMixedGraphDyadicSupportBudget
import WeightedEdgeColoring.VariableSlackGeometricSteps
import WeightedEdgeColoring.VariableSlackIterationScalars

/-! Fixed dyadic coefficients eventually satisfy every polynomial round envelope. -/

namespace WeightedEdgeColoring

noncomputable section

theorem mixedGraph_dyadicEventualEnvelope
    {A Ccoef L : ℕ} {scale alpha gamma delta traceEps : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha)
    (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (htraceEps : 0 < traceEps) :
    let T := variableSlackStepMultiplier alpha gamma traceEps
    let decayBudget := 3 * alpha * gamma * T
    let cfrac := Real.exp (-2 * decayBudget) / 4
    ∃ M0 : ℕ, ∀ m : ℕ, M0 ≤ m →
      (∀ d lambda : ℕ, 0 < d → 0 < lambda →
        cfrac * dyadicSimpleQuantizationScale m ≤ d →
        d ≤ (m + 1) ^ 30 →
        lambda ≤ dyadicSimpleCodegreeScale A m →
        DyadicSimpleClosedRoundScales 1 m d lambda alpha gamma delta) ∧
      (dyadicSimpleEndpointBlockScale (L + 1) m : ℝ) ≤
        traceEps * dyadicSimplePaletteScale m ∧
      (Ccoef : ℝ) + 1 ≤ gamma * m ∧
      scale ≤ (m : ℝ) ∧
      4 * (1 - gamma) * A ≤
        alpha * gamma ^ 2 * cfrac * m ∧
      T * A ≤ Real.exp (-2 * decayBudget) / 4 * m ∧
      2 ≤ m := by
  let T := variableSlackStepMultiplier alpha gamma traceEps
  let decayBudget : ℝ := 3 * alpha * gamma * T
  let cfrac : ℝ := Real.exp (-2 * decayBudget) / 4
  have hcfrac : 0 < cfrac := by dsimp [cfrac]; positivity
  have hclosedEventually := eventually_dyadicSimple_closedRoundScales
    A 1 alpha gamma delta cfrac hA (by norm_num) halpha
      hgamma hdelta hcfrac
  have hboundaryEventually :=
    eventually_dyadicSimple_fixedEndpointBlock_sublinear
      (L + 1) traceEps htraceEps
  have hlossEventually := eventually_const_le_pos_mul_nat
    ((Ccoef : ℝ) + 1) gamma hgamma
  have hscaleEventually := eventually_const_le_pos_mul_nat scale 1 (by norm_num)
  have hmarginEventually := eventually_const_le_pos_mul_nat
    (4 * (1 - gamma) * A)
      (alpha * gamma ^ 2 * cfrac) (by positivity)
  have hfloorEventually := eventually_const_le_pos_mul_nat
    (T * A) (Real.exp (-2 * decayBudget) / 4) (by positivity)
  have hrootEventually : ∀ᶠ m : ℕ in Filter.atTop, 2 ≤ m :=
    Filter.eventually_ge_atTop 2
  have hall : ∀ᶠ m : ℕ in Filter.atTop,
      (∀ d lambda : ℕ, 0 < d → 0 < lambda →
        cfrac * dyadicSimpleQuantizationScale m ≤ d →
        d ≤ (m + 1) ^ 30 →
        lambda ≤ dyadicSimpleCodegreeScale A m →
        DyadicSimpleClosedRoundScales 1 m d lambda alpha gamma delta) ∧
      (dyadicSimpleEndpointBlockScale (L + 1) m : ℝ) ≤
        traceEps * dyadicSimplePaletteScale m ∧
      (Ccoef : ℝ) + 1 ≤ gamma * m ∧
      scale ≤ (m : ℝ) ∧
      4 * (1 - gamma) * A ≤
        alpha * gamma ^ 2 * cfrac * m ∧
      T * A ≤ Real.exp (-2 * decayBudget) / 4 * m ∧
      2 ≤ m := by
    filter_upwards [hclosedEventually, hboundaryEventually, hlossEventually,
      hscaleEventually, hmarginEventually, hfloorEventually,
      hrootEventually] with m hclosed hboundary hloss hscale hmargin hfloor hm
    exact ⟨hclosed, hboundary, hloss, (by simpa using hscale), hmargin,
      hfloor, hm⟩
  rcases Filter.eventually_atTop.1 hall with ⟨M0, hM0⟩
  exact ⟨M0, hM0⟩

end

end WeightedEdgeColoring
