import WeightedEdgeColoring.ExtendedProfileSelectedNormalizedOptions
import WeightedEdgeColoring.TinyEdgeResidualRounding

/-!
# Rounding the selected normalized tiny options

This file instantiates the generic coloured-or-uncoloured two-constraint
rounding theorem with the normalized tiny option masses obtained from the
selected extended profiles.  Every edge below `beta` receives either a
palette colour or its private uncoloured option.  The integral load in an
endpoint--colour row is bounded by the selected normalized reservoir load,
up to the additive `2 * beta` rounding error.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- The graph edges handled by the tiny-edge rounding step. -/
def selectedBlockTinyEdges (β : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦ G.weight e < β

@[simp] theorem mem_selectedBlockTinyEdges {e : G.E} :
    e ∈ G.selectedBlockTinyEdges β ↔ G.weight e < β := by
  simp [selectedBlockTinyEdges]

/-- Restricting the normalized tiny array to the tiny edges cannot increase
an endpoint--colour load. -/
theorem tinyResidualColorLoad_selectedBlockNormalizedTiny_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (c : Fin (B * k)) :
    G.tinyResidualColorLoad (G.selectedBlockTinyEdges β)
        (fun e c' ↦ G.selectedBlockNormalizedTinyOptionMass
          R0 rho omega choice e.1 c') v c ≤
      G.selectedBlockNormalizedTinyReservoirLoad
        R0 rho omega choice (v, c) := by
  classical
  let R := G.selectedBlockTinyEdges β
  let f : G.E → ℝ := fun e ↦
    if G.Inc v e then
      G.selectedBlockNormalizedTinyOptionMass
        R0 rho omega choice e c * G.weight e
    else 0
  have hf0 : ∀ e, 0 ≤ f e := by
    intro e
    by_cases hinc : G.Inc v e
    · simp only [f, hinc, if_true]
      exact mul_nonneg
        (G.selectedBlockNormalizedTinyOptionMass_nonneg R0 hn hs hq hr0
          hleft homega0 homega1 hrho choice e c)
        (G.weight_nonneg e)
    · simp [f, hinc]
  calc
    G.tinyResidualColorLoad R
        (fun e c' ↦ G.selectedBlockNormalizedTinyOptionMass
          R0 rho omega choice e.1 c') v c =
        ∑ e ∈ R, f e := by
      unfold tinyResidualColorLoad
      rw [Finset.sum_subtype (p := fun e : G.E ↦ e ∈ R) R
        (by intro e; simp)]
    _ ≤ ∑ e, f e :=
      Finset.sum_le_univ_sum_of_nonneg hf0
    _ = G.selectedBlockNormalizedTinyReservoirLoad
        R0 rho omega choice (v, c) := by
      unfold selectedBlockNormalizedTinyReservoirLoad
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e
      · simp [f, hinc, mul_comm]
      · simp [f, hinc]

/-- Round every selected normalized tiny-edge distribution to an explicit
colour-or-uncoloured decision.  A selected colour retains positive
normalized mass and therefore has a positive concrete reservoir at both
endpoints. -/
theorem exists_selectedBlockTinyColorDecision
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r) :
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (∀ e c, decision e = some c →
        0 < G.selectedBlockNormalizedTinyOptionMass
            R0 rho omega choice e.1 c ∧
          0 < G.extendedProfileReservoirSize R0 (G.fst e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.fst e.1) c) ∧
          0 < G.extendedProfileReservoirSize R0 (G.snd e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.snd e.1) c)) ∧
      (∀ e, decision e = none →
        0 < G.selectedBlockResidualOptionMass
          R0 rho omega choice e.1) ∧
      (∀ v c,
        G.tinyResidualIntegralColorLoad decision v c ≤
          G.selectedBlockNormalizedTinyReservoirLoad
            R0 rho omega choice (v, c) + 2 * β) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass
              R0 rho omega choice e.1) v + 2 * β := by
  let R := G.selectedBlockTinyEdges β
  let x : {e : G.E // e ∈ R} → Fin (B * k) → ℝ :=
    fun e c ↦ G.selectedBlockNormalizedTinyOptionMass
      R0 rho omega choice e.1 c
  let residual : {e : G.E // e ∈ R} → ℝ :=
    fun e ↦ G.selectedBlockResidualOptionMass
      R0 rho omega choice e.1
  have hx0 : ∀ e c, 0 ≤ x e c := by
    intro e c
    exact G.selectedBlockNormalizedTinyOptionMass_nonneg R0
      hn hs hq hr0 hleft homega0 homega1 hrho choice e.1 c
  have hresidual0 : ∀ e, 0 ≤ residual e := by
    intro e
    exact G.selectedBlockResidualOptionMass_nonneg R0
      rho omega choice e.1
  have htotal : ∀ e, (∑ c, x e c) + residual e = 1 := by
    intro e
    have htiny : G.weight e.1 < β := by
      apply G.mem_selectedBlockTinyEdges.mp
      simpa only [R] using e.2
    simpa [x, residual] using
      (G.sum_selectedBlockNormalizedTiny_add_residual_of_tiny R0
        hn hs hq hr0 hleft homega0 homega1 hrho choice e.1 htiny)
  have hweight : ∀ e ∈ R, G.weight e ≤ β := by
    intro e he
    exact (G.mem_selectedBlockTinyEdges.mp he).le
  obtain ⟨decision, hpositive, hresidual, hcolor, hloss⟩ :=
    G.exists_tinyColorDecision R β hβ x residual
      hx0 hresidual0 htotal hweight
  have hresidual' : ∀ e, decision e = none →
      0 < G.selectedBlockResidualOptionMass
        R0 rho omega choice e.1 := by
    intro e he
    simpa [residual] using hresidual e he
  refine ⟨decision, ?_, hresidual', ?_, hloss⟩
  · intro e c hec
    have hmass : 0 < G.selectedBlockNormalizedTinyOptionMass
        R0 rho omega choice e.1 c := by
      simpa [x] using hpositive e c hec
    have hfit := G.selectedBlockNormalizedTinyOptionMass_pos_fit R0
      hn hs hq hr0 hleft homega0 homega1 hrho choice e.1 c hmass
    exact ⟨hmass, hfit.1.2, hfit.2.2⟩
  intro v c
  calc
    G.tinyResidualIntegralColorLoad decision v c ≤
        G.tinyResidualColorLoad R x v c + 2 * β := hcolor v c
    _ ≤ G.selectedBlockNormalizedTinyReservoirLoad
          R0 rho omega choice (v, c) + 2 * β := by
      apply add_le_add_left
      exact G.tinyResidualColorLoad_selectedBlockNormalizedTiny_le R0
        hn hs hq hr0 hleft rho omega homega0 homega1 hrho choice v c

/-- The same integral tiny-edge choice is controlled by the unnormalized
selected reservoir load, which is often the form supplied directly by the
packing selector. -/
theorem exists_selectedBlockTinyColorDecision_raw_bound
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (rho omega : ℝ)
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r) :
    ∃ decision : {e : G.E // e ∈ G.selectedBlockTinyEdges β} →
        Option (Fin (B * k)),
      (∀ e c, decision e = some c →
        0 < G.selectedBlockNormalizedTinyOptionMass
            R0 rho omega choice e.1 c ∧
          0 < G.extendedProfileReservoirSize R0 (G.fst e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.fst e.1) c) ∧
          0 < G.extendedProfileReservoirSize R0 (G.snd e.1)
            (G.decodedExtendedProfileBlockSelection
              R0 choice (G.snd e.1) c)) ∧
      (∀ e, decision e = none →
        0 < G.selectedBlockResidualOptionMass
          R0 rho omega choice e.1) ∧
      (∀ v c,
        G.tinyResidualIntegralColorLoad decision v c ≤
          G.selectedBlockTinyReservoirLoad
            R0 rho omega choice (v, c) + 2 * β) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
            (fun e ↦ G.selectedBlockResidualOptionMass
              R0 rho omega choice e.1) v + 2 * β := by
  obtain ⟨decision, hpositive, hresidual, hcolor, hloss⟩ :=
    G.exists_selectedBlockTinyColorDecision R0
      hn hs hq hr0 hleft rho omega homega0 homega1 hrho choice
  refine ⟨decision, hpositive, hresidual, ?_, hloss⟩
  intro v c
  exact (hcolor v c).trans (add_le_add_left
    (G.selectedBlockNormalizedTinyReservoirLoad_le R0
      hn hs hq hr0 hleft homega0 homega1 hrho choice (v, c)) _)

end WeightedSimpleGraph

end

end WeightedEdgeColoring
