import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileSelectedCapacityDecoder
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileSelectedNormalizedOptions

/-!
# From selected candidate capacities to clipped option loads

This module identifies the additive candidate loads with the actual
large-slot and tiny-reservoir loads of the selected equation-(23) array.
Edgewise clipping can only decrease either load.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- The actual raw load of a selected large slot. -/
def selectedColorDependentLargeSlotLoad
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  let choice := G.encodedColorDependentSelectedBlock proposal R selected
  ∑ e : G.E,
    ((if v = G.fst e then
        ∑ j, G.selectedColorDependentLargeOptionMass
          proposal R rho omega choice e c slot j else 0) +
      (if v = G.snd e then
        ∑ i, G.selectedColorDependentLargeOptionMass
          proposal R rho omega choice e c i slot else 0))

/-- The actual clipped load of a selected large slot. -/
def selectedColorDependentNormalizedLargeSlotLoad
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  let choice := G.encodedColorDependentSelectedBlock proposal R selected
  ∑ e : G.E,
    ((if v = G.fst e then
        ∑ j, G.selectedColorDependentNormalizedLargeOptionMass
          proposal R rho omega choice e c slot j else 0) +
      (if v = G.snd e then
        ∑ i, G.selectedColorDependentNormalizedLargeOptionMass
          proposal R rho omega choice e c i slot else 0))

/-- The actual weighted raw load sent to one selected tiny reservoir. -/
def selectedColorDependentTinyReservoirLoad
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) : ℝ :=
  let choice := G.encodedColorDependentSelectedBlock proposal R selected
  ∑ e : G.E, if G.Inc v e then
    G.weight e * G.selectedColorDependentTinyOptionMass
      proposal R rho omega choice e c else 0

/-- The weighted tiny-reservoir load after edgewise clipping. -/
def selectedColorDependentNormalizedTinyReservoirLoad
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) : ℝ :=
  let choice := G.encodedColorDependentSelectedBlock proposal R selected
  ∑ e : G.E, if G.Inc v e then
    G.weight e * G.selectedColorDependentNormalizedTinyOptionMass
      proposal R rho omega choice e c else 0

/-- Candidate transposition is exact for large slots. -/
theorem selectedColorDependentLargeCapacityLoad_eq_slotLoad
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) :
    G.selectedColorDependentLargeCapacityLoad
        proposal R rho omega selected v c slot =
      G.selectedColorDependentLargeSlotLoad
        proposal R rho omega selected v c slot := by
  classical
  unfold selectedColorDependentLargeCapacityLoad
    colorDependentCandidateAtomUse selectedColorDependentLargeSlotLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hfst : v = G.fst e
  · have hsnd : v ≠ G.snd e := by
      intro h
      exact G.noLoop e (hfst.symm.trans h)
    subst v
    have hne : G.fst e ≠ G.snd e := G.noLoop e
    simp [selectedColorDependentLargeCandidateRow,
      colorDependentLargeCandidateEdgeUse,
      selectedColorDependentLargeOptionMass,
      G.decode_encodedColorDependentSelectedBlock, hne, hsnd]
  · by_cases hsnd : v = G.snd e
    · subst v
      have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
      simp [selectedColorDependentLargeCandidateRow,
        colorDependentLargeCandidateEdgeUse,
        selectedColorDependentLargeOptionMass,
        G.decode_encodedColorDependentSelectedBlock, hne, hfst]
    · have hfst' : G.fst e ≠ v := Ne.symm hfst
      have hsnd' : G.snd e ≠ v := Ne.symm hsnd
      simp [selectedColorDependentLargeCandidateRow,
        colorDependentLargeCandidateEdgeUse,
        selectedColorDependentLargeOptionMass,
        G.decode_encodedColorDependentSelectedBlock,
        hfst, hsnd, hfst', hsnd']

/-- Candidate transposition is exact for weighted tiny reservoirs. -/
theorem selectedColorDependentTinyCapacityLoad_eq_reservoirLoad
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) :
    G.selectedColorDependentTinyCapacityLoad
        proposal R rho omega selected v c =
      G.selectedColorDependentTinyReservoirLoad
        proposal R rho omega selected v c := by
  classical
  unfold selectedColorDependentTinyCapacityLoad
    colorDependentCandidateAtomUse selectedColorDependentTinyReservoirLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hfst : v = G.fst e
  · have hsnd : v ≠ G.snd e := by
      intro h
      exact G.noLoop e (hfst.symm.trans h)
    subst v
    have hne : G.fst e ≠ G.snd e := G.noLoop e
    simp [selectedColorDependentTinyCandidateRow,
      colorDependentTinyCandidateEdgeUse,
      selectedColorDependentTinyOptionMass,
      G.decode_encodedColorDependentSelectedBlock,
      WeightedMultigraph.Inc, hne, hsnd]
  · by_cases hsnd : v = G.snd e
    · subst v
      have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
      simp [selectedColorDependentTinyCandidateRow,
        colorDependentTinyCandidateEdgeUse,
        selectedColorDependentTinyOptionMass,
        G.decode_encodedColorDependentSelectedBlock,
        WeightedMultigraph.Inc, hne, hfst]
    · have hfst' : G.fst e ≠ v := Ne.symm hfst
      have hsnd' : G.snd e ≠ v := Ne.symm hsnd
      simp [selectedColorDependentTinyCandidateRow,
        colorDependentTinyCandidateEdgeUse,
        selectedColorDependentTinyOptionMass,
        G.decode_encodedColorDependentSelectedBlock,
        WeightedMultigraph.Inc, hfst, hsnd, hfst', hsnd']

/-- Clipping decreases every selected large-slot load. -/
theorem selectedColorDependentNormalizedLargeSlotLoad_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r)) :
    G.selectedColorDependentNormalizedLargeSlotLoad
        proposal R rho omega selected v c slot ≤
      G.selectedColorDependentLargeSlotLoad
        proposal R rho omega selected v c slot := by
  unfold selectedColorDependentNormalizedLargeSlotLoad
    selectedColorDependentLargeSlotLoad
  apply Finset.sum_le_sum
  intro e _he
  apply add_le_add
  · by_cases hfst : v = G.fst e
    · simp only [hfst, if_true]
      exact Finset.sum_le_sum fun j _hj ↦
        G.selectedColorDependentNormalizedLargeOptionMass_le proposal R
          hs hq hr0 hleft homega0 homega1 hrho
          (G.encodedColorDependentSelectedBlock proposal R selected) e c slot j
    · simp [hfst]
  · by_cases hsnd : v = G.snd e
    · simp only [hsnd, if_true]
      exact Finset.sum_le_sum fun i _hi ↦
        G.selectedColorDependentNormalizedLargeOptionMass_le proposal R
          hs hq hr0 hleft homega0 homega1 hrho
          (G.encodedColorDependentSelectedBlock proposal R selected) e c i slot
    · simp [hsnd]

/-- Clipping decreases every selected weighted reservoir load. -/
theorem selectedColorDependentNormalizedTinyReservoirLoad_le
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k) :
    G.selectedColorDependentNormalizedTinyReservoirLoad
        proposal R rho omega selected v c ≤
      G.selectedColorDependentTinyReservoirLoad
        proposal R rho omega selected v c := by
  unfold selectedColorDependentNormalizedTinyReservoirLoad
    selectedColorDependentTinyReservoirLoad
  apply Finset.sum_le_sum
  intro e _he
  by_cases hinc : G.Inc v e
  · simp only [hinc, if_true]
    exact mul_le_mul_of_nonneg_left
      (G.selectedColorDependentNormalizedTinyOptionMass_le proposal R
        hs hq hr0 hleft homega0 homega1 hrho
        (G.encodedColorDependentSelectedBlock proposal R selected) e c)
      (G.weight_nonneg e)
  · simp [hinc]

/-- Capacity selection therefore bounds the clipped large-slot load. -/
theorem selectedColorDependentNormalizedLargeSlotLoad_lt
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (scale deviation : ℝ) (hscale : 0 < scale)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (slot : Fin (explicitLargeSlotBound β q r))
    (hrow :
      FiniteCategoricalSelection.rowLoad
        (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
        (G.selectedColorDependentLargeCapacityRow proposal R selected v c slot)
        (G.encodedColorDependentSelectedBlock proposal R selected) <
      (n : ℝ) * (rho / (1 - omega)) / scale + deviation) :
    G.selectedColorDependentNormalizedLargeSlotLoad
        proposal R rho omega selected v c slot <
      rho / (1 - omega) + scale / n * deviation := by
  exact (G.selectedColorDependentNormalizedLargeSlotLoad_le proposal R
    hs hq hr0 hleft homega0 homega1 hrho selected v c slot).trans_lt
      ((G.selectedColorDependentLargeCapacityLoad_eq_slotLoad
        proposal R rho omega selected v c slot) ▸
        G.selectedColorDependentLargeCapacityLoad_lt proposal R hn scale rho
          omega deviation hscale selected v c slot hrow)

/-- Capacity selection bounds the clipped tiny load by the reservoir size
of the selected state, with the same vanishing additive error. -/
theorem selectedColorDependentNormalizedTinyReservoirLoad_lt
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (scale deviation : ℝ) (hscale : 0 < scale)
    (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin B × Fin k)
    (hrow :
      FiniteCategoricalSelection.rowLoad
        (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
        (G.selectedColorDependentTinyCapacityRow proposal R selected v c)
        (G.encodedColorDependentSelectedBlock proposal R selected) <
      (n : ℝ) *
          (rho * G.colorDependentExtendedProfileReservoirSize
            R v c (selected v c.1 c.2) / (1 - omega)) / scale + deviation) :
    G.selectedColorDependentNormalizedTinyReservoirLoad
        proposal R rho omega selected v c <
      rho * G.colorDependentExtendedProfileReservoirSize
          R v c (selected v c.1 c.2) / (1 - omega) +
        scale / n * deviation := by
  exact (G.selectedColorDependentNormalizedTinyReservoirLoad_le proposal R
    hs hq hr0 hleft homega0 homega1 hrho selected v c).trans_lt
      ((G.selectedColorDependentTinyCapacityLoad_eq_reservoirLoad
        proposal R rho omega selected v c) ▸
        G.selectedColorDependentTinyCapacityLoad_lt proposal R hn scale rho
          omega deviation hscale selected v c hrow)

end WeightedMultigraph

end

end WeightedEdgeColoring
