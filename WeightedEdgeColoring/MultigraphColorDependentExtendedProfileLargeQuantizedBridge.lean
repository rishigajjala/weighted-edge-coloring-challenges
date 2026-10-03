import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileSelectedCapacityOptionBridge
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockVarianceBounds
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileStateSafety
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeOptionBounds
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeMatchingExtraction
import WeightedEdgeColoring.MultigraphOrdinaryMatchingExtraction
import WeightedEdgeColoring.MultigraphExtendedProfileSelectedJointLoad

/-!
# Quantized large-option bounds for color-dependent selected profiles

This file flattens the product palette selected in fixed color blocks and
proves the ordinary slot and codegree estimates needed by the existing
rank-three large-edge iteration.  The factor two in the pointwise envelope
comes from the unconditional coordinate option-mass estimate.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k n N reserve : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- Selected normalized ordinary masses, expressed on the flattened palette. -/
def flattenedSelectedColorDependentNormalizedLarge
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) : ℝ :=
  G.selectedColorDependentNormalizedLargeOptionMass proposal R rho omega
    (G.encodedColorDependentSelectedBlock proposal R selected) e
    (finProdFinEquiv.symm c) i j

theorem flattenedSelectedColorDependentNormalizedLarge_nonneg
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (selected : G.ColorDependentSelectedStates proposal R) :
    ∀ e c i j, 0 ≤
      G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected e c i j := by
  intro e c i j
  exact G.selectedColorDependentNormalizedLargeOptionMass_nonneg proposal R
    hs hq hr0 hleft homega0 homega1 hrho
    (G.encodedColorDependentSelectedBlock proposal R selected) e
    (finProdFinEquiv.symm c) i j

/-- One flattened color's complete ordinary mass has the diffuse
`2*scale/n` envelope. -/
theorem flattenedSelectedColorDependentNormalizedLarge_colorMass_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (selected : G.ColorDependentSelectedStates proposal R)
    (e : G.E) (c : Fin (B * k)) :
    ∑ i, ∑ j,
        G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected e c i j ≤
      2 * colorDependentCandidateCapacityScale
        rho s omega β q r C0 / n := by
  let choice := G.encodedColorDependentSelectedBlock proposal R selected
  let d := finProdFinEquiv.symm c
  let P := G.decodeColorDependentExtendedProfileBlock proposal R
    (G.fst e, d.1) (choice (G.fst e, d.1)) d.2
  let Q := G.decodeColorDependentExtendedProfileBlock proposal R
    (G.snd e, d.1) (choice (G.snd e, d.1)) d.2
  have hlarge :
      (∑ i, ∑ j, G.selectedColorDependentLargeOptionMass
        proposal R rho omega choice e d i j) ≤
        G.colorDependentCoordinateOptionMass proposal R rho omega e d P Q := by
    unfold colorDependentCoordinateOptionMass
    exact le_add_of_nonneg_right
      (G.colorDependentExtendedProfileTinyProductMass_nonneg proposal R
        hs hq hr0 hleft homega0 homega1 hrho e d P Q)
  have hnormalized :
      (∑ i, ∑ j,
        G.selectedColorDependentNormalizedLargeOptionMass
          proposal R rho omega choice e d i j) ≤
      ∑ i, ∑ j, G.selectedColorDependentLargeOptionMass
          proposal R rho omega choice e d i j := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact G.selectedColorDependentNormalizedLargeOptionMass_le proposal R
      hs hq hr0 hleft homega0 homega1 hrho choice e d i j
  change (∑ i, ∑ j,
      G.selectedColorDependentNormalizedLargeOptionMass
        proposal R rho omega choice e d i j) ≤ _
  exact hnormalized.trans (hlarge.trans
    (G.colorDependentCoordinateOptionMass_le_two_scale_div_n proposal R
      hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal e d P Q))

/-- A pointwise ordinary option inherits the same envelope. -/
theorem flattenedSelectedColorDependentNormalizedLarge_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (selected : G.ColorDependentSelectedStates proposal R)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) :
    G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected e c i j ≤
      2 * colorDependentCandidateCapacityScale
        rho s omega β q r C0 / n := by
  have hsingle :
      G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected e c i j ≤
        ∑ i, ∑ j,
          G.flattenedSelectedColorDependentNormalizedLarge
            proposal R rho omega selected e c i j := by
    have hinner :
        G.flattenedSelectedColorDependentNormalizedLarge
            proposal R rho omega selected e c i j ≤
          ∑ j,
            G.flattenedSelectedColorDependentNormalizedLarge
              proposal R rho omega selected e c i j :=
      Finset.single_le_sum
        (fun j _ ↦ G.flattenedSelectedColorDependentNormalizedLarge_nonneg
          proposal R hs hq hr0 hleft homega0 homega1 hrho selected e c i j)
        (Finset.mem_univ j)
    have houter :
        (∑ j,
            G.flattenedSelectedColorDependentNormalizedLarge
              proposal R rho omega selected e c i j) ≤
          ∑ i, ∑ j,
            G.flattenedSelectedColorDependentNormalizedLarge
              proposal R rho omega selected e c i j :=
      Finset.single_le_sum
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦
        G.flattenedSelectedColorDependentNormalizedLarge_nonneg proposal R
          hs hq hr0 hleft homega0 homega1 hrho selected e c i j)
        (Finset.mem_univ i)
    exact hinner.trans houter
  exact hsingle.trans
    (G.flattenedSelectedColorDependentNormalizedLarge_colorMass_le proposal R
      hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal selected e c)

/-- Generic ordinary slot load is exactly the product-color selected load. -/
theorem flattenedSelectedColorDependentNormalizedLarge_slotLoad_eq
    (rho omega : ℝ) (selected : G.ColorDependentSelectedStates proposal R)
    (v : G.V) (c : Fin (B * k))
    (slot : Fin (explicitLargeSlotBound β q r)) :
    (∑ e,
      ((if v = G.fst e then ∑ j,
          G.flattenedSelectedColorDependentNormalizedLarge
            proposal R rho omega selected e c slot j else 0) +
       if v = G.snd e then ∑ i,
          G.flattenedSelectedColorDependentNormalizedLarge
            proposal R rho omega selected e c i slot else 0)) =
      G.selectedColorDependentNormalizedLargeSlotLoad
        proposal R rho omega selected v (finProdFinEquiv.symm c) slot := by
  rfl

/-- Capacity-row control implies the copied ordinary slot-degree bound. -/
theorem colorDependent_quantizedOrdinarySlotDegree_lt
    (hn : 0 < n) (hN : 0 < N)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (scale deviation : ℝ) (hscale : 0 < scale)
    (selected : G.ColorDependentSelectedStates proposal R)
    (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (hrow : ∀ v c slot,
      FiniteCategoricalSelection.rowLoad
        (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
        (G.selectedColorDependentLargeCapacityRow proposal R selected v c slot)
        (G.encodedColorDependentSelectedBlock proposal R selected) <
      (n : ℝ) * (rho / (1 - omega)) / scale + deviation)
    (slot : OrdinarySlot G.V (Fin (B * k))
      (explicitLargeSlotBound β q r)) :
    ((((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve residual
        (G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected))).slotDegree (Sum.inl slot) : ℕ) : ℝ) <
      (N : ℝ) * (rho / (1 - omega) + scale / n * deviation) := by
  have hx0 := G.flattenedSelectedColorDependentNormalizedLarge_nonneg
    proposal R hs hq hr0 hleft homega0 homega1 hrho selected
  have hdegree := G.dyadicLargeEdge_quantized_slotDegree_inl_le
    (explicitLargeSlotBound β q r) bucket gamma reserve residual
    (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected) hx0 N slot
  rw [G.flattenedSelectedColorDependentNormalizedLarge_slotLoad_eq
    proposal R rho omega selected] at hdegree
  have hload := G.selectedColorDependentNormalizedLargeSlotLoad_lt proposal R
    hn hs hq hr0 hleft homega0 homega1 hrho scale deviation hscale selected
    slot.vertex (finProdFinEquiv.symm slot.color) slot.place
    (hrow slot.vertex (finProdFinEquiv.symm slot.color) slot.place)
  exact hdegree.trans_lt (mul_lt_mul_of_pos_left hload (by exact_mod_cast hN))

/-- Copied ordinary job-slot codegrees are `O(N/n)`. -/
theorem colorDependent_quantizedOrdinaryJobSlotCodegree_le
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (selected : G.ColorDependentSelectedStates proposal R)
    (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (e : G.E)
    (slot : OrdinarySlot G.V (Fin (B * k))
      (explicitLargeSlotBound β q r)) :
    (((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve residual
        (G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected))).jobSlotCodegree e (Sum.inl slot) : ℝ) ≤
      (N : ℝ) *
        (2 * colorDependentCandidateCapacityScale
          rho s omega β q r C0 / n) := by
  have hx0 := G.flattenedSelectedColorDependentNormalizedLarge_nonneg
    proposal R hs hq hr0 hleft homega0 homega1 hrho selected
  have hbase := G.dyadicLargeEdge_quantized_jobSlotCodegree_inl_le
    (explicitLargeSlotBound β q r) bucket gamma reserve residual
    (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected) hx0 N e slot
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (G.flattenedSelectedColorDependentNormalizedLarge_colorMass_le proposal R
      hn hs hq hr0 hleft homega0 homega1 rho C0 hrho hC0
      hproposal0 hproposal selected e slot.color) (by positivity))

/-- Extracting the ordinary summand preserves the concrete selected-slot
packing bound. -/
theorem colorDependentSelectedLargeMatching_load_le_concreteSlotSum
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve residual
        (G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
          reserve residual
          (G.flattenedSelectedColorDependentNormalizedLarge
            proposal R rho omega selected))).IsPartialMatching M)
    (v : G.V) (c : Fin B × Fin k) :
    let O := G.selectedDyadicOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      residual (G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected) M
    let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      residual (G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected) M hM
    G.selectedOrdinaryIntegralColorLoad O hO v (finProdFinEquiv c) ≤
      ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
        (selected v c.1 c.2) i := by
  dsimp only
  let O := G.selectedDyadicOrdinaryBaseOptions
    (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
    residual (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected) M
  let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      residual (G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected) M hM
  let slotSize := fun v d i ↦
    G.colorDependentExtendedProfileConcreteSlotSize R v
      (finProdFinEquiv.symm d)
      (selected v (finProdFinEquiv.symm d).1
        (finProdFinEquiv.symm d).2) i
  have hbound :
      G.selectedOrdinaryIntegralColorLoad O hO v (finProdFinEquiv c) ≤
        ∑ i, slotSize v (finProdFinEquiv c) i := by
    apply G.selectedOrdinaryIntegralColorLoad_le_slotSum hO slotSize
      (fun v d i ↦ G.colorDependentExtendedProfileConcreteSlotSize_nonneg
        R v (finProdFinEquiv.symm d) _ i)
    · intro o ho
      have hpos := G.selectedDyadicOrdinaryBaseOptions_mass_pos
        (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
        residual (G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected) M ho
      simpa [slotSize, flattenedSelectedColorDependentNormalizedLarge,
        finProdFinEquiv.symm_apply_apply] using
        (G.weight_le_colorDependentExtendedProfileConcreteSlotSize_fst_of_pos
          proposal R hs hq hr0 hleft rho omega homega0 homega1
          (G.encodedColorDependentSelectedBlock proposal R selected)
          o.job (finProdFinEquiv.symm o.color) o.leftPlace o.rightPlace hpos)
    · intro o ho
      have hpos := G.selectedDyadicOrdinaryBaseOptions_mass_pos
        (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
        residual (G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected) M ho
      simpa [slotSize, flattenedSelectedColorDependentNormalizedLarge,
        finProdFinEquiv.symm_apply_apply] using
        (G.weight_le_colorDependentExtendedProfileConcreteSlotSize_snd_of_pos
          proposal R hs hq hr0 hleft rho omega homega0 homega1
          (G.encodedColorDependentSelectedBlock proposal R selected)
          o.job (finProdFinEquiv.symm o.color) o.leftPlace o.rightPlace hpos)
  calc
    G.selectedOrdinaryIntegralColorLoad O hO v (finProdFinEquiv c) ≤
        ∑ i, slotSize v (finProdFinEquiv c) i := hbound
    _ = ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
          (selected v c.1 c.2) i := by
      unfold slotSize
      rw [show finProdFinEquiv.symm (finProdFinEquiv c) = c from
        finProdFinEquiv.symm_apply_apply c]

/-- Every ordinary edge extracted from positive selected mass uses positive
original proposal support. -/
theorem colorDependentSelectedLargeMatching_support
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hB : 0 < B) (hk : 0 < k)
    (rho omega : ℝ)
    (selected : G.ColorDependentSelectedStates proposal R)
    (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve residual
        (G.flattenedSelectedColorDependentNormalizedLarge
          proposal R rho omega selected))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
      bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
          reserve residual
          (G.flattenedSelectedColorDependentNormalizedLarge
            proposal R rho omega selected))).IsPartialMatching M) :
    let O := G.selectedDyadicOrdinaryBaseOptions
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      residual (G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected) M
    let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
      residual (G.flattenedSelectedColorDependentNormalizedLarge
        proposal R rho omega selected) M hM
    ∀ e ∈ G.ordinarySelectedEdges O,
      0 < proposal e (finProdFinEquiv.symm
        (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) O hO e)) := by
  dsimp only
  let O := G.selectedDyadicOrdinaryBaseOptions
    (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
    residual (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected) M
  let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
    (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
    residual (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected) M hM
  intro e he
  rcases (G.mem_ordinarySelectedEdges_iff _ e).mp he with ⟨o, ho, rfl⟩
  have hpos := G.selectedDyadicOrdinaryBaseOptions_mass_pos
    (B * k) (explicitLargeSlotBound β q r) N bucket gamma reserve
    residual (G.flattenedSelectedColorDependentNormalizedLarge
      proposal R rho omega selected) M ho
  have hp := G.proposal_pos_of_selectedColorDependentNormalizedLarge_pos
    proposal R hproposal0 rho omega
      (G.encodedColorDependentSelectedBlock proposal R selected)
      o.job (finProdFinEquiv.symm o.color) o.leftPlace o.rightPlace hpos
  have heO : o.job ∈ G.ordinarySelectedEdges O :=
    (G.mem_ordinarySelectedEdges_iff _ o.job).mpr ⟨o, ho, rfl⟩
  have hchosen : G.selectedOrdinaryOption O hO o.job heO = o := by
    apply hO.2
    · exact G.selectedOrdinaryOption_mem O hO o.job heO
    · exact ho
    · exact G.selectedOrdinaryOption_job O hO o.job heO
  have hcolor :
      G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) O hO o.job =
        o.color := by
    rw [G.extendSelectedOrdinaryColor_of_mem (Nat.mul_pos hB hk) O hO heO]
    change (G.selectedOrdinaryOption O hO o.job heO).color = o.color
    rw [hchosen]
  change 0 < proposal o.job (finProdFinEquiv.symm
    (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) O hO o.job))
  rw [hcolor]
  exact hp

end WeightedMultigraph

end

end WeightedEdgeColoring
