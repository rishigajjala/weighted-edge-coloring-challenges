import WeightedEdgeColoring.SubtwoMixedGraphSelectedNormalization
import WeightedEdgeColoring.MultigraphTinyEdgeResidualRounding

/-!
# Round the selected mixed tiny options

The selected mixed distribution is first clipped on each physical edge.
Tiny edges have no large-slot option, so their tiny colours and private
residual form a complete distribution.  The two-constraint rounding theorem
then makes one decision per tiny edge while preserving positive endpoint
labels and bounding each physical reservoir load.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Label : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

def selectedMixedTinyEdges : Finset G.E :=
  Finset.univ.filter fun e ↦ G.weight e < β

@[simp] theorem mem_selectedMixedTinyEdges {e : G.E} :
    e ∈ G.selectedMixedTinyEdges (β := β) ↔ G.weight e < β := by
  simp [selectedMixedTinyEdges]

theorem selectedMixedNormalizedTinyOptionMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) :
    0 ≤ G.selectedMixedNormalizedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c := by
  unfold selectedMixedNormalizedTinyOptionMass
  exact div_nonneg
    (G.selectedMixedTinyOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e c)
    (G.selectedMixedNormalizationDenominator_pos
      proposal edgeLabel qLaw R rho omega choice e).le

theorem selectedMixedLargeOptionMass_eq_zero_of_tiny
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r))
    (htiny : G.weight e < β) :
    G.selectedMixedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j = 0 := by
  unfold selectedMixedLargeOptionMass mixedGraphLargeProductMass pairedOption
    mixedGraphLargeEdgeMass
  simp [not_le.mpr htiny]

theorem selectedMixedNormalizedLargeOptionMass_eq_zero_of_tiny
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r))
    (htiny : G.weight e < β) :
    G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j = 0 := by
  unfold selectedMixedNormalizedLargeOptionMass
  rw [G.selectedMixedLargeOptionMass_eq_zero_of_tiny
    proposal edgeLabel qLaw R rho omega choice e c i j htiny]
  exact zero_div _

theorem sum_selectedMixedNormalizedTiny_add_residual_of_tiny
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (htiny : G.weight e < β) :
    (∑ c : Color, G.selectedMixedNormalizedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c) +
      G.selectedMixedResidualOptionMass
        proposal edgeLabel qLaw R rho omega choice e = 1 := by
  have h := G.sum_selectedMixedNormalizedOptionMass_add_residual
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 choice e
  have hzero (c : Color) (i j : Fin (explicitLargeSlotBound β qstep r)) :
      G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j = 0 :=
    G.selectedMixedNormalizedLargeOptionMass_eq_zero_of_tiny
      proposal edgeLabel qLaw R rho omega choice e c i j htiny
  simpa [hzero] using h

/-- The fractional tiny load on the tiny-edge set is bounded by the
physical reservoir load of the same selected word. -/
theorem tinyResidualColorLoad_selectedMixed_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) :
    G.tinyResidualColorLoad (G.selectedMixedTinyEdges (β := β))
        (fun e (d : Fin (Fintype.card Color)) ↦
          G.selectedMixedNormalizedTinyOptionMass
            proposal edgeLabel qLaw R rho omega choice e.1
              ((Fintype.equivFin Color).symm d))
        v ((Fintype.equivFin Color) c) ≤
      G.selectedMixedNormalizedTinyReservoirLoad
        proposal edgeLabel qLaw R rho omega choice v c := by
  classical
  let T := G.selectedMixedTinyEdges (β := β)
  let f : G.E → ℝ := fun e ↦
    if G.Inc v e then
      G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e c * G.weight e
    else 0
  have hf0 : ∀ e, 0 ≤ f e := by
    intro e
    by_cases hinc : G.Inc v e
    · simp only [f, hinc, if_true]
      exact mul_nonneg
        (G.selectedMixedNormalizedTinyOptionMass_nonneg
          proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
          hleft homega0 homega1 hrho hproposal0 choice e c)
        (G.weight_nonneg e)
    · simp [f, hinc]
  calc
    G.tinyResidualColorLoad T
        (fun e (d : Fin (Fintype.card Color)) ↦
          G.selectedMixedNormalizedTinyOptionMass
            proposal edgeLabel qLaw R rho omega choice e.1
              ((Fintype.equivFin Color).symm d))
        v ((Fintype.equivFin Color) c) =
        ∑ e ∈ T, f e := by
      unfold tinyResidualColorLoad
      simp only [Equiv.symm_apply_apply]
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach T f
    _ ≤ ∑ e, f e := Finset.sum_le_univ_sum_of_nonneg hf0
    _ = G.selectedMixedNormalizedTinyReservoirLoad
        proposal edgeLabel qLaw R rho omega choice v c := by
      unfold selectedMixedNormalizedTinyReservoirLoad
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hinc : G.Inc v e
      · simp [f, hinc, mul_comm]
      · simp [f, hinc]

/-- A genuine colour-or-residual decision for every tiny edge.  Palette
indices use the canonical finite encoding; decoding an index gives the
physical colour and hence the labels at both endpoints. -/
theorem exists_selectedMixedTinyColorDecision
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R) :
    ∃ decision : {e : G.E // e ∈ G.selectedMixedTinyEdges (β := β)} →
        Option (Fin (Fintype.card Color)),
      (∀ e d, decision e = some d →
        0 < G.selectedMixedNormalizedTinyOptionMass
          proposal edgeLabel qLaw R rho omega choice e.1
            ((Fintype.equivFin Color).symm d) ∧
        G.decodeMixedGraphLabel proposal edgeLabel qLaw R
          (G.fst e.1) (choice (G.fst e.1))
            ((Fintype.equivFin Color).symm d) =
          some (edgeLabel (G.fst e.1) (G.fstStarEdge e.1)) ∧
        G.decodeMixedGraphLabel proposal edgeLabel qLaw R
          (G.snd e.1) (choice (G.snd e.1))
            ((Fintype.equivFin Color).symm d) =
          some (edgeLabel (G.snd e.1) (G.sndStarEdge e.1))) ∧
      (∀ e, decision e = none →
        0 < G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega choice e.1) ∧
      (∀ v c,
        G.tinyResidualIntegralColorLoad decision v
            ((Fintype.equivFin Color) c) ≤
          G.selectedMixedNormalizedTinyReservoirLoad
            proposal edgeLabel qLaw R rho omega choice v c + 2 * β) ∧
      ∀ v,
        G.tinyResidualIntegralLossLoad decision v ≤
          G.tinyResidualLossLoad (G.selectedMixedTinyEdges (β := β))
            (fun e ↦ G.selectedMixedResidualOptionMass
              proposal edgeLabel qLaw R rho omega choice e.1) v + 2 * β := by
  classical
  let T := G.selectedMixedTinyEdges (β := β)
  let enc := Fintype.equivFin Color
  let x : {e : G.E // e ∈ T} → Fin (Fintype.card Color) → ℝ :=
    fun e d ↦ G.selectedMixedNormalizedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e.1 (enc.symm d)
  let residual : {e : G.E // e ∈ T} → ℝ :=
    fun e ↦ G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice e.1
  have hx0 : ∀ e d, 0 ≤ x e d := by
    intro e d
    exact G.selectedMixedNormalizedTinyOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e.1 (enc.symm d)
  have hresidual0 : ∀ e, 0 ≤ residual e := by
    intro e
    exact G.selectedMixedResidualOptionMass_nonneg
      proposal edgeLabel qLaw R rho omega choice e.1
  have htotal : ∀ e, (∑ d, x e d) + residual e = 1 := by
    intro e
    have htiny : G.weight e.1 < β := by
      apply G.mem_selectedMixedTinyEdges.mp
      simpa only [T] using e.2
    have hsum : (∑ d, x e d) =
        ∑ c : Color, G.selectedMixedNormalizedTinyOptionMass
          proposal edgeLabel qLaw R rho omega choice e.1 c := by
      simpa [x, enc] using
        (Equiv.sum_comp (Fintype.equivFin Color).symm
          (fun c : Color ↦ G.selectedMixedNormalizedTinyOptionMass
            proposal edgeLabel qLaw R rho omega choice e.1 c))
    rw [hsum]
    exact G.sum_selectedMixedNormalizedTiny_add_residual_of_tiny
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e.1 htiny
  have hweight : ∀ e ∈ T, G.weight e ≤ β := by
    intro e he
    exact (G.mem_selectedMixedTinyEdges.mp he).le
  obtain ⟨decision, hpositive, hresidual, hcolor, hloss⟩ :=
    G.exists_tinyColorDecision T β hβ x residual
      hx0 hresidual0 htotal hweight
  refine ⟨decision, ?_, ?_, ?_, hloss⟩
  · intro e d hed
    have hmass : 0 < G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e.1 (enc.symm d) := by
      simpa [x] using hpositive e d hed
    exact ⟨hmass, (G.positive_selectedMixedNormalizedTinyOptionMass_endpointLabels
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e.1 (enc.symm d)
      hmass).1,
      (G.positive_selectedMixedNormalizedTinyOptionMass_endpointLabels
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e.1 (enc.symm d)
      hmass).2⟩
  · intro e he
    simpa [residual] using hresidual e he
  · intro v c
    have h := hcolor v (enc c)
    have hbound := G.tinyResidualColorLoad_selectedMixed_le
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice v c
    calc
      G.tinyResidualIntegralColorLoad decision v (enc c) ≤
          G.tinyResidualColorLoad T x v (enc c) + 2 * β := h
      _ ≤ G.selectedMixedNormalizedTinyReservoirLoad
          proposal edgeLabel qLaw R rho omega choice v c + 2 * β := by
        simpa [x, enc, T] using add_le_add_right hbound (2 * β)

end WeightedMultigraph

end

end WeightedEdgeColoring
