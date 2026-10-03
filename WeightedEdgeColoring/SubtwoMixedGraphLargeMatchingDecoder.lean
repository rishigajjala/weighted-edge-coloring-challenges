import WeightedEdgeColoring.SubtwoMixedGraphConcreteDecoder
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeMatchingExtraction
import WeightedEdgeColoring.MultigraphExtendedProfileSelectedJointLoad

/-!
# Extract a physical large-edge matching from selected mixed options

The quantized job system uses the actual selected normalized edge array.
Every positive ordinary option fits the concrete local slot on both sides;
partial matching then gives a weighted partial colouring of physical edges.
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

def encodedSelectedMixedNormalizedLarge
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (d : Fin (Fintype.card Color))
    (i j : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice e
      ((Fintype.equivFin Color).symm d) i j

def encodedSelectedMixedConcreteSlotSize
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (d : Fin (Fintype.card Color))
    (i : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  G.selectedMixedConcreteSlotSize proposal edgeLabel qLaw R choice v
    ((Fintype.equivFin Color).symm d) i

/-- A partial matching of copied selected jobs gives a feasible physical
weighted colouring of its large ordinary edges. -/
theorem selectedMixedLargeMatching_isFeasibleOn
    (hColor : 0 < Fintype.card Color)
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
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.encodedSelectedMixedNormalizedLarge
          proposal edgeLabel qLaw R rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
        (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.encodedSelectedMixedNormalizedLarge
          proposal edgeLabel qLaw R rho omega choice))).IsPartialMatching M) :
    let O := G.selectedDyadicOrdinaryBaseOptions
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual
      (G.encodedSelectedMixedNormalizedLarge
        proposal edgeLabel qLaw R rho omega choice) M
    G.IsFeasibleOn (G.ordinarySelectedEdges O)
      (G.extendSelectedOrdinaryColor hColor O
        (G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
          (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
          bucket gamma reserve residual
          (G.encodedSelectedMixedNormalizedLarge
            proposal edgeLabel qLaw R rho omega choice) M hM)) := by
  let x := G.encodedSelectedMixedNormalizedLarge
    proposal edgeLabel qLaw R rho omega choice
  let slotSize := G.encodedSelectedMixedConcreteSlotSize
    proposal edgeLabel qLaw R choice
  have hslot0 : ∀ v d i, 0 ≤ slotSize v d i := by
    intro v d i
    exact G.selectedMixedConcreteSlotSize_nonneg
      proposal edgeLabel qLaw R choice v
        ((Fintype.equivFin Color).symm d) i
  have hsafe : ∀ v d, (∑ i, slotSize v d i) ≤ 1 := by
    intro v d
    exact G.sum_selectedMixedConcreteSlotSize_le_one
      proposal edgeLabel qLaw R choice v
        ((Fintype.equivFin Color).symm d)
  have hfitLeft : ∀ e d i j, 0 < x e d i j →
      G.weight e ≤ slotSize (G.fst e) d i := by
    intro e d i j hpos
    exact (G.weight_le_selectedMixedConcreteSlots_of_large_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e
      ((Fintype.equivFin Color).symm d) i j hpos).1
  have hfitRight : ∀ e d i j, 0 < x e d i j →
      G.weight e ≤ slotSize (G.snd e) d j := by
    intro e d i j hpos
    exact (G.weight_le_selectedMixedConcreteSlots_of_large_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e
      ((Fintype.equivFin Color).symm d) i j hpos).2
  exact G.dyadicLargeEdgeQuantizedMatching_isFeasibleOn
    hColor bucket gamma reserve residual x M hM
    slotSize hslot0 hsafe hfitLeft hfitRight

/-- The integral large-edge load occupies at most the sum of the concrete
slots in the selected local state. -/
theorem selectedMixedLargeMatching_load_le_concreteSlotSum
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
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.encodedSelectedMixedNormalizedLarge
          proposal edgeLabel qLaw R rho omega choice))))
    (hM : ((G.dyadicLargeEdgeOptionSystem
        (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.encodedSelectedMixedNormalizedLarge
          proposal edgeLabel qLaw R rho omega choice))).IsPartialMatching M)
    (v : G.V) (d : Fin (Fintype.card Color)) :
    let x := G.encodedSelectedMixedNormalizedLarge
      proposal edgeLabel qLaw R rho omega choice
    let O := G.selectedDyadicOrdinaryBaseOptions
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual x M
    let hO := G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual x M hM
    G.selectedOrdinaryIntegralColorLoad O hO v d ≤
      ∑ i, G.encodedSelectedMixedConcreteSlotSize
        proposal edgeLabel qLaw R choice v d i := by
  dsimp only
  apply G.selectedOrdinaryIntegralColorLoad_le_slotSum
    (G.selectedDyadicOrdinaryBaseOptions_isPartialMatching
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual
      (G.encodedSelectedMixedNormalizedLarge
        proposal edgeLabel qLaw R rho omega choice) M hM)
    (G.encodedSelectedMixedConcreteSlotSize
      proposal edgeLabel qLaw R choice)
  · intro v d i
    exact G.selectedMixedConcreteSlotSize_nonneg
      proposal edgeLabel qLaw R choice v
      ((Fintype.equivFin Color).symm d) i
  · intro o ho
    have hpos := G.selectedDyadicOrdinaryBaseOptions_mass_pos
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual
      (G.encodedSelectedMixedNormalizedLarge
        proposal edgeLabel qLaw R rho omega choice) M ho
    exact (G.weight_le_selectedMixedConcreteSlots_of_large_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice o.job
      ((Fintype.equivFin Color).symm o.color) o.leftPlace o.rightPlace
      hpos).1
  · intro o ho
    have hpos := G.selectedDyadicOrdinaryBaseOptions_mass_pos
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual
      (G.encodedSelectedMixedNormalizedLarge
        proposal edgeLabel qLaw R rho omega choice) M ho
    exact (G.weight_le_selectedMixedConcreteSlots_of_large_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice o.job
      ((Fintype.equivFin Color).symm o.color) o.leftPlace o.rightPlace
      hpos).2

theorem selectedMixedLargeMatching_disjoint_tinyEdges
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.encodedSelectedMixedNormalizedLarge
          proposal edgeLabel qLaw R rho omega choice)))) :
    let O := G.selectedDyadicOrdinaryBaseOptions
      (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
      bucket gamma reserve residual
      (G.encodedSelectedMixedNormalizedLarge
        proposal edgeLabel qLaw R rho omega choice) M
    Disjoint (G.ordinarySelectedEdges O)
      (G.selectedMixedTinyEdges (β := β)) := by
  dsimp only
  rw [Finset.disjoint_left]
  intro e heOrd heTiny
  rcases (G.mem_ordinarySelectedEdges_iff _ e).mp heOrd with ⟨o, ho, rfl⟩
  have hpos := G.selectedDyadicOrdinaryBaseOptions_mass_pos
    (Fintype.card Color) (explicitLargeSlotBound β qstep r) N
    bucket gamma reserve residual
    (G.encodedSelectedMixedNormalizedLarge
      proposal edgeLabel qLaw R rho omega choice) M ho
  have hzero := G.selectedMixedNormalizedLargeOptionMass_eq_zero_of_tiny
    proposal edgeLabel qLaw R rho omega choice o.job
    ((Fintype.equivFin Color).symm o.color) o.leftPlace o.rightPlace
    (G.mem_selectedMixedTinyEdges.mp heTiny)
  exact (ne_of_gt hpos) hzero

end WeightedMultigraph

end

end WeightedEdgeColoring
