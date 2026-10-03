import WeightedEdgeColoring.SubtwoMixedGraphLargeResidual

/-!
# Degree bounds for the masked selected copied-job system
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

theorem selectedMixedMaskedLarge_slotDegree_le
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
    (bucket : G.E → Class) (gamma : ℝ) (reserve N S0 : ℕ)
    (hN : 0 < N)
    (bound : ℝ)
    (hcapacity : ∀ v c place,
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R rho omega choice c
          (Sum.inl (G.selectedMixedLargeCandidateRow
            proposal edgeLabel qLaw R choice v c place)) < bound)
    (hordinaryCap : (N : ℝ) * bound ≤ S0)
    (hreserve : 0 < reserve) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma < 1)
    (hextraCap : (1 - gamma) * N ≤ S0) :
    let residual := G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let Hbase := (G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve residual x)
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∀ slot, Hlarge.slotDegree slot ≤ S0 := by
  dsimp only
  let residual := G.selectedMixedLargeResidual
    proposal edgeLabel qLaw R rho omega choice
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let Hbase := (G.dyadicLargeEdgeOptionSystem
    (Color := Color) (explicitLargeSlotBound β qstep r)
    bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual x)
  intro slot
  apply (G.largeEdgeJobSystem_slotDegree_le Hbase β slot).trans
  cases slot with
  | inl slot =>
      have hdeg := G.selectedMixed_quantizedOrdinarySlotDegree_lt
        proposal edgeLabel qLaw R hN hq0 hqsum hqsingle
        hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 choice
        bucket gamma reserve residual bound hcapacity slot
      have hreal : (Hbase.slotDegree (Sum.inl slot) : ℝ) ≤ S0 :=
        hdeg.le.trans hordinaryCap
      exact_mod_cast hreal
  | inr slot =>
      have hres0 : ∀ e, 0 ≤ residual e := by
        intro e
        exact G.selectedMixedLargeResidual_nonneg
          proposal edgeLabel qLaw R rho omega choice e
      have hdeg := G.dyadicLargeEdge_quantized_slotDegree_inr_le
        (explicitLargeSlotBound β qstep r) bucket gamma reserve residual x
        hres0 hreserve hgamma0 hgamma1 N slot
      have hreal : (Hbase.slotDegree (Sum.inr slot) : ℝ) ≤ S0 :=
        hdeg.trans hextraCap
      exact_mod_cast hreal

theorem selectedMixedMaskedLarge_jobSlotCodegree_le
    {n : ℕ} (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (hreserve : 0 < reserve)
    (lambda : ℝ)
    (hordinary : (N : ℝ) *
      ((explicitLargeSlotBound β qstep r : ℝ) *
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
          (n : ℝ)) ≤ lambda)
    (hextra : (N : ℝ) / reserve ≤ lambda) :
    let residual := G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let Hbase := (G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve residual x)
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∀ e slot, (Hlarge.jobSlotCodegree e slot : ℝ) ≤ lambda := by
  dsimp only
  let residual := G.selectedMixedLargeResidual
    proposal edgeLabel qLaw R rho omega choice
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let Hbase := (G.dyadicLargeEdgeOptionSystem
    (Color := Color) (explicitLargeSlotBound β qstep r)
    bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual x)
  intro e slot
  rw [G.largeEdgeJobSystem_jobSlotCodegree Hbase β e slot]
  cases slot with
  | inl slot =>
      have hdeg := G.selectedMixed_quantizedOrdinaryJobSlotCodegree_le
        proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 rho C0 hrho hC0
        hproposal0 hproposal choice bucket gamma reserve N residual e.1 slot
      exact hdeg.trans hordinary
  | inr slot =>
      have hres0 : ∀ e, 0 ≤ residual e := by
        intro e
        exact G.selectedMixedLargeResidual_nonneg
          proposal edgeLabel qLaw R rho omega choice e
      have hres1 : ∀ e, residual e ≤ 1 := by
        intro e
        exact G.selectedMixedLargeResidual_le_one
          proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
          hleft homega0 homega1 hrho hproposal0 choice e
      have hdeg := G.dyadicLargeEdge_quantized_jobSlotCodegree_inr_le
        (explicitLargeSlotBound β qstep r) bucket gamma reserve residual x
        hres0 hres1 hreserve N e.1 slot
      exact hdeg.trans hextra

end WeightedMultigraph

end

end WeightedEdgeColoring
