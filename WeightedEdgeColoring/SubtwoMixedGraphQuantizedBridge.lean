import WeightedEdgeColoring.SubtwoMixedGraphTinyRounding
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeOptionBounds

/-!
# Quantized large-edge data for the selected mixed graph

The normalized selected large options retain the diffuse edge envelope and
the physical slot-load bounds.  These are the two estimates consumed by the
ordinary part of the rank-three matching iteration.
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
variable {N : ℕ}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

theorem selectedMixedNormalizedLargeOptionMass_nonneg
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
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r)) :
    0 ≤ G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j := by
  unfold selectedMixedNormalizedLargeOptionMass
  exact div_nonneg
    (G.selectedMixedLargeOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e c i j)
    (G.selectedMixedNormalizationDenominator_pos
      proposal edgeLabel qLaw R rho omega choice e).le

/-- The selected oriented large option has the same `scale/n` envelope as
its raw two-endpoint product. -/
theorem n_mul_sum_selectedMixedNormalizedLarge_le_scale
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
    (e : G.E) (c : Color)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    (n : ℝ) *
        (∑ j, G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c i j) ≤
      mixedGraphCandidateCapacityScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  have hsum :
      (∑ j, G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j) ≤
      ∑ j, G.selectedMixedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j := by
    apply Finset.sum_le_sum
    intro j _
    exact G.selectedMixedNormalizedLargeOptionMass_le
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e c i j
  have hraw := G.n_mul_sum_mixedGraphLargeProductMass_le_scale
    proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho hC0
    hproposal0 hproposal e c
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      (G.fst e) (choice (G.fst e)) c)
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      (G.snd e) (choice (G.snd e)) c) i
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    (by simpa [selectedMixedLargeOptionMass] using hraw)

/-- Summing over the fixed padded place alphabet gives a diffuse bound for
one physical edge and one colour. -/
theorem selectedMixedNormalizedLarge_colorMass_le
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
    (e : G.E) (c : Color) :
    (∑ i, ∑ j, G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j) ≤
      (explicitLargeSlotBound β qstep r : ℝ) *
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
          (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).2
  calc
    (∑ i, ∑ j, G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j) * (n : ℝ) =
        ∑ i, (n : ℝ) *
          (∑ j, G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice e c i j) := by
      rw [mul_comm, Finset.mul_sum]
    _ ≤ ∑ _i : Fin (explicitLargeSlotBound β qstep r),
          mixedGraphCandidateCapacityScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
      apply Finset.sum_le_sum
      intro i _
      exact G.n_mul_sum_selectedMixedNormalizedLarge_le_scale
        proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        hproposal0 hproposal choice e c i
    _ = (explicitLargeSlotBound β qstep r : ℝ) *
          mixedGraphCandidateCapacityScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0 := by simp

/-- The copied ordinary job-slot codegree is at most `N` times the
diffuse colour envelope. -/
theorem selectedMixed_quantizedOrdinaryJobSlotCodegree_le
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
    (rho C0 : ℝ) (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (residual : G.E → ℝ)
    (e : G.E)
    (slot : OrdinarySlot G.V Color (explicitLargeSlotBound β qstep r)) :
    (((G.dyadicLargeEdgeOptionSystem
        (Color := Color) (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice))).jobSlotCodegree
            e (Sum.inl slot) : ℝ) ≤
      (N : ℝ) *
        ((explicitLargeSlotBound β qstep r : ℝ) *
          mixedGraphCandidateCapacityScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0 /
            (n : ℝ)) := by
  have hx0 : ∀ e c i j,
      0 ≤ G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j := by
    intro e c i j
    exact G.selectedMixedNormalizedLargeOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e c i j
  have hbase := G.dyadicLargeEdge_quantized_jobSlotCodegree_inl_le
    (explicitLargeSlotBound β qstep r) bucket gamma reserve residual
    (G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice) hx0 N e slot
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (G.selectedMixedNormalizedLarge_colorMass_le
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal choice e slot.color) (by positivity))

/-- The actual selected candidate row bounds the copied ordinary slot
degree after the same edgewise normalization. -/
theorem selectedMixed_quantizedOrdinarySlotDegree_lt
    (hN : 0 < N)
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
    (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (bound : ℝ)
    (hcapacity : ∀ v c slot,
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R rho omega choice c
          (Sum.inl (G.selectedMixedLargeCandidateRow
            proposal edgeLabel qLaw R choice v c slot)) < bound)
    (slot : OrdinarySlot G.V Color (explicitLargeSlotBound β qstep r)) :
    ((((G.dyadicLargeEdgeOptionSystem
        (Color := Color) (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve residual
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice))).slotDegree
            (Sum.inl slot) : ℕ) : ℝ) <
      (N : ℝ) * bound := by
  have hx0 : ∀ e c i j,
      0 ≤ G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j := by
    intro e c i j
    exact G.selectedMixedNormalizedLargeOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e c i j
  have hbase := G.dyadicLargeEdge_quantized_slotDegree_inl_le
    (explicitLargeSlotBound β qstep r) bucket gamma reserve residual
    (G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice) hx0 N slot
  change _ ≤ (N : ℝ) *
    G.selectedMixedNormalizedLargeSlotLoad
      proposal edgeLabel qLaw R rho omega choice
        slot.vertex slot.color slot.place at hbase
  have hnormal := G.selectedMixedNormalizedLargeSlotLoad_le
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice
    slot.vertex slot.color slot.place
  have hraw := G.selectedMixedLargeSlotLoad_lt
    proposal edgeLabel qLaw R rho omega bound choice
    slot.vertex slot.color slot.place
    (hcapacity slot.vertex slot.color slot.place)
  exact hbase.trans_lt
    (mul_lt_mul_of_pos_left (hnormal.trans_lt hraw) (by exact_mod_cast hN))

end WeightedMultigraph

end

end WeightedEdgeColoring
