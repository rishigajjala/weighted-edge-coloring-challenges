import WeightedEdgeColoring.SubtwoMixedGraphReservoirRelative
import WeightedEdgeColoring.SubtwoMixedGraphJointDecoder

/-!
# Transfer reservoir-relative means through the packed-word selector
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

theorem scaledMixedTinyCandidateAtomMean_le_concreteReservoir
    (n : ℕ) (scale rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hscale : 0 < scale) (c : Color)
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
            n scale rho omega source c z (Sum.inr row)) ≤
      (n : ℝ) / scale *
        (rho / (1 - omega) *
          G.mixedGraphConcreteReservoirSize proposal edgeLabel qLaw R
            row.center c row.candidate) := by
  have hraw := G.mixedTinyCandidateAtomMean_le_concreteReservoir
    proposal edgeLabel qLaw R rho omega hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho c row
  unfold scaledMixedCandidateAtomUse
  have hrearrange :
      (∑ source : G.V,
        ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega source c z *
            ((n : ℝ) * G.mixedCandidateAtomUse
              proposal edgeLabel qLaw R rho omega source c z (Sum.inr row) /
              scale)) =
        (n : ℝ) / scale *
          (∑ source : G.V,
            ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
              G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
                omega source c z *
                G.mixedCandidateAtomUse proposal edgeLabel qLaw R
                  rho omega source c z (Sum.inr row)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hrearrange]
  exact mul_le_mul_of_nonneg_left hraw
    (div_nonneg (Nat.cast_nonneg n) hscale.le)

theorem mixedGraphJointTiny_rowMean_le_concreteReservoir
    (hColor : 0 < Fintype.card Color)
    (n : ℕ) (scale rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hscale : 0 < scale) (c : Color)
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :
    FiniteCategoricalSelection.rowMean
      (G.paddedMixedGraphWordProbability proposal edgeLabel qLaw R omega)
      (G.mixedGraphJointUse proposal edgeLabel qLaw R
        hColor n scale rho omega) (Sum.inl ⟨c, Sum.inr row⟩) ≤
      (n : ℝ) / scale *
        (rho / (1 - omega) *
          G.mixedGraphConcreteReservoirSize proposal edgeLabel qLaw R
            row.center c row.candidate) := by
  classical
  change (∑ v, ∑ packed,
    G.paddedMixedGraphWordProbability proposal edgeLabel qLaw R
      omega v packed *
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
        n scale rho omega v c
        (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
          v packed c) (Sum.inr row)) ≤ _
  have heq : (∑ v, ∑ packed,
      G.paddedMixedGraphWordProbability proposal edgeLabel qLaw R
        omega v packed *
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
          n scale rho omega v c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
            v packed c) (Sum.inr row)) =
      ∑ v, ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega v c z *
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
            n scale rho omega v c z (Sum.inr row) := by
    apply Finset.sum_congr rfl
    intro v _
    exact Subtwo.sum_paddedLabelledProbability_mul_decode_coordinate
      (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
      (fun _ _ ↦ none)
      (mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r))
      (fun v c ↦ G.mixedGraphAtom_card_le
        proposal edgeLabel qLaw R v c)
      (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
      (fun v c ↦ G.sum_smoothedMixedGraphProbability
        proposal edgeLabel qLaw R omega v c)
      v c (fun z ↦ G.scaledMixedCandidateAtomUse
        proposal edgeLabel qLaw R n scale rho omega v c z (Sum.inr row))
  rw [heq]
  exact G.scaledMixedTinyCandidateAtomMean_le_concreteReservoir
    proposal edgeLabel qLaw R n scale rho omega
    hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
    homega0 homega1 hrho hscale c row

private theorem scaled_lt_base
    {n : ℕ} (hn : 0 < n) {scale load base deviation : ℝ}
    (hscale : 0 < scale)
    (h : (n : ℝ) * load / scale <
      (n : ℝ) / scale * base + deviation) :
    load < base + scale / (n : ℝ) * deviation := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrow' : (n : ℝ) * load / scale <
      ((n : ℝ) * base + scale * deviation) / scale := by
    calc
      _ < (n : ℝ) / scale * base + deviation := h
      _ = ((n : ℝ) * base + scale * deviation) / scale := by
        field_simp [ne_of_gt hscale]
        <;> ring
  have h' := (div_lt_div_iff_of_pos_right hscale).1 hrow'
  calc
    load < ((n : ℝ) * base + scale * deviation) / (n : ℝ) :=
      (lt_div_iff₀ hnR).2 (by simpa [mul_comm] using h')
    _ = base + scale / (n : ℝ) * deviation := by
      field_simp [ne_of_gt hnR]
      <;> ring

/-- The same selected packed word has a reservoir-relative tiny load bound.
Unlike the coarse global candidate bound, it leaves physical slack even as
the reservoir granularity tends to zero. -/
theorem selectedMixedNormalizedTinyReservoirLoad_lt_relative
    {n : ℕ} (hn : 0 < n)
    (hColor : 0 < Fintype.card Color)
    (scale rho omega deviation : ℝ) (hscale : 0 < scale)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (hrow : FiniteCategoricalSelection.rowLoad
      (G.mixedGraphJointUse proposal edgeLabel qLaw R
        hColor n scale rho omega)
      (Sum.inl ⟨c, Sum.inr (G.selectedMixedTinyCandidateRow
        proposal edgeLabel qLaw R choice v c)⟩) choice <
        FiniteCategoricalSelection.rowMean
          (G.paddedMixedGraphWordProbability
            proposal edgeLabel qLaw R omega)
          (G.mixedGraphJointUse proposal edgeLabel qLaw R
            hColor n scale rho omega)
          (Sum.inl ⟨c, Sum.inr (G.selectedMixedTinyCandidateRow
            proposal edgeLabel qLaw R choice v c)⟩) + deviation) :
    G.selectedMixedNormalizedTinyReservoirLoad
      proposal edgeLabel qLaw R rho omega choice v c <
      rho / (1 - omega) *
        G.selectedMixedConcreteReservoirSize
          proposal edgeLabel qLaw R choice v c +
        scale / (n : ℝ) * deviation := by
  let row := G.selectedMixedTinyCandidateRow
    proposal edgeLabel qLaw R choice v c
  have hmean := G.mixedGraphJointTiny_rowMean_le_concreteReservoir
    proposal edgeLabel qLaw R hColor n scale rho omega
    hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
    homega0 homega1 hrho hscale c row
  have hrow' :
      (∑ source : G.V,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
          n scale rho omega source c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
            source (choice source) c) (Sum.inr row)) <
      FiniteCategoricalSelection.rowMean
        (G.paddedMixedGraphWordProbability proposal edgeLabel qLaw R omega)
        (G.mixedGraphJointUse proposal edgeLabel qLaw R
          hColor n scale rho omega) (Sum.inl ⟨c, Sum.inr row⟩) +
        deviation := by
    simpa only [row, FiniteCategoricalSelection.rowLoad,
      mixedGraphJointUse] using hrow
  have hplus :
      FiniteCategoricalSelection.rowMean
        (G.paddedMixedGraphWordProbability proposal edgeLabel qLaw R omega)
        (G.mixedGraphJointUse proposal edgeLabel qLaw R
          hColor n scale rho omega) (Sum.inl ⟨c, Sum.inr row⟩) +
        deviation ≤
      (n : ℝ) / scale *
        (rho / (1 - omega) *
          G.mixedGraphConcreteReservoirSize proposal edgeLabel qLaw R
            row.center c row.candidate) + deviation := by
    simpa [add_comm] using add_le_add_right hmean deviation
  have hbound := lt_of_lt_of_le hrow' hplus
  rw [G.sum_scaledMixedCandidateAtomUse_eq_selectedLoad
    proposal edgeLabel qLaw R n scale rho omega choice c (Sum.inr row)] at hbound
  have hraw := scaled_lt_base hn hscale hbound
  have hraw' : G.selectedMixedTinyReservoirLoad
      proposal edgeLabel qLaw R rho omega choice v c <
      rho / (1 - omega) *
        G.selectedMixedConcreteReservoirSize
          proposal edgeLabel qLaw R choice v c +
        scale / (n : ℝ) * deviation := by
    simpa [row, G.selectedMixedTinyCapacityLoad_eq_reservoirLoad]
      using hraw
  exact lt_of_le_of_lt
    (G.selectedMixedNormalizedTinyReservoirLoad_le
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1.le hrho hproposal0 choice v c) hraw'

end WeightedMultigraph

end

end WeightedEdgeColoring
