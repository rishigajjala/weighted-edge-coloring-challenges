import WeightedEdgeColoring.SubtwoMixedGraphJointSelection

/-!
# Explicit endpoint-label counts from the joint mixed selector

The joint packed-word selector controls a normalized label-count row.
This module identifies that row with the number of selected colors carrying
a given endpoint label and compares its mean with the original conditional
label mass.
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

def selectedMixedEndpointLabelCount
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (label : Label) : ℝ :=
  ∑ c : Color,
    if G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      v (choice v) c = some label then 1 else 0

/-- The concrete colors reserved for one endpoint label at a vertex. -/
def selectedMixedEndpointLabelColors
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (label : Label) : Finset Color :=
  Finset.univ.filter fun c ↦
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      v (choice v) c = some label

theorem selectedMixedEndpointLabelCount_eq_card
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (label : Label) :
    G.selectedMixedEndpointLabelCount proposal edgeLabel qLaw R
      choice v label =
      (G.selectedMixedEndpointLabelColors proposal edgeLabel qLaw R
        choice v label).card := by
  classical
  simp only [selectedMixedEndpointLabelCount,
    selectedMixedEndpointLabelColors, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem selectedMixedEndpointLabelColors_disjoint
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) {label label' : Label} (h : label ≠ label') :
    Disjoint
      (G.selectedMixedEndpointLabelColors proposal edgeLabel qLaw R
        choice v label)
      (G.selectedMixedEndpointLabelColors proposal edgeLabel qLaw R
        choice v label') := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hc hc'
  simp only [selectedMixedEndpointLabelColors, Finset.mem_filter,
    Finset.mem_univ, true_and] at hc hc'
  exact h (by simpa using hc.symm.trans hc')

private theorem sum_mixedGraphPackedCoordinateLabel_eq_color
    (v : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (label : Label) :
    (∑ i : Fin (Fintype.card Color),
      if G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R
          v packed i = some label then (1 : ℝ) else 0) =
      ∑ c : Color,
        if G.decodeMixedGraphLabel proposal edgeLabel qLaw R
            v packed c = some label then (1 : ℝ) else 0 := by
  simpa [mixedGraphPackedCoordinateLabel] using
    (Equiv.sum_comp (Fintype.equivFin Color).symm
      (fun c : Color ↦
        if G.decodeMixedGraphLabel proposal edgeLabel qLaw R
            v packed c = some label then (1 : ℝ) else 0))

theorem selectedMixedLabel_rowLoad_eq_count_div
    (hColor : 0 < Fintype.card Color)
    (n : ℕ) (scale rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (label : Label) :
    FiniteCategoricalSelection.rowLoad
      (G.mixedGraphJointUse proposal edgeLabel qLaw R
        hColor n scale rho omega)
      (Sum.inr (v, some label)) choice =
      G.selectedMixedEndpointLabelCount
        proposal edgeLabel qLaw R choice v label /
        Fintype.card Color := by
  classical
  unfold FiniteCategoricalSelection.rowLoad
  rw [Finset.sum_eq_single v]
  · simp only [mixedGraphJointUse, Subtwo.packedLabelUse,
      Function.id_def, eq_self, ite_true]
    rw [G.sum_mixedGraphPackedCoordinateLabel_eq_color
      proposal edgeLabel qLaw R v (choice v) label]
    rfl
  · intro source _ hsource
    simp [mixedGraphJointUse, Subtwo.packedLabelUse, hsource]
  · simp

theorem mixedGraphLabel_rowMean_le_charge
    (hColor : 0 < Fintype.card Color)
    (n : ℕ) (scale rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (homega0 : 0 ≤ omega) (homega1 : omega ≤ 1)
    (v : G.V) (label : Label) :
    FiniteCategoricalSelection.rowMean
      (G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega)
      (G.mixedGraphJointUse proposal edgeLabel qLaw R
        hColor n scale rho omega)
      (Sum.inr (v, some label)) ≤
      ((∑ c : Color,
        subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        (Fintype.card Color : ℝ) * omega) /
        Fintype.card Color := by
  classical
  let prob := G.paddedMixedGraphWordProbability
    proposal edgeLabel qLaw R omega
  unfold FiniteCategoricalSelection.rowMean
  rw [Finset.sum_eq_single v]
  · simp only [mixedGraphJointUse, Subtwo.packedLabelUse,
      Function.id_def, eq_self, ite_true]
    have hconvert :
        (∑ packed : G.MixedGraphPackedState proposal edgeLabel qLaw R,
          prob v packed *
            ((∑ i : Fin (Fintype.card Color),
              if G.mixedGraphPackedCoordinateLabel
                  proposal edgeLabel qLaw R v packed i = some label
                then (1 : ℝ) else 0) / Fintype.card Color)) =
          (∑ packed : G.MixedGraphPackedState proposal edgeLabel qLaw R,
            prob v packed *
              (∑ c : Color,
                if G.decodeMixedGraphLabel proposal edgeLabel qLaw R
                    v packed c = some label then (1 : ℝ) else 0)) /
              Fintype.card Color := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro packed _
      rw [G.sum_mixedGraphPackedCoordinateLabel_eq_color
        proposal edgeLabel qLaw R v packed label]
      ring
    rw [hconvert]
    have hcharge := G.sum_paddedMixedGraphProbability_mul_labelCount_le
      proposal edgeLabel qLaw R hq0 homega0 homega1 v label
    have hk : (0 : ℝ) < Fintype.card Color := by exact_mod_cast hColor
    exact div_le_div_of_nonneg_right hcharge hk.le
  · intro source _ hsource
    simp [mixedGraphJointUse, Subtwo.packedLabelUse, hsource]
  · simp

/-- The label row of a joint selected word gives an actual integer label
count.  This bound keeps the label's own conditional mass, rather than
replacing it by the larger universal candidate-capacity mean. -/
theorem selectedMixedEndpointLabelCount_lt_charge
    (hColor : 0 < Fintype.card Color)
    (n : ℕ) (scale rho omega deviation : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (homega0 : 0 ≤ omega) (homega1 : omega ≤ 1)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (label : Label)
    (hrow :
      FiniteCategoricalSelection.rowLoad
        (G.mixedGraphJointUse proposal edgeLabel qLaw R
          hColor n scale rho omega)
        (Sum.inr (v, some label)) choice <
      FiniteCategoricalSelection.rowMean
        (G.paddedMixedGraphWordProbability
          proposal edgeLabel qLaw R omega)
        (G.mixedGraphJointUse proposal edgeLabel qLaw R
          hColor n scale rho omega)
        (Sum.inr (v, some label)) + deviation) :
    G.selectedMixedEndpointLabelCount
      proposal edgeLabel qLaw R choice v label <
      (∑ c : Color,
        subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        (Fintype.card Color : ℝ) * (omega + deviation) := by
  have hk : (0 : ℝ) < Fintype.card Color := by exact_mod_cast hColor
  rw [G.selectedMixedLabel_rowLoad_eq_count_div
    proposal edgeLabel qLaw R hColor n scale rho omega choice v label] at hrow
  have hmean := G.mixedGraphLabel_rowMean_le_charge
    proposal edgeLabel qLaw R hColor n scale rho omega
    hq0 homega0 homega1 v label
  have hbound := lt_of_lt_of_le hrow (add_le_add hmean le_rfl)
  have hscaled := (div_lt_iff₀ hk).mp hbound
  calc
    G.selectedMixedEndpointLabelCount
        proposal edgeLabel qLaw R choice v label <
        ((∑ c : Color,
            subsetLabelMass (edgeLabel v) (qLaw v c) label) +
          (Fintype.card Color : ℝ) * omega) /
          Fintype.card Color * Fintype.card Color +
          deviation * Fintype.card Color := by
        convert hscaled using 1 <;> ring
    _ = _ := by
      field_simp [ne_of_gt hk]
      ring

theorem mixedGraphCandidateCapacity_rowMean_le
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
    (hrho : 0 ≤ rho) (hscale : 0 < scale)
    (cr : Σ c : Color,
      G.MixedCandidateRowAt proposal edgeLabel qLaw R c) :
    FiniteCategoricalSelection.rowMean
      (G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega)
      (G.mixedGraphJointUse proposal edgeLabel qLaw R
        hColor n scale rho omega)
      (Sum.inl cr) ≤
      (n : ℝ) * (rho / (1 - omega)) / scale := by
  classical
  change (∑ v, ∑ packed,
    G.paddedMixedGraphWordProbability proposal edgeLabel qLaw R
      omega v packed *
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
        n scale rho omega v cr.1
        (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
          v packed cr.1) cr.2) ≤ _
  have heq : (∑ v, ∑ packed,
      G.paddedMixedGraphWordProbability proposal edgeLabel qLaw R
        omega v packed *
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
          n scale rho omega v cr.1
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
            v packed cr.1) cr.2) =
      ∑ v, ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R v cr.1,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega v cr.1 z *
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
            n scale rho omega v cr.1 z cr.2 := by
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
      v cr.1 (fun z ↦ G.scaledMixedCandidateAtomUse
        proposal edgeLabel qLaw R n scale rho omega v cr.1 z cr.2)
  rw [heq]
  exact G.scaledMixedCandidateAtomMean_le_one_sub_omega
    proposal edgeLabel qLaw R n scale rho omega
    hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
    homega0 homega1 hrho hscale cr.1 cr.2

/-- One selected mixed word controls both the raw candidate loads and the
actual endpoint-label counts.  The latter is charged to its own conditional
label mass, which is the quantity needed by block palette restoration. -/
theorem exists_mixedGraphPackedWord_rawLoads_and_labelCounts_lt
    {L n D : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hColor : 0 < Fintype.card Color)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 < s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hdegree : ∀ v, Fintype.card (G.StarEdge v) ≤ D * n) :
    let scale := (L : ℝ) * mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
    let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
    let columnBound := mixedCandidatePerColorColumnBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) D n
    let deviation := FinitePartialResamplingNumerics.packingDeviation
      (1 + meanBound)
      ((Fintype.card Color : ℝ) * columnBound +
        Fintype.card (Option Label))
    ∃ choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R,
      (∀ v, 0 < G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega v (choice v)) ∧
      (∀ c (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c),
        G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
          rho omega choice c row <
          rho / (1 - omega) + scale / (n : ℝ) * deviation) ∧
      (∀ v label,
        G.selectedMixedEndpointLabelCount
          proposal edgeLabel qLaw R choice v label <
          (∑ c : Color,
            subsetLabelMass (edgeLabel v) (qLaw v c) label) +
            (Fintype.card Color : ℝ) * (omega + deviation)) := by
  classical
  let scale := (L : ℝ) * mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
  let columnBound := mixedCandidatePerColorColumnBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) D n
  let deviation := FinitePartialResamplingNumerics.packingDeviation
    (1 + meanBound)
    ((Fintype.card Color : ℝ) * columnBound +
      Fintype.card (Option Label))
  obtain ⟨choice, hpos, hrows⟩ :=
    G.exists_mixedGraphPackedWord_candidateAndLabelRows_lt
      proposal edgeLabel qLaw R hL hmult hn hColor
      hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
      homega0 homega1 hrho hC0 hproposal0 hproposal hdegree
  have hscale : 0 < scale := by
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    exact mul_pos hLreal
      (mixedCandidateOrientedScale_pos hrho hs homega0 hC0)
  refine ⟨choice, hpos, ?_, ?_⟩
  · intro c row
    have hrow := hrows (Sum.inl ⟨c, row⟩)
    change (∑ source : G.V,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
        n scale rho omega source c
        (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
          source (choice source) c) row) < _ at hrow
    have hmean := G.mixedGraphCandidateCapacity_rowMean_le
      proposal edgeLabel qLaw R hColor n scale rho omega
      hq0 hqmarg hqsingle hqsum hs.le hqstep hr0 hleft
      homega0 homega1 hrho.le hscale ⟨c, row⟩
    have hbound := lt_of_lt_of_le hrow (add_le_add hmean le_rfl)
    exact G.selectedMixedCandidateCapacityLoad_lt
      proposal edgeLabel qLaw R hn scale rho omega deviation hscale
      choice c row hbound
  · intro v label
    exact G.selectedMixedEndpointLabelCount_lt_charge
      proposal edgeLabel qLaw R hColor n scale rho omega deviation
      hq0 homega0.le homega1.le choice v label
      (hrows (Sum.inr (v, some label)))

end WeightedMultigraph

end

end WeightedEdgeColoring
