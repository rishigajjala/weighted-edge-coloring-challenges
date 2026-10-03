import WeightedEdgeColoring.SubtwoMixedGraphCandidateEnvelope
import WeightedEdgeColoring.SubtwoLabelPackedDecoder

/-!
# Common packed color words for mixed graph atoms

Each vertex-color coordinate has the concrete state `Option (Σ label,
local rounded profile)`.  Its profile type depends on both the vertex and
the color.  The fixed alphabet bound from the mixed candidate module lets
the generic dependent-word encoder place every such word in one common
finite packed state type.  Decoding retrieves the actual selected label and
profile on genuine words; padding states have zero probability.
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

abbrev MixedGraphPackedState :=
  Subtwo.LabelledPackedWordState
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))

def mixedGraphAtomLabel (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) : Option Label :=
  Subtwo.labelMixtureAtomLabel
    (fun label ↦ G.LocalExtendedProfileState (R v c label)) a

def encodeMixedGraphWord (v : G.V)
    (word : ∀ c : Color,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    G.MixedGraphPackedState proposal edgeLabel qLaw R := by
  classical
  exact Subtwo.encodeLabelledPackedWord
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c) v word

def decodeMixedGraphAtom (v : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (c : Color) : G.MixedGraphAtom proposal edgeLabel qLaw R v c := by
  classical
  exact Subtwo.decodeLabelledPackedAtom
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (fun _ _ ↦ none)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c) v packed c

def decodeMixedGraphLabel (v : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (c : Color) : Option Label :=
  G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c
    (G.decodeMixedGraphAtom proposal edgeLabel qLaw R v packed c)

@[simp] theorem decode_encodeMixedGraphWord
    (v : G.V)
    (word : ∀ c : Color,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (c : Color) :
    G.decodeMixedGraphAtom proposal edgeLabel qLaw R v
      (G.encodeMixedGraphWord proposal edgeLabel qLaw R v word) c =
        word c := by
  classical
  exact Subtwo.decode_encodeLabelledPackedAtom
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (fun _ _ ↦ none)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c) v word c

@[simp] theorem decode_encodeMixedGraphLabel
    (v : G.V)
    (word : ∀ c : Color,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (c : Color) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R v
      (G.encodeMixedGraphWord proposal edgeLabel qLaw R v word) c =
      G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c (word c) := by
  simp [decodeMixedGraphLabel]

def paddedMixedGraphWordProbability (omega : ℝ) (v : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R) : ℝ := by
  classical
  exact Subtwo.paddedLabelledWordProbability
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
    v packed

theorem sum_paddedMixedGraphWordProbability
    (omega : ℝ) (v : G.V) :
    (∑ packed : G.MixedGraphPackedState proposal edgeLabel qLaw R,
      G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega v packed) = 1 := by
  classical
  exact Subtwo.sum_paddedLabelledWordProbability
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
    (fun v c ↦ G.sum_smoothedMixedGraphProbability
      proposal edgeLabel qLaw R omega v c) v

theorem paddedMixedGraphWordProbability_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R) :
    0 ≤ G.paddedMixedGraphWordProbability
      proposal edgeLabel qLaw R omega v packed := by
  classical
  exact Subtwo.paddedLabelledWordProbability_nonneg
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
    (fun v c a ↦ (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 v c a).le)
    v packed

theorem exists_mixedGraphWord_of_padded_pos
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (hpos : 0 < G.paddedMixedGraphWordProbability
      proposal edgeLabel qLaw R omega v packed) :
    ∃ word : ∀ c : Color,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      G.encodeMixedGraphWord proposal edgeLabel qLaw R v word = packed := by
  classical
  obtain ⟨word, hcode, _⟩ :=
    Subtwo.exists_labelledWord_of_paddedProbability_pos
      (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
      (mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r))
      (fun v c ↦ G.mixedGraphAtom_card_le
        proposal edgeLabel qLaw R v c)
      (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
      (fun v c a ↦ (G.smoothedMixedGraphProbability_pos
        proposal edgeLabel qLaw R hq0 hqsum hqsingle
        hs hqstep hr0 hleft homega0 homega1 v c a).le)
      v packed hpos
  exact ⟨word, hcode⟩

/-- Before smoothing, the chance that one color chooses a given endpoint
label is exactly its original nonempty outcome mass. -/
theorem sum_mixedGraphProbability_label
    (v : G.V) (c : Color) (label : Label) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      G.mixedGraphProbability proposal edgeLabel qLaw R v c a *
        (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
          some label then (1 : ℝ) else 0)) =
      subsetLabelMass (edgeLabel v) (qLaw v c) label := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [mixedGraphProbability, mixedLabelGraphAtomProbability,
    Subtwo.labelMixtureAtomProbability, mixedGraphAtomLabel,
    Subtwo.labelMixtureAtomLabel, reduceCtorEq, ite_false, mul_zero,
    zero_add, Option.some.injEq, mul_ite, mul_one]
  rw [Finset.sum_eq_single label]
  · simp only [ite_true]
    rw [← Finset.mul_sum]
    simp only [G.sum_localExtendedProfileProbability]
    ring
  · intro other _ hne
    simp [hne]
  · simp

/-- Uniform smoothing changes one label's probability by at most `omega`.
The unconditioned label mass remains the controlling term. -/
theorem sum_smoothedMixedGraphProbability_label_le
    (homega0 : 0 ≤ omega) (homega1 : omega ≤ 1)
    (v : G.V) (c : Color) (label : Label) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega v c a *
        (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
          some label then (1 : ℝ) else 0)) ≤
      (1 - omega) * subsetLabelMass (edgeLabel v) (qLaw v c) label + omega := by
  classical
  have hcard : 0 < (Fintype.card
      (G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hterm : ∀ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      (omega / Fintype.card
        (G.MixedGraphAtom proposal edgeLabel qLaw R v c)) *
        (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
          some label then (1 : ℝ) else 0) ≤
      omega / Fintype.card
        (G.MixedGraphAtom proposal edgeLabel qLaw R v c) := by
    intro a
    split
    · simp
    · simpa using div_nonneg homega0 hcard.le
  calc
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega v c a *
        (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
          some label then (1 : ℝ) else 0)) =
      (1 - omega) *
        (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
          G.mixedGraphProbability proposal edgeLabel qLaw R v c a *
            (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
              some label then (1 : ℝ) else 0)) +
      (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        (omega / Fintype.card
          (G.MixedGraphAtom proposal edgeLabel qLaw R v c)) *
          (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
            some label then (1 : ℝ) else 0)) := by
      calc
        (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega v c a *
            (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
              some label then (1 : ℝ) else 0)) =
          ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
            ((1 - omega) *
              (G.mixedGraphProbability proposal edgeLabel qLaw R v c a *
                (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
                  some label then (1 : ℝ) else 0)) +
              (omega / Fintype.card
                (G.MixedGraphAtom proposal edgeLabel qLaw R v c)) *
                (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
                  some label then (1 : ℝ) else 0)) := by
          apply Finset.sum_congr rfl
          intro a _
          unfold smoothedMixedGraphProbability
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ (1 - omega) * subsetLabelMass (edgeLabel v) (qLaw v c) label +
        ∑ _a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
          omega / Fintype.card
            (G.MixedGraphAtom proposal edgeLabel qLaw R v c) := by
      rw [G.sum_mixedGraphProbability_label
        proposal edgeLabel qLaw R v c label]
      gcongr
      exact hterm _
    _ = (1 - omega) * subsetLabelMass (edgeLabel v) (qLaw v c) label +
        omega := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hcard.ne']

/-- The expected number of colors selecting a fixed endpoint label is
controlled by the sum of its original label masses, plus the fixed
smoothing error per color.  The expectation is taken on the actual common
packed word that the selector sees. -/
theorem sum_paddedMixedGraphProbability_mul_labelCount_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (homega0 : 0 ≤ omega) (homega1 : omega ≤ 1)
    (v : G.V) (label : Label) :
    (∑ packed : G.MixedGraphPackedState proposal edgeLabel qLaw R,
      G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega v packed *
        (∑ c : Color,
          if G.decodeMixedGraphLabel proposal edgeLabel qLaw R
              v packed c = some label then (1 : ℝ) else 0)) ≤
      (∑ c : Color, subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        (Fintype.card Color : ℝ) * omega := by
  classical
  have hmean := Subtwo.sum_paddedProbability_mul_labelCount
    (fun v c ↦ G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (G.mixedGraphAtomLabel proposal edgeLabel qLaw R)
    (fun _ _ ↦ none)
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r))
    (fun v c ↦ G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega)
    (fun v c ↦ G.sum_smoothedMixedGraphProbability
      proposal edgeLabel qLaw R omega v c) v (some label)
  change (∑ packed : G.MixedGraphPackedState proposal edgeLabel qLaw R,
    G.paddedMixedGraphWordProbability
      proposal edgeLabel qLaw R omega v packed *
      (∑ c : Color,
        if G.decodeMixedGraphLabel proposal edgeLabel qLaw R
            v packed c = some label then (1 : ℝ) else 0)) =
    ∑ c : Color, ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega v c a *
        (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
          some label then (1 : ℝ) else 0) at hmean
  rw [hmean]
  calc
    (∑ c : Color,
      ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega v c a *
          (if G.mixedGraphAtomLabel proposal edgeLabel qLaw R v c a =
            some label then (1 : ℝ) else 0)) ≤
      ∑ c : Color,
        ((1 - omega) * subsetLabelMass (edgeLabel v) (qLaw v c) label +
          omega) := by
      apply Finset.sum_le_sum
      intro c _
      exact G.sum_smoothedMixedGraphProbability_label_le
        proposal edgeLabel qLaw R homega0 homega1 v c label
    _ ≤ ∑ c : Color,
        (subsetLabelMass (edgeLabel v) (qLaw v c) label + omega) := by
      apply Finset.sum_le_sum
      intro c _
      have hm0 : 0 ≤ subsetLabelMass (edgeLabel v) (qLaw v c) label := by
        exact G.subsetLabelMass_nonneg_local
          (edgeLabel v) (qLaw v c) (hq0 v c) label
      nlinarith [mul_nonneg homega0 hm0]
    _ = (∑ c : Color, subsetLabelMass (edgeLabel v) (qLaw v c) label) +
        (Fintype.card Color : ℝ) * omega := by
      rw [Finset.sum_add_distrib]
      simp


end WeightedMultigraph

end

end WeightedEdgeColoring
