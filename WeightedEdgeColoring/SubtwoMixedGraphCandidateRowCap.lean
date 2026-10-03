import WeightedEdgeColoring.SubtwoMixedGraphCandidateOptionBounds

/-!
# Unit capacity for each scaled mixed candidate coefficient

The only graph input to this step is bounded endpoint-pair multiplicity.
Every candidate row sees edges only between its center and source, and each
such edge has the fixed oriented diffuse envelope.  Summing over the pair
cell gives a unit-bounded coefficient for the finite packing selector.
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

private theorem mixedLargeCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedLargeCandidateRow
      proposal edgeLabel qLaw R c)
    (h : ¬G.EndpointPairMatches row.center source e) :
    G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom e row = 0 := by
  unfold EndpointPairMatches at h
  simp only [not_or] at h
  simp [mixedLargeCandidateEdgeUse, h.1, h.2]

private theorem mixedTinyCandidateEdgeUse_eq_zero_of_not_matches
    (rho omega : ℝ) (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (e : G.E) (row : G.MixedTinyCandidateRow
      proposal edgeLabel qLaw R c)
    (h : ¬G.EndpointPairMatches row.center source e) :
    G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom e row = 0 := by
  unfold EndpointPairMatches at h
  simp only [not_or] at h
  simp [mixedTinyCandidateEdgeUse, h.1, h.2]

theorem mixedCandidateOrientedScale_pos
    (hrho : 0 < rho) (hs : 0 < s)
    (homega0 : 0 < omega) (hC0 : 0 < C0) :
    0 < mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  unfold mixedCandidateOrientedScale mixedGraphCandidateCapacityScale
    mixedGraphAtomBound extendedProfileStateBound profileStateBound
  positivity

theorem scaledMixedCandidateAtomUse_le_one
    {L n : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 < s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) :
    G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
      ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0)
      rho omega source c sourceAtom row ≤ 1 := by
  classical
  let baseScale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let scale := (L : ℝ) * baseScale
  have hbase : 0 < baseScale :=
    mixedCandidateOrientedScale_pos hrho hs homega0 hC0
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hscale : 0 < scale := mul_pos hLreal hbase
  apply (div_le_one hscale).2
  rcases row with large | tiny
  · unfold mixedCandidateAtomUse
    let F := G.endpointPairCell large.center source
    have hout : ∀ e ∈ (Finset.univ : Finset G.E), e ∉ F →
        G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R rho omega
          source c sourceAtom e large = 0 := by
      intro e _ heF
      apply G.mixedLargeCandidateEdgeUse_eq_zero_of_not_matches
        proposal edgeLabel qLaw R
      intro hmatch
      exact heF ((G.mem_endpointPairCell_iff_endpointPairMatches
        large.center source e).mpr hmatch)
    have hrestrict :
        (∑ e : G.E,
          G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R rho omega
            source c sourceAtom e large) =
          ∑ e ∈ F,
            G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R rho omega
              source c sourceAtom e large := by
      symm
      exact Finset.sum_subset (Finset.subset_univ F) hout
    change (n : ℝ) * (∑ e : G.E,
      G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R rho omega
        source c sourceAtom e large) ≤ scale
    rw [hrestrict, Finset.mul_sum]
    calc
      (∑ e ∈ F, (n : ℝ) *
        G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R rho omega
          source c sourceAtom e large) ≤
          ∑ _e ∈ F, baseScale := by
        apply Finset.sum_le_sum
        intro e _
        exact G.n_mul_mixedLargeCandidateEdgeUse_le_scale
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
          hproposal0 hproposal source c sourceAtom e large
      _ = (F.card : ℝ) * baseScale := by simp
      _ ≤ (L : ℝ) * baseScale := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hmult large.center source) hbase.le
      _ = scale := rfl
  · unfold mixedCandidateAtomUse
    let F := G.endpointPairCell tiny.center source
    have hout : ∀ e ∈ (Finset.univ : Finset G.E), e ∉ F →
        G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R rho omega
          source c sourceAtom e tiny = 0 := by
      intro e _ heF
      apply G.mixedTinyCandidateEdgeUse_eq_zero_of_not_matches
        proposal edgeLabel qLaw R
      intro hmatch
      exact heF ((G.mem_endpointPairCell_iff_endpointPairMatches
        tiny.center source e).mpr hmatch)
    have hrestrict :
        (∑ e : G.E,
          G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R rho omega
            source c sourceAtom e tiny) =
          ∑ e ∈ F,
            G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R rho omega
              source c sourceAtom e tiny := by
      symm
      exact Finset.sum_subset (Finset.subset_univ F) hout
    change (n : ℝ) * (∑ e : G.E,
      G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R rho omega
        source c sourceAtom e tiny) ≤ scale
    rw [hrestrict, Finset.mul_sum]
    calc
      (∑ e ∈ F, (n : ℝ) *
        G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R rho omega
          source c sourceAtom e tiny) ≤
          ∑ _e ∈ F, baseScale := by
        apply Finset.sum_le_sum
        intro e _
        exact G.n_mul_mixedTinyCandidateEdgeUse_le_scale
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
          hproposal0 hproposal source c sourceAtom e tiny
      _ = (F.card : ℝ) * baseScale := by simp
      _ ≤ (L : ℝ) * baseScale := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast hmult tiny.center source) hbase.le
      _ = scale := rfl

end WeightedMultigraph

end

end WeightedEdgeColoring
