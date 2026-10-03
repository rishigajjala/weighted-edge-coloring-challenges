import WeightedEdgeColoring.SubtwoMixedGraphCandidateRowCap
import WeightedEdgeColoring.SubtwoMixedGraphWeightedCandidateEdge
import WeightedEdgeColoring.SubtwoSelectorTwoSidedRows

/-!
# Source envelopes for complementary mixed candidate rows

The complement row needs a state-independent cap whose total is controlled
by physical star weight.  Large candidates charge one unit for each large
parallel edge; tiny candidates charge their actual edge weights.  Both caps
are divided by the pair-multiplicity bound, so each source coefficient is at
most one.  The remaining theorems connect the original candidate use to
these envelopes.
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

def mixedLargeSourceEnvelope (mult : ℕ) (center source : G.V) : ℝ :=
  ((G.endpointPairCell center source).filter
    (fun e ↦ β ≤ G.weight e)).card / (mult : ℝ)

def mixedTinySourceEnvelope (mult : ℕ) (center source : G.V) : ℝ :=
  (∑ e ∈ G.endpointPairCell center source,
    G.weight e) / (mult : ℝ)

def mixedCandidateSourceEnvelope (mult : ℕ) (source : G.V)
    {c : Color} (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) : ℝ :=
  match row with
  | Sum.inl large => G.mixedLargeSourceEnvelope (β := β) mult large.center source
  | Sum.inr tiny => G.mixedTinySourceEnvelope mult tiny.center source

theorem mixedLargeSourceEnvelope_nonneg (mult : ℕ) (center source : G.V) :
    0 ≤ G.mixedLargeSourceEnvelope (β := β) mult center source := by
  unfold mixedLargeSourceEnvelope
  positivity

theorem mixedTinySourceEnvelope_nonneg (mult : ℕ) (center source : G.V) :
    0 ≤ G.mixedTinySourceEnvelope mult center source := by
  unfold mixedTinySourceEnvelope
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro e _
  exact (G.weight_pos e).le

theorem mixedLargeSourceEnvelope_le_one
    {mult : ℕ} (hmult0 : 0 < mult)
    (hmult : G.PairMultiplicityAtMost mult)
    (center source : G.V) :
    G.mixedLargeSourceEnvelope (β := β) mult center source ≤ 1 := by
  unfold mixedLargeSourceEnvelope
  apply (div_le_one (by exact_mod_cast hmult0)).2
  have hcard := Finset.card_filter_le
    (s := G.endpointPairCell center source)
    (p := fun e ↦ β ≤ G.weight e)
  exact_mod_cast hcard.trans (hmult center source)

theorem mixedTinySourceEnvelope_le_one
    {mult : ℕ} (hmult0 : 0 < mult)
    (hmult : G.PairMultiplicityAtMost mult)
    (center source : G.V) :
    G.mixedTinySourceEnvelope mult center source ≤ 1 := by
  unfold mixedTinySourceEnvelope
  apply (div_le_one (by exact_mod_cast hmult0)).2
  calc
    (∑ e ∈ G.endpointPairCell center source,
      G.weight e) ≤
        ∑ _e ∈ G.endpointPairCell center source, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact G.weight_le_one e
    _ = (G.endpointPairCell center source).card := by simp
    _ ≤ mult := by exact_mod_cast hmult center source

theorem scaledMixedLargeCandidateAtomUse_le_envelope
    {mult n : ℕ} (hmult0 : 0 < mult) (hn : 0 < n)
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
    (row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c) :
    G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
      ((mult : ℝ) * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0)
      rho omega source c sourceAtom (Sum.inl row) ≤
      G.mixedLargeSourceEnvelope (β := β) mult row.center source := by
  classical
  let baseScale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let F := (G.endpointPairCell row.center source).filter
    (fun e ↦ β ≤ G.weight e)
  have hbase : 0 < baseScale :=
    mixedCandidateOrientedScale_pos hrho hs homega0 hC0
  have hmultR : (0 : ℝ) < mult := by exact_mod_cast hmult0
  have hscale : (0 : ℝ) < (mult : ℝ) * baseScale :=
    mul_pos hmultR hbase
  have hout : ∀ e ∈ (Finset.univ : Finset G.E), e ∉ F →
      G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source c sourceAtom e row = 0 := by
    intro e _ heF
    by_cases hlarge : β ≤ G.weight e
    · have hnotMatch : ¬G.EndpointPairMatches row.center source e := by
        intro hmatch
        exact heF (Finset.mem_filter.mpr
          ⟨(G.mem_endpointPairCell_iff_endpointPairMatches _ _ _).mpr hmatch,
            hlarge⟩)
      unfold mixedLargeCandidateEdgeUse EndpointPairMatches at *
      simp only [not_or] at hnotMatch
      simp [hnotMatch.1, hnotMatch.2]
    · exact G.mixedLargeCandidateEdgeUse_eq_zero_of_tiny
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row
        (lt_of_not_ge hlarge)
  have hrestrict :
      (∑ e : G.E,
        G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
          rho omega source c sourceAtom e row) =
        ∑ e ∈ F,
          G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c sourceAtom e row := by
    symm
    exact Finset.sum_subset (Finset.subset_univ F) hout
  have hsum : (n : ℝ) *
      (∑ e ∈ F, G.mixedLargeCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) ≤
        (F.card : ℝ) * baseScale := by
    rw [Finset.mul_sum]
    calc
      (∑ e ∈ F, (n : ℝ) * G.mixedLargeCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) ≤
          ∑ _e ∈ F, baseScale := by
        apply Finset.sum_le_sum
        intro e _
        exact G.n_mul_mixedLargeCandidateEdgeUse_le_scale
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
          hproposal0 hproposal source c sourceAtom e row
      _ = (F.card : ℝ) * baseScale := by simp
  change (n : ℝ) *
      (∑ e : G.E, G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source c sourceAtom e row) /
        ((mult : ℝ) * baseScale) ≤ (F.card : ℝ) / mult
  rw [hrestrict]
  have hdiv : (n : ℝ) *
      (∑ e ∈ F, G.mixedLargeCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) /
        baseScale ≤ (F.card : ℝ) :=
    (div_le_iff₀ hbase).2 hsum
  calc
    (n : ℝ) *
      (∑ e ∈ F, G.mixedLargeCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) /
        ((mult : ℝ) * baseScale) =
      ((n : ℝ) *
        (∑ e ∈ F, G.mixedLargeCandidateEdgeUse
          proposal edgeLabel qLaw R rho omega source c sourceAtom e row) /
        baseScale) / mult := by field_simp [hbase.ne', hmultR.ne']
    _ ≤ (F.card : ℝ) / mult :=
      div_le_div_of_nonneg_right hdiv hmultR.le

theorem n_mul_mixedTinyCandidateEdgeUse_le_weightScale
    {n : ℕ} (hn : 0 < n)
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
    (e : G.E)
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :
    (n : ℝ) * G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source c sourceAtom e row ≤
      G.weight e * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  let raw := mixedGraphCandidateCapacityScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let base := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hraw0 : 0 ≤ raw := by
    unfold raw mixedGraphCandidateCapacityScale
    positivity
  have hrawLe : raw ≤ base := by
    dsimp [base, mixedCandidateOrientedScale]
    have hplaces : (0 : ℝ) ≤ explicitLargeSlotBound β qstep r := by
      positivity
    nlinarith [mul_nonneg hplaces hraw0]
  have hbound : ∀
      (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
      (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c),
      (n : ℝ) * (G.weight e * G.mixedGraphTinyProductMass
        proposal edgeLabel qLaw R rho omega e c a b) ≤
        G.weight e * base := by
    intro a b
    calc
      (n : ℝ) * (G.weight e * G.mixedGraphTinyProductMass
        proposal edgeLabel qLaw R rho omega e c a b) ≤
          G.weight e * raw :=
        G.n_mul_weight_mul_mixedGraphTinyProductMass_le
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
          hproposal0 hproposal e c a b
      _ ≤ G.weight e * base :=
        mul_le_mul_of_nonneg_left hrawLe (G.weight_pos e).le
  unfold mixedTinyCandidateEdgeUse
  split
  · rename_i hmatch
    exact hbound (hmatch.1 ▸ row.candidate) (hmatch.2 ▸ sourceAtom)
  · split
    · rename_i hmatch
      exact hbound (hmatch.2 ▸ sourceAtom) (hmatch.1 ▸ row.candidate)
    · simpa using mul_nonneg (G.weight_pos e).le
          (mixedCandidateOrientedScale_nonneg (Label := Label)
            (β := β) (qstep := qstep) (r := r)
            hrho.le hs.le homega0 hC0.le)

theorem scaledMixedTinyCandidateAtomUse_le_envelope
    {mult n : ℕ} (hmult0 : 0 < mult) (hn : 0 < n)
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
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :
    G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
      ((mult : ℝ) * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0)
      rho omega source c sourceAtom (Sum.inr row) ≤
      G.mixedTinySourceEnvelope mult row.center source := by
  classical
  let baseScale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let F := G.endpointPairCell row.center source
  have hbase : 0 < baseScale :=
    mixedCandidateOrientedScale_pos hrho hs homega0 hC0
  have hmultR : (0 : ℝ) < mult := by exact_mod_cast hmult0
  have hout : ∀ e ∈ (Finset.univ : Finset G.E), e ∉ F →
      G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source c sourceAtom e row = 0 := by
    intro e _ heF
    have hnotMatch : ¬G.EndpointPairMatches row.center source e := by
      intro hmatch
      exact heF ((G.mem_endpointPairCell_iff_endpointPairMatches _ _ _).mpr hmatch)
    unfold mixedTinyCandidateEdgeUse EndpointPairMatches at *
    simp only [not_or] at hnotMatch
    simp [hnotMatch.1, hnotMatch.2]
  have hrestrict :
      (∑ e : G.E,
        G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
          rho omega source c sourceAtom e row) =
        ∑ e ∈ F,
          G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c sourceAtom e row := by
    symm
    exact Finset.sum_subset (Finset.subset_univ F) hout
  have hsum : (n : ℝ) *
      (∑ e ∈ F, G.mixedTinyCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) ≤
        (∑ e ∈ F, G.weight e) * baseScale := by
    rw [Finset.mul_sum]
    calc
      (∑ e ∈ F, (n : ℝ) * G.mixedTinyCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) ≤
          ∑ e ∈ F, G.weight e * baseScale := by
        apply Finset.sum_le_sum
        intro e _
        exact G.n_mul_mixedTinyCandidateEdgeUse_le_weightScale
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs hqstep hr0 hleft homega0 homega1 hrho hC0
          hproposal0 hproposal source c sourceAtom e row
      _ = (∑ e ∈ F, G.weight e) * baseScale := by rw [Finset.sum_mul]
  change (n : ℝ) *
      (∑ e : G.E, G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source c sourceAtom e row) /
        ((mult : ℝ) * baseScale) ≤
      (∑ e ∈ F, G.weight e) / mult
  rw [hrestrict]
  have hdiv : (n : ℝ) *
      (∑ e ∈ F, G.mixedTinyCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) /
        baseScale ≤ (∑ e ∈ F, G.weight e) :=
    (div_le_iff₀ hbase).2 hsum
  calc
    (n : ℝ) *
      (∑ e ∈ F, G.mixedTinyCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row) /
        ((mult : ℝ) * baseScale) =
      ((n : ℝ) *
        (∑ e ∈ F, G.mixedTinyCandidateEdgeUse
          proposal edgeLabel qLaw R rho omega source c sourceAtom e row) /
        baseScale) / mult := by field_simp [hbase.ne', hmultR.ne']
    _ ≤ (∑ e ∈ F, G.weight e) / mult :=
      div_le_div_of_nonneg_right hdiv hmultR.le

theorem scaledMixedCandidateAtomUse_le_envelope
    {mult n : ℕ} (hmult0 : 0 < mult) (hn : 0 < n)
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
      ((mult : ℝ) * mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0)
      rho omega source c sourceAtom row ≤
      G.mixedCandidateSourceEnvelope proposal edgeLabel qLaw R
        (β := β) mult source row := by
  cases row with
  | inl large =>
      exact G.scaledMixedLargeCandidateAtomUse_le_envelope
        proposal edgeLabel qLaw R hmult0 hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        hproposal0 hproposal source c sourceAtom large
  | inr tiny =>
      exact G.scaledMixedTinyCandidateAtomUse_le_envelope
        proposal edgeLabel qLaw R hmult0 hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        hproposal0 hproposal source c sourceAtom tiny

end WeightedMultigraph

end

end WeightedEdgeColoring
