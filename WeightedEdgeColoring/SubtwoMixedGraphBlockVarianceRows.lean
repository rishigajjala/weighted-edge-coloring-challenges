import WeightedEdgeColoring.SubtwoMixedGraphBlockResidual

/-!
# Two-level selector rows for mixed block variance

A candidate row fixes the state at one center/block.  An opposite endpoint
contributes the weighted edge squares for that block.  The conditional
candidate mean is then used as a self row, as in the ordinary multigraph
block-variance selector.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {B k : ℕ} {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, (Fin B × Fin k) →
  Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

abbrev MixedBlockVarianceCandidateRow :=
  Σ _center : G.V, Σ b : Fin B,
    G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b

def mixedBlockVarianceCandidateEdgeUse
    (rho omega : ℝ) (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (e : G.E)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) : ℝ :=
  if hblock : source.2 = row.2.1 then
    if row.1 = G.fst e ∧ source.1 = G.snd e then
      G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e row.2.1
        row.2.2 (hblock ▸ state)
    else if row.1 = G.snd e ∧ source.1 = G.fst e then
      G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e row.2.1
        (hblock ▸ state) row.2.2
    else 0
  else 0

def rawMixedBlockVarianceCandidateUse
    (rho omega : ℝ) (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) : ℝ :=
  ∑ e : G.E,
    G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source state e row

theorem rawMixedBlockVarianceCandidateUse_nonneg
    (rho omega : ℝ) (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    0 ≤ G.rawMixedBlockVarianceCandidateUse
      proposal edgeLabel qLaw R rho omega source state row := by
  unfold rawMixedBlockVarianceCandidateUse
  apply Finset.sum_nonneg
  intro e _
  unfold mixedBlockVarianceCandidateEdgeUse
  split <;> try exact le_rfl
  split
  · exact G.mixedBlockVariance_nonneg
      proposal edgeLabel qLaw R _ _ _ _ _ _
  · split
    · exact G.mixedBlockVariance_nonneg
        proposal edgeLabel qLaw R _ _ _ _ _ _
    · exact le_rfl

theorem rawMixedBlockVarianceCandidateUse_eq_zero_of_block_ne
    (rho omega : ℝ) (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R)
    (hblock : source.2 ≠ row.2.1) :
    G.rawMixedBlockVarianceCandidateUse
      proposal edgeLabel qLaw R rho omega source state row = 0 := by
  unfold rawMixedBlockVarianceCandidateUse
  apply Finset.sum_eq_zero
  intro e _
  simp [mixedBlockVarianceCandidateEdgeUse, hblock]

def mixedBlockVarianceUnitScale (n : ℕ) (rho omega C0 : ℝ) : ℝ :=
  ((k : ℝ) *
    (mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r)
      rho s omega C0 + rho * s * C0) / (n : ℝ)) ^ 2

theorem mixedBlockVarianceUnitScale_pos
    {n : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hs : 0 < s)
    (homega0 : 0 < omega) (hrho : 0 < rho) (hC0 : 0 < C0) :
    0 < mixedBlockVarianceUnitScale (k := k) (s := s)
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      n rho omega C0 := by
  unfold mixedBlockVarianceUnitScale
  have hU : 0 ≤ mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r)
      rho s omega C0 :=
    mixedCandidateOrientedScale_nonneg (Label := Label)
      (β := β) (qstep := qstep) (r := r)
      hrho.le hs.le homega0 hC0.le
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem mixedBlockVarianceCandidateEdgeUse_div_le_indicator
    (rho omega unitScale : ℝ) (hunit : 0 < unitScale)
    (hvariance : ∀ b
      (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b) (e : G.E),
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right ≤ G.weight e * unitScale)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (e : G.E)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source state e row / unitScale ≤
      if source.2 = row.2.1 ∧
          G.EndpointPairMatches row.1 source.1 e then
        G.weight e else 0 := by
  by_cases hb : source.2 = row.2.1
  · by_cases hm : G.EndpointPairMatches row.1 source.1 e
    · rw [if_pos ⟨hb, hm⟩]
      rcases hm with hm | hm
      · have hterm : G.mixedBlockVarianceCandidateEdgeUse
            proposal edgeLabel qLaw R rho omega source state e row =
            G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e
              row.2.1 row.2.2 (hb ▸ state) := by
          simp [mixedBlockVarianceCandidateEdgeUse, hb, hm.1, hm.2]
        rw [hterm]
        exact (div_le_iff₀ hunit).2 (hvariance _ _ _ e)
      · have hnotFirst :
            ¬(row.1 = G.fst e ∧ source.1 = G.snd e) := by
          intro hfirst
          exact G.noLoop e (hfirst.1.symm.trans hm.1)
        have hterm : G.mixedBlockVarianceCandidateEdgeUse
            proposal edgeLabel qLaw R rho omega source state e row =
            G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e
              row.2.1 (hb ▸ state) row.2.2 := by
          rw [mixedBlockVarianceCandidateEdgeUse, dif_pos hb,
            if_neg hnotFirst, if_pos ⟨hm.1, hm.2⟩]
        rw [hterm]
        exact (div_le_iff₀ hunit).2 (hvariance _ _ _ e)
    · rw [if_neg (by simp [hb, hm])]
      unfold EndpointPairMatches at hm
      simp only [not_or] at hm
      simp [mixedBlockVarianceCandidateEdgeUse, hb, hm.1, hm.2]
  · rw [if_neg (by simp [hb])]
    simp [mixedBlockVarianceCandidateEdgeUse, hb]

theorem mixedBlockVarianceCandidateEdgeUse_le_unitScale
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
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (e : G.E)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source state e row ≤
      mixedBlockVarianceUnitScale (k := k) (s := s) (Label := Label)
        (β := β) (qstep := qstep) (r := r) n rho omega C0 := by
  have hscale0 : 0 ≤ mixedBlockVarianceUnitScale (k := k) (s := s) (Label := Label)
      (β := β) (qstep := qstep) (r := r) n rho omega C0 :=
    sq_nonneg _
  have hbound : ∀ b
      (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right ≤
        mixedBlockVarianceUnitScale (k := k) (s := s) (Label := Label)
          (β := β) (qstep := qstep) (r := r) n rho omega C0 := by
    intro b left right
    have h := G.mixedBlockVariance_le_pairScale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal e b left right
    exact h.trans (by
      unfold mixedBlockVarianceUnitScale
      simpa using
        (mul_le_mul_of_nonneg_right (G.weight_le_one e) (sq_nonneg _)))
  unfold mixedBlockVarianceCandidateEdgeUse
  split
  · split
    · exact hbound _ _ _
    · split
      · exact hbound _ _ _
      · exact hscale0
  · exact hscale0

theorem mixedBlockVarianceCandidateEdgeUse_eq_zero_of_not_pair
    (rho omega : ℝ) (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (e : G.E)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R)
    (hnot : e ∉ G.endpointPairCell row.1 source.1) :
    G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
      rho omega source state e row = 0 := by
  have hnotMatch : ¬G.EndpointPairMatches row.1 source.1 e := by
    intro hmatch
    exact hnot ((G.mem_endpointPairCell_iff_endpointPairMatches _ _ _).mpr hmatch)
  unfold mixedBlockVarianceCandidateEdgeUse EndpointPairMatches at *
  simp only [not_or] at hnotMatch
  by_cases hb : source.2 = row.2.1
  · simp [hb, hnotMatch.1, hnotMatch.2]
  · simp [hb]

theorem rawMixedBlockVarianceCandidateUse_le_of_edgeCap
    {mult : ℕ} (hmult : G.PairMultiplicityAtMost mult)
    (rho omega unitScale : ℝ) (hunit0 : 0 ≤ unitScale)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R)
    (hedge : ∀ e, G.mixedBlockVarianceCandidateEdgeUse
      proposal edgeLabel qLaw R rho omega source state e row ≤ unitScale) :
    G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
      rho omega source state row ≤ (mult : ℝ) * unitScale := by
  let F := G.endpointPairCell row.1 source.1
  have hrestrict :
      (∑ e : G.E,
        G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
          rho omega source state e row) =
        ∑ e ∈ F,
          G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source state e row := by
    symm
    apply Finset.sum_subset (Finset.subset_univ F)
    intro e _ heF
    exact G.mixedBlockVarianceCandidateEdgeUse_eq_zero_of_not_pair
      proposal edgeLabel qLaw R rho omega source state e row heF
  unfold rawMixedBlockVarianceCandidateUse
  rw [hrestrict]
  calc
    (∑ e ∈ F,
      G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source state e row) ≤ ∑ _e ∈ F, unitScale := by
      apply Finset.sum_le_sum
      intro e _
      exact hedge e
    _ = (F.card : ℝ) * unitScale := by simp
    _ ≤ (mult : ℝ) * unitScale :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmult row.1 source.1)
        hunit0

theorem rawMixedBlockVarianceCandidateUse_le_pairScale
    {mult n : ℕ} (hmult : G.PairMultiplicityAtMost mult) (hn : 0 < n)
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
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
      rho omega source state row ≤
      (mult : ℝ) *
        mixedBlockVarianceUnitScale (k := k) (s := s) (Label := Label)
          (β := β) (qstep := qstep) (r := r) n rho omega C0 := by
  exact G.rawMixedBlockVarianceCandidateUse_le_of_edgeCap
    proposal edgeLabel qLaw R hmult rho omega _ (sq_nonneg _)
    source state row (fun e ↦
      G.mixedBlockVarianceCandidateEdgeUse_le_unitScale
        proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        hproposal0 hproposal source state e row)

def conditionalMixedBlockVariance (rho omega : ℝ)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) : ℝ :=
  ∑ source : G.V × Fin B,
    ∑ state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2,
      G.mixedBlockProbability proposal edgeLabel qLaw R
        omega source.1 source.2 state *
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row

theorem conditionalMixedBlockVariance_nonneg
    (rho omega : ℝ)
    (hprob0 : ∀ (source : G.V × Fin B)
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R source.2),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega source.1 source.2 state)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    0 ≤ G.conditionalMixedBlockVariance
      proposal edgeLabel qLaw R rho omega row := by
  unfold conditionalMixedBlockVariance
  apply Finset.sum_nonneg
  intro source _
  apply Finset.sum_nonneg
  intro state _
  exact mul_nonneg (hprob0 source state)
    (G.rawMixedBlockVarianceCandidateUse_nonneg
      proposal edgeLabel qLaw R rho omega source state row)

theorem conditionalMixedBlockVariance_le_of_rowCap
    (rho omega rowCap : ℝ)
    (hprob0 : ∀ (source : G.V × Fin B)
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R source.2),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega source.1 source.2 state)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R)
    (hcap : ∀ source state,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row ≤ rowCap) :
    G.conditionalMixedBlockVariance
      proposal edgeLabel qLaw R rho omega row ≤
      (Fintype.card G.V : ℝ) * rowCap := by
  unfold conditionalMixedBlockVariance
  have hsource : ∀ source : G.V × Fin B,
      (∑ state : G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R source.2,
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2 state *
        G.rawMixedBlockVarianceCandidateUse
          proposal edgeLabel qLaw R rho omega source state row) ≤
        if source.2 = row.2.1 then rowCap else 0 := by
    intro source
    by_cases hb : source.2 = row.2.1
    · simp only [hb, ↓reduceIte]
      calc
        (∑ state,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2 state *
          G.rawMixedBlockVarianceCandidateUse
            proposal edgeLabel qLaw R rho omega source state row) ≤
          ∑ state,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega source.1 source.2 state * rowCap := by
          apply Finset.sum_le_sum
          intro state _
          exact mul_le_mul_of_nonneg_left (hcap source state)
            (hprob0 source state)
        _ = rowCap := by
          rw [← Finset.sum_mul,
            G.sum_mixedBlockProbability proposal edgeLabel qLaw R]
          ring
    · simp only [hb, ↓reduceIte]
      have hzero : (∑ state,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2 state *
          G.rawMixedBlockVarianceCandidateUse
            proposal edgeLabel qLaw R rho omega source state row) = 0 := by
        apply Finset.sum_eq_zero
        intro state _
        rw [G.rawMixedBlockVarianceCandidateUse_eq_zero_of_block_ne
          proposal edgeLabel qLaw R rho omega source state row hb]
        ring
      exact hzero.le
  calc
    (∑ source : G.V × Fin B,
      ∑ state,
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2 state *
        G.rawMixedBlockVarianceCandidateUse
          proposal edgeLabel qLaw R rho omega source state row) ≤
        ∑ source : G.V × Fin B,
          if source.2 = row.2.1 then rowCap else 0 := by
      apply Finset.sum_le_sum
      intro source _
      exact hsource source
    _ = (Fintype.card G.V : ℝ) * rowCap := by
      rw [Fintype.sum_prod_type]
      simp

theorem conditionalMixedBlockVariance_le_pairScale
    {mult n : ℕ} (hmult : G.PairMultiplicityAtMost mult) (hn : 0 < n)
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
    (hprob0 : ∀ (source : G.V × Fin B)
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R source.2),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega source.1 source.2 state)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    G.conditionalMixedBlockVariance
      proposal edgeLabel qLaw R rho omega row ≤
      (Fintype.card G.V : ℝ) * (mult : ℝ) *
        mixedBlockVarianceUnitScale (k := k) (s := s) (Label := Label)
          (β := β) (qstep := qstep) (r := r) n rho omega C0 := by
  have h := G.conditionalMixedBlockVariance_le_of_rowCap
    proposal edgeLabel qLaw R rho omega
    ((mult : ℝ) * mixedBlockVarianceUnitScale
      (k := k) (s := s) (Label := Label)
      (β := β) (qstep := qstep) (r := r) n rho omega C0)
    hprob0 row
    (fun source state ↦ G.rawMixedBlockVarianceCandidateUse_le_pairScale
      proposal edgeLabel qLaw R hmult hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal source state row)
  nlinarith [h]

theorem conditionalMixedBlockVariance_eq_edge_sum
    (rho omega : ℝ) (v : G.V) (b : Fin B)
    (centerState : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b) :
    G.conditionalMixedBlockVariance proposal edgeLabel qLaw R rho omega
        ⟨v, b, centerState⟩ =
      ∑ e : G.E,
        if v = G.fst e then
          ∑ oppositeState : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.snd e) b oppositeState *
              G.mixedBlockVariance proposal edgeLabel qLaw R
                rho omega e b centerState oppositeState
        else if v = G.snd e then
          ∑ oppositeState : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.fst e) b oppositeState *
              G.mixedBlockVariance proposal edgeLabel qLaw R
                rho omega e b oppositeState centerState
        else 0 := by
  unfold conditionalMixedBlockVariance rawMixedBlockVarianceCandidateUse
  simp_rw [Finset.mul_sum]
  calc
    (∑ source : G.V × Fin B,
      ∑ sourceState,
        ∑ e : G.E,
          G.mixedBlockProbability proposal edgeLabel qLaw R
              omega source.1 source.2 sourceState *
            G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source sourceState e ⟨v, b, centerState⟩) =
      ∑ source : G.V × Fin B, ∑ e : G.E, ∑ sourceState,
        G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2 sourceState *
          G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source sourceState e ⟨v, b, centerState⟩ := by
      apply Finset.sum_congr rfl
      intro source _
      rw [Finset.sum_comm]
    _ = ∑ e : G.E, ∑ source : G.V × Fin B, ∑ sourceState,
        G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2 sourceState *
          G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source sourceState e ⟨v, b, centerState⟩ := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.sum_prod_type]
      by_cases hfst : v = G.fst e
      · subst v
        have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [mixedBlockVarianceCandidateEdgeUse, hne]
      · by_cases hsnd : v = G.snd e
        · subst v
          have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [mixedBlockVarianceCandidateEdgeUse, hfst, hne]
        · simp [mixedBlockVarianceCandidateEdgeUse, hfst, hsnd]

theorem conditionalMixedBlockVariance_le_starWeight
    (rho omega unitScale : ℝ) (hscale0 : 0 ≤ unitScale)
    (hvariance : ∀ b
      (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b) (e : G.E),
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right ≤ G.weight e * unitScale)
    (hprob0 : ∀ v b
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    G.conditionalMixedBlockVariance
      proposal edgeLabel qLaw R rho omega row ≤
      unitScale * G.starWeight row.1 := by
  rcases row with ⟨v, b, centerState⟩
  rw [G.conditionalMixedBlockVariance_eq_edge_sum
    proposal edgeLabel qLaw R rho omega v b centerState]
  have hedge : ∀ e : G.E,
      (if v = G.fst e then
        ∑ oppositeState : G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R b,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega (G.snd e) b oppositeState *
            G.mixedBlockVariance proposal edgeLabel qLaw R
              rho omega e b centerState oppositeState
      else if v = G.snd e then
        ∑ oppositeState : G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R b,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega (G.fst e) b oppositeState *
            G.mixedBlockVariance proposal edgeLabel qLaw R
              rho omega e b oppositeState centerState
      else 0) ≤ if G.Inc v e then G.weight e * unitScale else 0 := by
    intro e
    by_cases hfst : v = G.fst e
    · subst v
      simp only [eq_self, if_true, WeightedMultigraph.Inc, true_or]
      calc
        _ ≤ ∑ oppositeState,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.snd e) b oppositeState *
            (G.weight e * unitScale) := by
          apply Finset.sum_le_sum
          intro state _
          exact mul_le_mul_of_nonneg_left (hvariance b centerState state e)
            (hprob0 _ _ state)
        _ = G.weight e * unitScale := by
          rw [← Finset.sum_mul,
            G.sum_mixedBlockProbability proposal edgeLabel qLaw R]
          ring
    · by_cases hsnd : v = G.snd e
      · subst v
        simp only [hfst, if_false, eq_self, if_true,
          WeightedMultigraph.Inc, or_true]
        calc
          _ ≤ ∑ oppositeState,
              G.mixedBlockProbability proposal edgeLabel qLaw R
                omega (G.fst e) b oppositeState *
              (G.weight e * unitScale) := by
            apply Finset.sum_le_sum
            intro state _
            exact mul_le_mul_of_nonneg_left (hvariance b state centerState e)
              (hprob0 _ _ state)
          _ = G.weight e * unitScale := by
            rw [← Finset.sum_mul,
              G.sum_mixedBlockProbability proposal edgeLabel qLaw R]
            ring
      · have hinc : ¬G.Inc v e := by
          intro h
          rcases h with h | h
          · exact hfst h.symm
          · exact hsnd h.symm
        simp [hfst, hsnd, hinc]
  calc
    _ ≤ ∑ e : G.E, if G.Inc v e then G.weight e * unitScale else 0 :=
      Finset.sum_le_sum fun e _ ↦ hedge e
    _ = unitScale * G.starWeight v := by
      calc
        _ = ∑ e ∈ Finset.univ.filter (G.Inc v),
              G.weight e * unitScale := by rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge v, G.weight e.1 * unitScale := by
          exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
            (by intro e; simp) (fun e ↦ G.weight e * unitScale)
        _ = _ := by unfold starWeight; rw [← Finset.sum_mul]; ring

theorem sum_rawMixedBlockVarianceCandidateUse_le_of_rowCap
    (rho omega rowCap : ℝ)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (hrowCap : ∀ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row ≤ rowCap) :
    (∑ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row) ≤
      (Fintype.card G.V : ℝ) *
        (Fintype.card (G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R source.2) : ℝ) * rowCap := by
  calc
    (∑ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row) ≤
        ∑ row : G.MixedBlockVarianceCandidateRow
          proposal edgeLabel qLaw R,
          if source.2 = row.2.1 then rowCap else 0 := by
      apply Finset.sum_le_sum
      intro row _
      by_cases hb : source.2 = row.2.1
      · simpa [hb] using hrowCap row
      · simp [hb, G.rawMixedBlockVarianceCandidateUse_eq_zero_of_block_ne
          proposal edgeLabel qLaw R rho omega source state row hb]
    _ = (Fintype.card G.V : ℝ) *
        (Fintype.card (G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R source.2) : ℝ) * rowCap := by
      have hinner (b : Fin B) :
          (∑ st : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
            if source.2 = b then rowCap else 0) =
          (Fintype.card (G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b) : ℝ) *
            (if source.2 = b then rowCap else 0) := by
        simp
      have hcard (b : Fin B) :
          Fintype.card (G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b) =
          Fintype.card (G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R source.2) := rfl
      rw [Fintype.sum_sigma]
      simp only [Fintype.sum_sigma]
      simp_rw [hinner, hcard]
      simp
      ring

theorem sum_rawMixedBlockVarianceCandidateUse_le_sparseColumn
    {mult n : ℕ} (hmult : G.PairMultiplicityAtMost mult) (hn : 0 < n)
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
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row) ≤
      (Fintype.card G.V : ℝ) *
        (Fintype.card (G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R source.2) : ℝ) *
        ((mult : ℝ) * mixedBlockVarianceUnitScale
          (k := k) (s := s) (Label := Label)
          (β := β) (qstep := qstep) (r := r) n rho omega C0) := by
  exact G.sum_rawMixedBlockVarianceCandidateUse_le_of_rowCap
    proposal edgeLabel qLaw R rho omega _ source state
    (fun row ↦ G.rawMixedBlockVarianceCandidateUse_le_pairScale
      proposal edgeLabel qLaw R hmult hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal source state row)

private theorem sum_mixedBlockVarianceCandidateRows_edge_le
    (rho omega unitScale : ℝ) (hunit : 0 < unitScale)
    (hvariance : ∀ b
      (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b) (e : G.E),
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right ≤ G.weight e * unitScale)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) (e : G.E) :
    (∑ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source state e row / unitScale) ≤
      if G.Inc source.1 e then
        ((mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * G.weight e
      else 0 := by
  calc
    _ ≤ ∑ row : G.MixedBlockVarianceCandidateRow
        proposal edgeLabel qLaw R,
        if source.2 = row.2.1 ∧
            G.EndpointPairMatches row.1 source.1 e then
          G.weight e else 0 :=
      Finset.sum_le_sum fun row _ ↦
        G.mixedBlockVarianceCandidateEdgeUse_div_le_indicator
          proposal edgeLabel qLaw R rho omega unitScale hunit
          hvariance source state e row
    _ = if G.Inc source.1 e then
        ((mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * G.weight e
      else 0 := by
      simp only [Fintype.sum_sigma]
      by_cases hfst : source.1 = G.fst e
      · have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [EndpointPairMatches, WeightedMultigraph.Inc,
          hne, hfst, FiniteDependentWordPadding.packedWordState_card,
          ite_and]
      · by_cases hsnd : source.1 = G.snd e
        · have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [EndpointPairMatches, WeightedMultigraph.Inc,
            hfst, hsnd, hne,
            FiniteDependentWordPadding.packedWordState_card, ite_and]
        · have hinc : ¬G.Inc source.1 e := by
            intro h
            rcases h with h | h
            · exact hfst h.symm
            · exact hsnd h.symm
          simp [EndpointPairMatches, hfst, hsnd, hinc, ite_and]

theorem sum_rawMixedBlockVarianceCandidateUse_le_starWeight
    (rho omega unitScale : ℝ) (hunit : 0 < unitScale)
    (hvariance : ∀ b
      (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b) (e : G.E),
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right ≤ G.weight e * unitScale)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row /
          unitScale) ≤
      ((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) *
        G.starWeight source.1 := by
  unfold rawMixedBlockVarianceCandidateUse
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ e : G.E, if G.Inc source.1 e then
          ((mixedGraphAtomBound (Label := Label)
            (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * G.weight e
        else 0 :=
      Finset.sum_le_sum fun e _ ↦
        G.sum_mixedBlockVarianceCandidateRows_edge_le
          proposal edgeLabel qLaw R rho omega unitScale hunit
          hvariance source state e
    _ = ((mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) *
          G.starWeight source.1 := by
      calc
        _ = ∑ e ∈ Finset.univ.filter (G.Inc source.1),
              ((mixedGraphAtomBound (Label := Label)
                (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) *
                G.weight e := by rw [Finset.sum_filter]
        _ = ∑ e : G.StarEdge source.1,
              ((mixedGraphAtomBound (Label := Label)
                (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) *
                G.weight e.1 := by
          exact Finset.sum_subtype (Finset.univ.filter (G.Inc source.1))
            (by intro e; simp)
            (fun e ↦ ((mixedGraphAtomBound (Label := Label)
              (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) *
              G.weight e)
        _ = _ := by unfold starWeight; rw [Finset.mul_sum]

theorem conditionalMixedBlockVariance_le_n_unitScale
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
    (hstar : ∀ v, G.starWeight v ≤ n)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
      rho omega row ≤ (n : ℝ) *
        mixedBlockVarianceUnitScale (k := k) (s := s) (Label := Label)
          (β := β) (qstep := qstep) (r := r) n rho omega C0 := by
  let unitScale := mixedBlockVarianceUnitScale (k := k) (s := s)
    (Label := Label) (β := β) (qstep := qstep) (r := r)
    n rho omega C0
  have hvar : ∀ b
      (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b) (e : G.E),
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right ≤ G.weight e * unitScale := by
    intro b left right e
    exact G.mixedBlockVariance_le_pairScale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal e b left right
  have hprob : ∀ v b
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state := by
    intro v b state
    exact G.paddedMixedGraphWordProbability_nonneg
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b)
      (fun v i S ↦ hq0 v (b, i) S)
      (fun v i ↦ hqsum v (b, i))
      (fun v i S ↦ hqsingle v (b, i) S)
      hs hqstep hr0 hleft homega0 homega1 v state
  have hrow := G.conditionalMixedBlockVariance_le_starWeight
    proposal edgeLabel qLaw R rho omega unitScale (sq_nonneg _)
    hvar hprob row
  calc
    _ ≤ unitScale * G.starWeight row.1 := hrow
    _ ≤ unitScale * n :=
      mul_le_mul_of_nonneg_left (hstar row.1) (sq_nonneg _)
    _ = n * unitScale := by ring

theorem sum_rawMixedBlockVarianceCandidateUse_le_n_stateCount
    {n : ℕ} (hn : 0 < n) (hk : 0 < k)
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
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
        rho omega source state row /
        mixedBlockVarianceUnitScale (k := k) (s := s) (Label := Label)
          (β := β) (qstep := qstep) (r := r) n rho omega C0) ≤
      ((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n := by
  let unitScale := mixedBlockVarianceUnitScale (k := k) (s := s)
    (Label := Label) (β := β) (qstep := qstep) (r := r)
    n rho omega C0
  have hvar : ∀ b
      (left right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b) (e : G.E),
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right ≤ G.weight e * unitScale := by
    intro b left right e
    exact G.mixedBlockVariance_le_pairScale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
      hproposal0 hproposal e b left right
  have hcol := G.sum_rawMixedBlockVarianceCandidateUse_le_starWeight
    proposal edgeLabel qLaw R rho omega unitScale
    (mixedBlockVarianceUnitScale_pos (Label := Label) (k := k)
      (s := s) (β := β) (qstep := qstep) (r := r)
      hn hk hs homega0 hrho hC0)
    hvar source state
  exact hcol.trans (mul_le_mul_of_nonneg_left (hstar source.1) (by positivity))

theorem sum_rawMixedBlockVarianceCandidateUse_div_mul_le
    {L : ℕ} (hL : 0 < L)
    (rho omega unitScale bound : ℝ) (hunit : 0 < unitScale)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (hcolumn :
      (∑ row : G.MixedBlockVarianceCandidateRow
        proposal edgeLabel qLaw R,
        G.rawMixedBlockVarianceCandidateUse
          proposal edgeLabel qLaw R rho omega source state row /
          unitScale) ≤ bound) :
    (∑ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row /
        ((L : ℝ) * unitScale)) ≤ bound := by
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hscaled : (0 : ℝ) < (L : ℝ) * unitScale := by positivity
  have hbaseScaled : unitScale ≤ (L : ℝ) * unitScale := by
    nlinarith [hunit.le]
  calc
    _ ≤ ∑ row : G.MixedBlockVarianceCandidateRow
        proposal edgeLabel qLaw R,
        G.rawMixedBlockVarianceCandidateUse
          proposal edgeLabel qLaw R rho omega source state row /
          unitScale := by
      apply Finset.sum_le_sum
      intro row _
      exact div_le_div_of_nonneg_left
        (G.rawMixedBlockVarianceCandidateUse_nonneg
          proposal edgeLabel qLaw R rho omega source state row)
        hunit hbaseScaled
    _ ≤ bound := hcolumn

def mixedBlockVarianceSelfUse (rho omega selfScale : ℝ)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (v : G.V) : ℝ :=
  if source.1 = v then
    G.conditionalMixedBlockVariance proposal edgeLabel qLaw R rho omega
      ⟨v, source.2, state⟩ / selfScale
  else 0

abbrev MixedBlockVarianceRow :=
  G.MixedBlockVarianceCandidateRow proposal edgeLabel qLaw R ⊕ G.V

def mixedBlockVarianceUse (rho omega pairScale selfScale : ℝ)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceRow proposal edgeLabel qLaw R) : ℝ :=
  match row with
  | Sum.inl candidate =>
      G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
        rho omega source state candidate / pairScale
  | Sum.inr v =>
      G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
        rho omega selfScale source state v

theorem mixedBlockVarianceSelfUse_nonneg
    (rho omega selfScale : ℝ) (hself : 0 < selfScale)
    (hprob0 : ∀ v b
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (v : G.V) :
    0 ≤ G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
      rho omega selfScale source state v := by
  unfold mixedBlockVarianceSelfUse
  split
  · exact div_nonneg
      (G.conditionalMixedBlockVariance_nonneg
        proposal edgeLabel qLaw R rho omega
        (fun src st ↦ hprob0 src.1 src.2 st) _) hself.le
  · exact le_rfl

theorem sum_mixedBlockVarianceSelfUse_le_one
    (rho omega unitScale : ℝ) (hunit : 0 < unitScale)
    {n : ℕ} (hn : 0 < n)
    (hrow : ∀ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega row ≤ (n : ℝ) * unitScale)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ v, G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
      rho omega ((n : ℝ) * unitScale) source state v) ≤ 1 := by
  have hscale : (0 : ℝ) < (n : ℝ) * unitScale := by
    exact mul_pos (by exact_mod_cast hn) hunit
  rw [Finset.sum_eq_single source.1]
  · unfold mixedBlockVarianceSelfUse
    rw [if_pos rfl]
    exact (div_le_one hscale).2 (hrow ⟨source.1, source.2, state⟩)
  · intro v _ hv
    simp [mixedBlockVarianceSelfUse, hv, Ne.symm hv]
  · simp

theorem mixedBlockVarianceUse_nonneg
    (rho omega pairScale selfScale : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (hprob0 : ∀ v b
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceRow proposal edgeLabel qLaw R) :
    0 ≤ G.mixedBlockVarianceUse proposal edgeLabel qLaw R
      rho omega pairScale selfScale source state row := by
  rcases row with candidate | v
  · exact div_nonneg
      (G.rawMixedBlockVarianceCandidateUse_nonneg
        proposal edgeLabel qLaw R rho omega source state candidate)
      hpair.le
  · exact G.mixedBlockVarianceSelfUse_nonneg
      proposal edgeLabel qLaw R rho omega selfScale hself
      hprob0 source state v

theorem mixedBlockVarianceUse_le_one
    (rho omega pairScale selfScale : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (hraw : ∀ source state row,
      G.rawMixedBlockVarianceCandidateUse
        proposal edgeLabel qLaw R rho omega source state row ≤ pairScale)
    (hconditional : ∀ row,
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega row ≤ selfScale)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockVarianceRow proposal edgeLabel qLaw R) :
    G.mixedBlockVarianceUse proposal edgeLabel qLaw R
      rho omega pairScale selfScale source state row ≤ 1 := by
  cases row with
  | inl candidate =>
      change G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
        rho omega source state candidate / pairScale ≤ 1
      exact (div_le_one hpair).2 (hraw source state candidate)
  | inr v =>
      change G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
        rho omega selfScale source state v ≤ 1
      unfold mixedBlockVarianceSelfUse
      split
      · exact (div_le_one hself).2 (hconditional _)
      · norm_num

theorem sum_mixedBlockVarianceUse_le_column
    (rho omega pairScale selfScale columnBound : ℝ)
    (hcolumn : ∀ source state,
      (∑ row : G.MixedBlockVarianceCandidateRow
        proposal edgeLabel qLaw R,
        G.rawMixedBlockVarianceCandidateUse
          proposal edgeLabel qLaw R rho omega source state row /
          pairScale) ≤ columnBound)
    (hself : ∀ source state,
      (∑ v, G.mixedBlockVarianceSelfUse
        proposal edgeLabel qLaw R rho omega selfScale
        source state v) ≤ 1)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ row : G.MixedBlockVarianceRow proposal edgeLabel qLaw R,
      G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale source state row) ≤
      columnBound + 1 := by
  rw [Fintype.sum_sum_type]
  exact add_le_add (hcolumn source state) (hself source state)

theorem mixedBlockVarianceUse_candidate_rowMean_eq
    (rho omega pairScale selfScale : ℝ)
    (row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale) (Sum.inl row) =
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega row / pairScale := by
  unfold FiniteCategoricalSelection.rowMean
    conditionalMixedBlockVariance
  simp_rw [mixedBlockVarianceUse, ← mul_div_assoc, Finset.sum_div]

theorem mixedBlockVarianceUse_self_rowMean_le
    (rho omega pairScale selfScale : ℝ)
    (hselfScale : 0 < selfScale)
    (hprob0 : ∀ v b
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state)
    (hself : ∀ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega row ≤ selfScale)
    (v : G.V) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale) (Sum.inr v) ≤
      (B : ℝ) := by
  unfold FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : Fin B,
        ∑ state : G.MixedGraphPackedBlockState
          proposal edgeLabel qLaw R b,
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega v b state *
            (G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
              rho omega ⟨v, b, state⟩ / selfScale) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_eq_single v]
      · simp [mixedBlockVarianceUse, mixedBlockVarianceSelfUse]
      · intro w _ hw
        simp [mixedBlockVarianceUse, mixedBlockVarianceSelfUse,
          hw, Ne.symm hw]
      · simp
    _ ≤ ∑ _b : Fin B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      calc
        _ ≤ ∑ state : G.MixedGraphPackedBlockState
            proposal edgeLabel qLaw R b,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega v b state * 1 := by
          apply Finset.sum_le_sum
          intro state _
          exact mul_le_mul_of_nonneg_left
            ((div_le_one hselfScale).2 (hself ⟨v, b, state⟩))
            (hprob0 v b state)
        _ = 1 := by
          rw [← Finset.sum_mul,
            G.sum_mixedBlockProbability proposal edgeLabel qLaw R]
          ring
    _ = B := by simp

/-- One block contributes its mean label count at a vertex.  The `1/k`
normalization keeps every categorical coefficient at most one. -/
def mixedBlockLabelUse (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.V × Option Label) : ℝ :=
  if source.1 = row.1 then
    (∑ i : Fin k,
      if G.decodeMixedGraphLabel
          (G.mixedBlockProposal proposal source.2) edgeLabel
          (G.mixedBlockLaw qLaw source.2)
          (G.mixedBlockRealization proposal edgeLabel qLaw R source.2)
          source.1 state i = row.2 then (1 : ℝ) else 0) / (k : ℝ)
  else 0

theorem mixedBlockLabelUse_nonneg (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.V × Option Label) :
    0 ≤ G.mixedBlockLabelUse proposal edgeLabel qLaw R
      source state row := by
  unfold mixedBlockLabelUse
  split
  · apply div_nonneg _ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro i _
    split <;> positivity
  · exact le_rfl

theorem mixedBlockLabelUse_le_one (hk : 0 < k)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.V × Option Label) :
    G.mixedBlockLabelUse proposal edgeLabel qLaw R
      source state row ≤ 1 := by
  unfold mixedBlockLabelUse
  split
  · apply (div_le_one (by exact_mod_cast hk)).2
    calc
      (∑ i : Fin k,
        if G.decodeMixedGraphLabel
            (G.mixedBlockProposal proposal source.2) edgeLabel
            (G.mixedBlockLaw qLaw source.2)
            (G.mixedBlockRealization proposal edgeLabel qLaw R source.2)
            source.1 state i = row.2 then (1 : ℝ) else 0) ≤
          ∑ _i : Fin k, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split <;> norm_num
      _ = k := by simp
  · norm_num

theorem mixedBlockLabel_rowMean_le_blocks
    (hk : 0 < k) (omega : ℝ)
    (hprob0 : ∀ v b
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state)
    (row : G.V × Option Label) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockLabelUse proposal edgeLabel qLaw R) row ≤
      (B : ℝ) := by
  unfold FiniteCategoricalSelection.rowMean
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ ≤ ∑ _b : Fin B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      rw [Finset.sum_eq_single row.1]
      · calc
          _ ≤ ∑ state : G.MixedGraphPackedBlockState
              proposal edgeLabel qLaw R b,
              G.mixedBlockProbability proposal edgeLabel qLaw R
                omega row.1 b state * 1 := by
            apply Finset.sum_le_sum
            intro state _
            exact mul_le_mul_of_nonneg_left
              (G.mixedBlockLabelUse_le_one proposal edgeLabel qLaw R
                hk (row.1, b) state row)
              (hprob0 row.1 b state)
          _ = 1 := by
            rw [← Finset.sum_mul,
              G.sum_mixedBlockProbability proposal edgeLabel qLaw R]
            ring
      · intro v _ hv
        simp [mixedBlockLabelUse, hv, Ne.symm hv]
      · simp
    _ = B := by simp

theorem sum_mixedBlockLabelUse_le_card
    (hk : 0 < k)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ row : G.V × Option Label,
      G.mixedBlockLabelUse proposal edgeLabel qLaw R
        source state row) ≤ (Fintype.card (Option Label) : ℝ) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single source.1]
  · calc
      _ ≤ ∑ _label : Option Label, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro label _
        exact G.mixedBlockLabelUse_le_one
          proposal edgeLabel qLaw R hk source state (source.1, label)
      _ = _ := by simp
  · intro v _ hv
    simp [mixedBlockLabelUse, hv, Ne.symm hv]
  · simp

end WeightedMultigraph

end
end WeightedEdgeColoring
