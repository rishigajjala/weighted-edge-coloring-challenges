import WeightedEdgeColoring.SubtwoMixedGraphBlockCandidate

/-! One fixed-block categorical selector for mixed candidates, variance, and labels. -/

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

abbrev MixedBlockJointRow :=
  (G.MixedBlockCapacityRow proposal edgeLabel qLaw R ⊕
    G.MixedBlockVarianceRow proposal edgeLabel qLaw R) ⊕
      (G.V × Option Label)

def mixedBlockJointUse (n : ℕ)
    (candidateScale rho omega pairScale selfScale : ℝ)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockJointRow proposal edgeLabel qLaw R) : ℝ :=
  match row with
  | Sum.inl (Sum.inl candidate) =>
      G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n candidateScale rho omega source state candidate
  | Sum.inl (Sum.inr variance) =>
      G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale source state variance
  | Sum.inr label =>
      G.mixedBlockLabelUse proposal edgeLabel qLaw R
        source state label

theorem mixedBlockJointUse_nonneg
    (n : ℕ) (candidateScale rho omega pairScale selfScale : ℝ)
    (hcapacity0 : ∀ source state row,
      0 ≤ G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n candidateScale rho omega source state row)
    (hvariance0 : ∀ source state row,
      0 ≤ G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale source state row)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockJointRow proposal edgeLabel qLaw R) :
    0 ≤ G.mixedBlockJointUse proposal edgeLabel qLaw R
      n candidateScale rho omega pairScale selfScale source state row := by
  rcases row with ⟨candidate | variance⟩ | label
  · exact hcapacity0 source state candidate
  · exact hvariance0 source state variance
  · exact G.mixedBlockLabelUse_nonneg
      proposal edgeLabel qLaw R source state label

theorem mixedBlockJointUse_le_one
    (n : ℕ) (candidateScale rho omega pairScale selfScale : ℝ)
    (hk : 0 < k)
    (hcapacity1 : ∀ source state row,
      G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n candidateScale rho omega source state row ≤ 1)
    (hvariance1 : ∀ source state row,
      G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale source state row ≤ 1)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2)
    (row : G.MixedBlockJointRow proposal edgeLabel qLaw R) :
    G.mixedBlockJointUse proposal edgeLabel qLaw R
      n candidateScale rho omega pairScale selfScale source state row ≤ 1 := by
  rcases row with ⟨candidate | variance⟩ | label
  · exact hcapacity1 source state candidate
  · exact hvariance1 source state variance
  · exact G.mixedBlockLabelUse_le_one
      proposal edgeLabel qLaw R hk source state label

theorem sum_mixedBlockJointUse_eq
    (n : ℕ) (candidateScale rho omega pairScale selfScale : ℝ)
    (source : G.V × Fin B)
    (state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R source.2) :
    (∑ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
      G.mixedBlockJointUse proposal edgeLabel qLaw R
        n candidateScale rho omega pairScale selfScale
        source state row) =
      (∑ row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R,
        G.mixedBlockCandidateUse proposal edgeLabel qLaw R
          n candidateScale rho omega source state row) +
      (∑ row : G.MixedBlockVarianceRow proposal edgeLabel qLaw R,
        G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale source state row) +
      (∑ row : G.V × Option Label,
        G.mixedBlockLabelUse proposal edgeLabel qLaw R
          source state row) := by
  simp [mixedBlockJointUse, Fintype.sum_sum_type]

theorem mixedBlockJoint_rowMean_le
    (n : ℕ) (candidateScale rho omega pairScale selfScale : ℝ)
    (capacityBound varianceBound labelBound : ℝ)
    (hcapacityBound : 0 ≤ capacityBound)
    (hvarianceBound : 0 ≤ varianceBound)
    (hlabelBound : 0 ≤ labelBound)
    (hcapacityMean : ∀ row : G.MixedBlockCapacityRow
      proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockCandidateUse proposal edgeLabel qLaw R
          n candidateScale rho omega) row ≤ capacityBound)
    (hvarianceMean : ∀ row : G.MixedBlockVarianceRow
      proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale) row ≤ varianceBound)
    (hlabelMean : ∀ row : G.V × Option Label,
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockLabelUse proposal edgeLabel qLaw R) row ≤ labelBound)
    (row : G.MixedBlockJointRow proposal edgeLabel qLaw R) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockJointUse proposal edgeLabel qLaw R
        n candidateScale rho omega pairScale selfScale) row ≤
      capacityBound + varianceBound + labelBound := by
  rcases row with ⟨capacity | variance⟩ | label
  · have h := hcapacityMean capacity
    dsimp [FiniteCategoricalSelection.rowMean,
      mixedBlockJointUse] at *
    linarith
  · have h := hvarianceMean variance
    dsimp [FiniteCategoricalSelection.rowMean,
      mixedBlockJointUse] at *
    linarith
  · have h := hlabelMean label
    dsimp [FiniteCategoricalSelection.rowMean,
      mixedBlockJointUse] at *
    linarith

theorem mixedBlockVariance_rowMean_le
    (rho omega pairScale selfScale varianceMeanBound : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (hvarianceMeanBound : 0 ≤ varianceMeanBound)
    (hprob0 : ∀ v b
      (state : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b),
      0 ≤ G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state)
    (hconditional : ∀ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega row ≤ varianceMeanBound * pairScale)
    (hselfBound : ∀ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega row ≤ selfScale)
    (row : G.MixedBlockVarianceRow proposal edgeLabel qLaw R) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale) row ≤
      varianceMeanBound + B := by
  rcases row with candidate | v
  · rw [G.mixedBlockVarianceUse_candidate_rowMean_eq]
    have h := (div_le_iff₀ hpair).2 (hconditional candidate)
    linarith
  · have h := G.mixedBlockVarianceUse_self_rowMean_le
      proposal edgeLabel qLaw R rho omega pairScale selfScale
      hself hprob0 hselfBound v
    linarith

theorem exists_mixedGraphFullWord_of_supported_blocks
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (choice : ∀ v (b : Fin B),
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (hsupport : ∀ v b,
      0 < G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b (choice v b)) :
    ∃ selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      ∀ v b,
        G.encodeMixedGraphWord
          (G.mixedBlockProposal proposal b) edgeLabel
          (G.mixedBlockLaw qLaw b)
          (G.mixedBlockRealization proposal edgeLabel qLaw R b)
          v (fun i ↦ selected v (b, i)) = choice v b := by
  classical
  have hdecode : ∀ v b, ∃ word : ∀ i : Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v (b, i),
      G.encodeMixedGraphWord
        (G.mixedBlockProposal proposal b) edgeLabel
        (G.mixedBlockLaw qLaw b)
        (G.mixedBlockRealization proposal edgeLabel qLaw R b)
        v word = choice v b := by
    intro v b
    exact G.exists_mixedGraphWord_of_padded_pos
      (G.mixedBlockProposal proposal b) edgeLabel
      (G.mixedBlockLaw qLaw b)
      (G.mixedBlockRealization proposal edgeLabel qLaw R b)
      (fun v i S ↦ hq0 v (b, i) S)
      (fun v i ↦ hqsum v (b, i))
      (fun v i S ↦ hqsingle v (b, i) S)
      hs hqstep hr0 hleft homega0 homega1 v (choice v b)
      (hsupport v b)
  let selected : ∀ v : G.V, ∀ c : Fin B × Fin k,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c :=
    fun v c ↦ Classical.choose (hdecode v c.1) c.2
  exact ⟨selected, fun v b ↦ (Classical.choose_spec (hdecode v b))⟩

theorem exists_mixedGraphSupportedBlockJointChoice
    {L n : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n) (hk : 0 < k)
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
    (hstar : ∀ v, G.starWeight v ≤ n) :
    let candidateScale := (L : ℝ) *
      mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0
    let unitScale := mixedBlockVarianceUnitScale (k := k) (s := s)
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      n rho omega C0
    let pairScale := (L : ℝ) * unitScale
    let selfScale := (n : ℝ) * unitScale
    let meanBound := 1 + (n : ℝ) * (rho / (1 - omega)) /
      candidateScale + n + 2 * B
    let columnBound :=
      (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
        (Label := Label) (β := β) (qstep := qstep) (r := r) n +
      ((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
      Fintype.card (Option Label)
    ∃ choice : ∀ v (b : Fin B),
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b,
      (∀ v b, 0 < G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b (choice v b)) ∧
      ∀ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
        FiniteCategoricalSelection.rowLoad
          (G.mixedBlockJointUse proposal edgeLabel qLaw R
            n candidateScale rho omega pairScale selfScale) row
          (fun source ↦ choice source.1 source.2) <
        FiniteCategoricalSelection.rowMean
          (fun source : G.V × Fin B ↦
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega source.1 source.2)
          (G.mixedBlockJointUse proposal edgeLabel qLaw R
            n candidateScale rho omega pairScale selfScale) row +
        FinitePartialResamplingNumerics.packingDeviation
          meanBound columnBound := by
  classical
  let candidateScale := (L : ℝ) *
    mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
  let unitScale := mixedBlockVarianceUnitScale (k := k) (s := s)
    (Label := Label) (β := β) (qstep := qstep) (r := r)
    n rho omega C0
  let pairScale := (L : ℝ) * unitScale
  let selfScale := (n : ℝ) * unitScale
  let capacityMean := (n : ℝ) * (rho / (1 - omega)) / candidateScale
  let meanBound := 1 + capacityMean + n + 2 * B
  let columnBound :=
    (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
      (Label := Label) (β := β) (qstep := qstep) (r := r) n +
    ((mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 +
    Fintype.card (Option Label)
  let prob : (G.V × Fin B) →
      FiniteDependentWordPadding.PackedWordState
        (Color := Fin k) (mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r)) → ℝ :=
    fun source state ↦ G.mixedBlockProbability proposal edgeLabel qLaw R
      omega source.1 source.2 state
  let use := G.mixedBlockJointUse proposal edgeLabel qLaw R
    n candidateScale rho omega pairScale selfScale
  have hscale : 0 < candidateScale := by
    unfold candidateScale
    exact mul_pos (by exact_mod_cast hL)
      (mixedCandidateOrientedScale_pos (Label := Label)
        (β := β) (qstep := qstep) (r := r)
        hrho hs homega0 hC0)
  have hunit : 0 < unitScale :=
    mixedBlockVarianceUnitScale_pos (Label := Label) (k := k)
      (s := s) (β := β) (qstep := qstep) (r := r)
      hn hk hs homega0 hrho hC0
  have hpair : 0 < pairScale := by
    unfold pairScale
    exact mul_pos (by exact_mod_cast hL) hunit
  have hself : 0 < selfScale := by
    unfold selfScale
    exact mul_pos (by exact_mod_cast hn) hunit
  have hprob0 : ∀ source state, 0 ≤ prob source state := by
    intro source state
    exact G.paddedMixedGraphWordProbability_nonneg
      (G.mixedBlockProposal proposal source.2) edgeLabel
      (G.mixedBlockLaw qLaw source.2)
      (G.mixedBlockRealization proposal edgeLabel qLaw R source.2)
      (fun v i S ↦ hq0 v (source.2, i) S)
      (fun v i ↦ hqsum v (source.2, i))
      (fun v i S ↦ hqsingle v (source.2, i) S)
      hs.le hqstep hr0 hleft homega0 homega1.le source.1 state
  have hprobSum : ∀ source, ∑ state, prob source state = 1 := by
    intro source
    exact G.sum_mixedBlockProbability proposal edgeLabel qLaw R
      omega source.1 source.2
  have hvariance : ∀ row : G.MixedBlockVarianceCandidateRow
      proposal edgeLabel qLaw R,
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega row ≤ selfScale := by
    intro row
    exact G.conditionalMixedBlockVariance_le_n_unitScale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs.le hqstep hr0 hleft homega0 homega1.le hrho.le hC0.le
      hproposal0 hproposal hstar row
  have hraw : ∀ source state row,
      G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
        rho omega source state row ≤ pairScale := by
    intro source state row
    exact G.rawMixedBlockVarianceCandidateUse_le_pairScale
      proposal edgeLabel qLaw R hmult hn hq0 hqmarg hqsingle hqsum
      hs.le hqstep hr0 hleft homega0 homega1.le hrho.le hC0.le
      hproposal0 hproposal source state row
  have hcapacity0 : ∀ source state row,
      0 ≤ G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n candidateScale rho omega source state row := by
    intro source state row
    apply G.mixedBlockCandidateUse_nonneg
      proposal edgeLabel qLaw R n candidateScale rho omega
    intro v c z candidate
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (G.mixedCandidateAtomUse_nonneg proposal edgeLabel qLaw R
        hq0 hqsum hqsingle hs.le hqstep hr0 hleft
        homega0 homega1.le hrho.le hproposal0 v c z candidate)) hscale.le
  have hcapacity1 : ∀ source state row,
      G.mixedBlockCandidateUse proposal edgeLabel qLaw R
        n candidateScale rho omega source state row ≤ 1 := by
    intro source state row
    apply G.mixedBlockCandidateUse_le_one
      proposal edgeLabel qLaw R n candidateScale rho omega
    intro v c z candidate
    exact G.scaledMixedCandidateAtomUse_le_one
      proposal edgeLabel qLaw R hL hmult hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1.le hrho hC0
      hproposal0 hproposal v c z candidate
  have hvariance0 : ∀ source state row,
      0 ≤ G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale source state row := by
    intro source state row
    exact G.mixedBlockVarianceUse_nonneg
      proposal edgeLabel qLaw R rho omega pairScale selfScale
      hpair hself (fun v b state ↦ hprob0 (v,b) state)
      source state row
  have hvariance1 : ∀ source state row,
      G.mixedBlockVarianceUse proposal edgeLabel qLaw R
        rho omega pairScale selfScale source state row ≤ 1 := by
    intro source state row
    exact G.mixedBlockVarianceUse_le_one
      proposal edgeLabel qLaw R rho omega pairScale selfScale
      hpair hself hraw hvariance source state row
  have huse0 : ∀ source state row, 0 ≤ use source state row := by
    intro source state row
    exact G.mixedBlockJointUse_nonneg proposal edgeLabel qLaw R
      n candidateScale rho omega pairScale selfScale
      hcapacity0 hvariance0 source state row
  have huse1 : ∀ source state row, use source state row ≤ 1 := by
    intro source state row
    exact G.mixedBlockJointUse_le_one proposal edgeLabel qLaw R
      n candidateScale rho omega pairScale selfScale
      hk hcapacity1 hvariance1 source state row
  have hcapacityMean : ∀ row : G.MixedBlockCapacityRow
      proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowMean prob
        (G.mixedBlockCandidateUse proposal edgeLabel qLaw R
          n candidateScale rho omega) row ≤ capacityMean := by
    intro row
    rw [G.mixedBlockCandidate_rowMean_eq
      proposal edgeLabel qLaw R n candidateScale rho omega row]
    exact G.scaledMixedCandidateAtomMean_le_one_sub_omega
      proposal edgeLabel qLaw R n candidateScale rho omega
      hq0 hqmarg hqsingle hqsum hs.le hqstep hr0 hleft
      homega0 homega1 hrho.le hscale row.1 row.2
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hvarianceMean : ∀ row : G.MixedBlockVarianceRow
      proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowMean prob
        (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale) row ≤ (n : ℝ) + B := by
    intro row
    apply G.mixedBlockVariance_rowMean_le proposal edgeLabel qLaw R
      rho omega pairScale selfScale (n : ℝ) hpair hself
      (Nat.cast_nonneg _) (fun v b st ↦ hprob0 (v,b) st)
      (fun candidate ↦ by
        have h := hvariance candidate
        have hcomp : selfScale ≤ (n : ℝ) * pairScale := by
          dsimp [selfScale, pairScale]
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          nlinarith [mul_nonneg hn0 (mul_nonneg (sub_nonneg.mpr hLreal) hunit.le)]
        exact h.trans hcomp)
      hvariance row
  have hlabelMean : ∀ row : G.V × Option Label,
      FiniteCategoricalSelection.rowMean prob
        (G.mixedBlockLabelUse proposal edgeLabel qLaw R) row ≤ B := by
    intro row
    exact G.mixedBlockLabel_rowMean_le_blocks
      proposal edgeLabel qLaw R hk omega
      (fun v b st ↦ hprob0 (v,b) st) row
  have hcapacityMean0 : 0 ≤ capacityMean := by
    dsimp [capacityMean]
    have hrho0 : 0 ≤ rho / (1 - omega) := by
      exact div_nonneg hrho.le (sub_nonneg.mpr homega1.le)
    positivity
  have hmeanBound : 0 < meanBound := by
    dsimp [meanBound]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
    linarith
  have hmean : ∀ row, FiniteCategoricalSelection.rowMean prob use row ≤
      meanBound := by
    intro row
    have h := G.mixedBlockJoint_rowMean_le
      proposal edgeLabel qLaw R n candidateScale rho omega
      pairScale selfScale capacityMean ((n : ℝ) + B) (B : ℝ)
      hcapacityMean0 (by positivity) (Nat.cast_nonneg _)
      hcapacityMean hvarianceMean hlabelMean row
    dsimp [meanBound]
    linarith
  have hcapacityColumn : ∀ source state,
      (∑ row : G.MixedBlockCapacityRow proposal edgeLabel qLaw R,
        G.mixedBlockCandidateUse proposal edgeLabel qLaw R
          n candidateScale rho omega source state row) ≤
      (k : ℝ) * mixedCandidateWeightedPerColorColumnBound
        (Label := Label) (β := β) (qstep := qstep) (r := r) n := by
    intro source state
    exact G.sum_mixedBlockCandidateUse_le_weightedColumn
      proposal edgeLabel qLaw R hL hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1.le hrho hC0
      hproposal0 hproposal hstar source state
  have hvarianceColumn : ∀ source state,
      (∑ row : G.MixedBlockVarianceRow proposal edgeLabel qLaw R,
        G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale source state row) ≤
      ((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n + 1 := by
    intro source state
    apply G.sum_mixedBlockVarianceUse_le_column
      proposal edgeLabel qLaw R rho omega pairScale selfScale
      (((mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n)
    · intro src st
      apply G.sum_rawMixedBlockVarianceCandidateUse_div_mul_le
        proposal edgeLabel qLaw R hL rho omega unitScale
        (((mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n)
        hunit src st
      exact G.sum_rawMixedBlockVarianceCandidateUse_le_n_stateCount
        proposal edgeLabel qLaw R hn hk hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1.le hrho hC0
        hproposal0 hproposal hstar src st
    · intro src st
      exact G.sum_mixedBlockVarianceSelfUse_le_one
        proposal edgeLabel qLaw R rho omega unitScale hunit hn
        hvariance src st
  have hlabelColumn : ∀ source state,
      (∑ row : G.V × Option Label,
        G.mixedBlockLabelUse proposal edgeLabel qLaw R
          source state row) ≤ Fintype.card (Option Label) := by
    intro source state
    exact G.sum_mixedBlockLabelUse_le_card
      proposal edgeLabel qLaw R hk source state
  have hcolumn : ∀ source state,
      (∑ row : G.MixedBlockJointRow proposal edgeLabel qLaw R,
        use source state row) ≤ columnBound := by
    intro source state
    rw [G.sum_mixedBlockJointUse_eq
      proposal edgeLabel qLaw R n candidateScale rho omega
      pairScale selfScale source state]
    have h1 := hcapacityColumn source state
    have h2 := hvarianceColumn source state
    have h3 := hlabelColumn source state
    dsimp [columnBound]
    linarith
  have hcolumnBound : 0 ≤ columnBound := by
    dsimp [columnBound, mixedCandidateWeightedPerColorColumnBound]
    positivity
  have hcolumnOne : 1 ≤ columnBound := by
    have hcandidate : 0 ≤ (k : ℝ) *
        mixedCandidateWeightedPerColorColumnBound
          (Label := Label) (β := β) (qstep := qstep) (r := r) n := by
      unfold mixedCandidateWeightedPerColorColumnBound
      positivity
    have hvarianceTerm : 0 ≤
        ((mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) ^ k) * n := by
      positivity
    have hlabel : (0 : ℝ) ≤ Fintype.card (Option Label) :=
      Nat.cast_nonneg _
    dsimp [columnBound]
    linarith
  let K := Nat.ceil meanBound + 1
  have hK : 0 < K := by omega
  have hmeanK : meanBound ≤ (K : ℝ) := by
    have hceil : meanBound ≤ (Nat.ceil meanBound : ℝ) := Nat.le_ceil _
    have hstep : (Nat.ceil meanBound : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.le_succ (Nat.ceil meanBound)
    exact hceil.trans hstep
  have hM : 0 < mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) := by
    unfold mixedGraphAtomBound
    omega
  let dummyState : FiniteDependentWordPadding.PackedWordState
      (Color := Fin k) (mixedGraphAtomBound (Label := Label)
        (β := β) (qstep := qstep) (r := r)) :=
    ⟨0, by
      change 0 < Fintype.card
        (Fin k → Fin (mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r)))
      exact Fintype.card_pos_iff.mpr
        ⟨fun _ ↦ ⟨0, hM⟩⟩⟩
  let dummyProb : _ → ℝ := fun state ↦ if state = dummyState then 1 else 0
  have hdummy0 : ∀ state, 0 ≤ dummyProb state := by
    intro state
    by_cases hstate : state = dummyState <;> simp [dummyProb, hstate]
  have hdummySum : ∑ state, dummyProb state = 1 := by
    simp [dummyProb]
  obtain ⟨choice, hsupport, hrows⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      meanBound columnBound hmeanBound hcolumnBound hcolumnOne
      K hK hmeanK prob dummyProb use hprob0 hprobSum
      hdummy0 hdummySum huse0 huse1 hmean hcolumn
  exact ⟨fun v b ↦ choice (v,b),
    fun v b ↦ hsupport (v,b),
    fun row ↦ hrows row⟩

end WeightedMultigraph

end
end WeightedEdgeColoring
