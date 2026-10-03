import WeightedEdgeColoring.SubtwoMixedGraphBlockJointSelector

/-! Sharp two-level selected mixed block variance bookkeeping. -/

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

def selectedRawMixedBlockVariance (rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) (b : Fin B) : ℝ :=
  ∑ source : G.V × Fin B,
    G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
      rho omega source (choice source.1 source.2)
        ⟨v, b, choice v b⟩

def selectedTotalRawMixedBlockVariance (rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) : ℝ :=
  ∑ b : Fin B,
    G.selectedRawMixedBlockVariance proposal edgeLabel qLaw R
      rho omega choice v b

def selectedConditionalMixedBlockVariance (rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) : ℝ :=
  ∑ b : Fin B,
    G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
      rho omega ⟨v, b, choice v b⟩

def meanTotalMixedBlockVariance (rho omega : ℝ)
    (v : G.V) : ℝ :=
  ∑ b : Fin B,
    ∑ state : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b,
      G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b state *
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega ⟨v, b, state⟩

def mixedBlockVarianceProductMean (rho omega : ℝ)
    (e : G.E) (b : Fin B) : ℝ :=
  ∑ left : G.MixedGraphPackedBlockState
      proposal edgeLabel qLaw R b,
    G.mixedBlockProbability proposal edgeLabel qLaw R
      omega (G.fst e) b left *
    ∑ right : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b,
      G.mixedBlockProbability proposal edgeLabel qLaw R
        omega (G.snd e) b right *
      G.mixedBlockVariance proposal edgeLabel qLaw R
        rho omega e b left right

theorem sum_centerProbability_mul_conditionalMixedBlockVariance
    (rho omega : ℝ) (v : G.V) (b : Fin B) :
    (∑ centerState : G.MixedGraphPackedBlockState
        proposal edgeLabel qLaw R b,
      G.mixedBlockProbability proposal edgeLabel qLaw R
        omega v b centerState *
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega ⟨v, b, centerState⟩) =
      ∑ e : G.StarEdge v,
        G.mixedBlockVarianceProductMean
          proposal edgeLabel qLaw R rho omega e.1 b := by
  simp_rw [G.conditionalMixedBlockVariance_eq_edge_sum
    proposal edgeLabel qLaw R rho omega v b]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ e : G.E, ∑ centerState,
      G.mixedBlockProbability proposal edgeLabel qLaw R
          omega v b centerState *
        (if v = G.fst e then
          ∑ oppositeState,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.snd e) b oppositeState *
              G.mixedBlockVariance proposal edgeLabel qLaw R
                rho omega e b centerState oppositeState
        else if v = G.snd e then
          ∑ oppositeState,
            G.mixedBlockProbability proposal edgeLabel qLaw R
              omega (G.fst e) b oppositeState *
              G.mixedBlockVariance proposal edgeLabel qLaw R
                rho omega e b oppositeState centerState
        else 0)) =
      ∑ e : G.E, if G.Inc v e then
        G.mixedBlockVarianceProductMean
          proposal edgeLabel qLaw R rho omega e b else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases hfst : v = G.fst e
      · subst v
        simp [WeightedMultigraph.Inc, mixedBlockVarianceProductMean]
      · by_cases hsnd : v = G.snd e
        · subst v
          have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          have hswap :
              (∑ centerState,
                G.mixedBlockProbability proposal edgeLabel qLaw R
                  omega (G.snd e) b centerState *
                  ∑ oppositeState,
                    G.mixedBlockProbability proposal edgeLabel qLaw R
                      omega (G.fst e) b oppositeState *
                    G.mixedBlockVariance proposal edgeLabel qLaw R
                      rho omega e b oppositeState centerState) =
              G.mixedBlockVarianceProductMean
                proposal edgeLabel qLaw R rho omega e b := by
            unfold mixedBlockVarianceProductMean
            calc
              _ = ∑ centerState, ∑ oppositeState,
                  G.mixedBlockProbability proposal edgeLabel qLaw R
                    omega (G.snd e) b centerState *
                  (G.mixedBlockProbability proposal edgeLabel qLaw R
                    omega (G.fst e) b oppositeState *
                  G.mixedBlockVariance proposal edgeLabel qLaw R
                    rho omega e b oppositeState centerState) := by
                apply Finset.sum_congr rfl
                intro centerState _
                rw [Finset.mul_sum]
              _ = ∑ oppositeState, ∑ centerState,
                  G.mixedBlockProbability proposal edgeLabel qLaw R
                    omega (G.snd e) b centerState *
                  (G.mixedBlockProbability proposal edgeLabel qLaw R
                    omega (G.fst e) b oppositeState *
                  G.mixedBlockVariance proposal edgeLabel qLaw R
                    rho omega e b oppositeState centerState) := by
                rw [Finset.sum_comm]
              _ = _ := by
                apply Finset.sum_congr rfl
                intro oppositeState _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro centerState _
                ring
          simp [WeightedMultigraph.Inc, hfst, hne, hswap]
        · have hinc : ¬G.Inc v e := by
            intro h
            rcases h with h | h
            · exact hfst h.symm
            · exact hsnd h.symm
          simp [hfst, hsnd, hinc]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp)
        (fun e ↦ G.mixedBlockVarianceProductMean
          proposal edgeLabel qLaw R rho omega e b)

theorem meanTotalMixedBlockVariance_le_sharp
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
    (hmass : ∀ e, ∑ c : Fin B × Fin k, proposal e c ≤ 1)
    (hstar : ∀ v, G.starWeight v ≤ n) (v : G.V) :
    G.meanTotalMixedBlockVariance proposal edgeLabel qLaw R rho omega v ≤
      (mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 /
        (n : ℝ)) * (rho * s * n) := by
  let U := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0 / (n : ℝ)
  have hU0 : 0 ≤ U := by
    unfold U
    exact div_nonneg
      (mixedCandidateOrientedScale_nonneg (Label := Label)
        (β := β) (qstep := qstep) (r := r)
        hrho hs homega0 hC0)
      (Nat.cast_nonneg _)
  unfold meanTotalMixedBlockVariance
  simp_rw [G.sum_centerProbability_mul_conditionalMixedBlockVariance
    proposal edgeLabel qLaw R rho omega v]
  calc
    (∑ b : Fin B, ∑ e : G.StarEdge v,
      G.mixedBlockVarianceProductMean
        proposal edgeLabel qLaw R rho omega e.1 b) ≤
      ∑ b : Fin B, ∑ e : G.StarEdge v,
        G.weight e.1 * (U * G.mixedBlockTarget proposal rho s e.1 b) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro e _
      exact G.expected_mixedBlockVariance_le
        proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 rho C0 hrho hC0
        hproposal0 hproposal e.1 b
    _ = U * ∑ e : G.StarEdge v,
        G.weight e.1 *
          (∑ b : Fin B, G.mixedBlockTarget proposal rho s e.1 b) := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      calc
        (∑ b : Fin B, G.weight e.1 *
          (U * G.mixedBlockTarget proposal rho s e.1 b)) =
          U * ∑ b : Fin B, G.weight e.1 *
            G.mixedBlockTarget proposal rho s e.1 b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = U * (G.weight e.1 *
          ∑ b : Fin B, G.mixedBlockTarget proposal rho s e.1 b) := by
          congr 1
          rw [Finset.mul_sum]
    _ ≤ U * (rho * s * G.starWeight v) := by
      apply mul_le_mul_of_nonneg_left _ hU0
      calc
        (∑ e : G.StarEdge v, G.weight e.1 *
            (∑ b : Fin B, G.mixedBlockTarget proposal rho s e.1 b)) =
          rho * s * ∑ e : G.StarEdge v,
            G.weight e.1 *
              (∑ c : Fin B × Fin k, proposal e.1 c) := by
          unfold mixedBlockTarget
          conv_rhs => rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          rw [Fintype.sum_prod_type]
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ rho * s * ∑ e : G.StarEdge v, G.weight e.1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hrho hs)
          apply Finset.sum_le_sum
          intro e _
          exact (mul_le_mul_of_nonneg_left (hmass e.1)
            (G.weight_nonneg e.1)).trans_eq (mul_one _)
        _ = rho * s * G.starWeight v := by rfl
    _ ≤ U * (rho * s * n) := by
      apply mul_le_mul_of_nonneg_left _ hU0
      exact mul_le_mul_of_nonneg_left (hstar v) (mul_nonneg hrho hs)

theorem mixedBlockVarianceSelf_rowLoad_eq
    (rho omega selfScale : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) :
    FiniteCategoricalSelection.rowLoad
      (G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
        rho omega selfScale) v
      (fun source ↦ choice source.1 source.2) =
      G.selectedConditionalMixedBlockVariance
        proposal edgeLabel qLaw R rho omega choice v / selfScale := by
  unfold FiniteCategoricalSelection.rowLoad
    selectedConditionalMixedBlockVariance
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mixedBlockVarianceSelfUse, Finset.sum_div]

theorem mixedBlockVarianceSelf_rowMean_eq
    (rho omega selfScale : ℝ) (v : G.V) :
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
        rho omega selfScale) v =
      G.meanTotalMixedBlockVariance
        proposal edgeLabel qLaw R rho omega v / selfScale := by
  unfold FiniteCategoricalSelection.rowMean
    meanTotalMixedBlockVariance
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [mixedBlockVarianceSelfUse, Finset.sum_div,
    ← mul_div_assoc]

theorem mixedBlockVarianceCandidate_rowLoad_eq
    (rho omega pairScale : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) (b : Fin B) :
    FiniteCategoricalSelection.rowLoad
      (fun source state row ↦
        G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
          rho omega source state row / pairScale)
      ⟨v, b, choice v b⟩
      (fun source ↦ choice source.1 source.2) =
      G.selectedRawMixedBlockVariance
        proposal edgeLabel qLaw R rho omega choice v b / pairScale := by
  unfold FiniteCategoricalSelection.rowLoad
    selectedRawMixedBlockVariance
  rw [Finset.sum_div]

theorem selectedTotalRawMixedBlockVariance_le_of_rowBounds
    (rho omega pairScale selfScale deviation : ℝ)
    (hpair : 0 < pairScale) (hself : 0 < selfScale)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (hrows : ∀ row : G.MixedBlockVarianceRow
      proposal edgeLabel qLaw R,
      FiniteCategoricalSelection.rowLoad
        (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale) row
        (fun source ↦ choice source.1 source.2) ≤
      FiniteCategoricalSelection.rowMean
        (fun source : G.V × Fin B ↦
          G.mixedBlockProbability proposal edgeLabel qLaw R
            omega source.1 source.2)
        (G.mixedBlockVarianceUse proposal edgeLabel qLaw R
          rho omega pairScale selfScale) row + deviation) :
    ∀ v,
      G.selectedTotalRawMixedBlockVariance
          proposal edgeLabel qLaw R rho omega choice v ≤
        G.meanTotalMixedBlockVariance
          proposal edgeLabel qLaw R rho omega v +
          selfScale * deviation + (B : ℝ) * pairScale * deviation := by
  intro v
  have hcandidate : ∀ b : Fin B,
      G.selectedRawMixedBlockVariance
          proposal edgeLabel qLaw R rho omega choice v b ≤
        G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
          rho omega ⟨v, b, choice v b⟩ + pairScale * deviation := by
    intro b
    have h := hrows (Sum.inl ⟨v, b, choice v b⟩)
    rw [G.mixedBlockVarianceUse_candidate_rowMean_eq] at h
    change FiniteCategoricalSelection.rowLoad
      (fun source state row ↦
        G.rawMixedBlockVarianceCandidateUse proposal edgeLabel qLaw R
          rho omega source state row / pairScale)
      ⟨v, b, choice v b⟩ (fun source ↦ choice source.1 source.2) ≤
      G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
        rho omega ⟨v, b, choice v b⟩ / pairScale + deviation at h
    rw [G.mixedBlockVarianceCandidate_rowLoad_eq] at h
    have hmult := mul_le_mul_of_nonneg_right h hpair.le
    have hpairNe : pairScale ≠ 0 := ne_of_gt hpair
    field_simp at hmult ⊢
    nlinarith
  have hsum :
      G.selectedTotalRawMixedBlockVariance
          proposal edgeLabel qLaw R rho omega choice v ≤
        G.selectedConditionalMixedBlockVariance
          proposal edgeLabel qLaw R rho omega choice v +
          (B : ℝ) * pairScale * deviation := by
    unfold selectedTotalRawMixedBlockVariance
      selectedConditionalMixedBlockVariance
    calc
      _ ≤ ∑ b : Fin B,
        (G.conditionalMixedBlockVariance proposal edgeLabel qLaw R
          rho omega ⟨v, b, choice v b⟩ + pairScale * deviation) :=
        Finset.sum_le_sum fun b _ ↦ hcandidate b
      _ = _ := by simp [Finset.sum_add_distrib, mul_assoc]
  have hselfRow := hrows (Sum.inr v)
  change FiniteCategoricalSelection.rowLoad
      (G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
        rho omega selfScale) v (fun source ↦ choice source.1 source.2) ≤
    FiniteCategoricalSelection.rowMean
      (fun source : G.V × Fin B ↦
        G.mixedBlockProbability proposal edgeLabel qLaw R
          omega source.1 source.2)
      (G.mixedBlockVarianceSelfUse proposal edgeLabel qLaw R
        rho omega selfScale) v + deviation at hselfRow
  rw [G.mixedBlockVarianceSelf_rowLoad_eq,
    G.mixedBlockVarianceSelf_rowMean_eq] at hselfRow
  have hmult := mul_le_mul_of_nonneg_right hselfRow hself.le
  have hselfNe : selfScale ≠ 0 := ne_of_gt hself
  have hselfBound :
      G.selectedConditionalMixedBlockVariance
          proposal edgeLabel qLaw R rho omega choice v ≤
        G.meanTotalMixedBlockVariance
          proposal edgeLabel qLaw R rho omega v +
          selfScale * deviation := by
    field_simp at hmult ⊢
    nlinarith
  linarith

theorem selectedRawMixedBlockVariance_eq_star_sum
    (rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) (b : Fin B) :
    G.selectedRawMixedBlockVariance
        proposal edgeLabel qLaw R rho omega choice v b =
      ∑ e : G.StarEdge v,
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e.1 b
          (choice (G.fst e.1) b) (choice (G.snd e.1) b) := by
  unfold selectedRawMixedBlockVariance
    rawMixedBlockVarianceCandidateUse
  rw [Finset.sum_comm]
  calc
    (∑ e : G.E, ∑ source : G.V × Fin B,
      G.mixedBlockVarianceCandidateEdgeUse proposal edgeLabel qLaw R
        rho omega source (choice source.1 source.2) e
        ⟨v, b, choice v b⟩) =
      ∑ e : G.E, if G.Inc v e then
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e b
          (choice (G.fst e) b) (choice (G.snd e) b) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Fintype.sum_prod_type]
      by_cases hfst : v = G.fst e
      · subst v
        have hne : G.fst e ≠ G.snd e := G.noLoop e
        simp [mixedBlockVarianceCandidateEdgeUse,
          WeightedMultigraph.Inc, hne]
      · by_cases hsnd : v = G.snd e
        · subst v
          have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
          simp [mixedBlockVarianceCandidateEdgeUse,
            WeightedMultigraph.Inc, hne, hfst]
        · have hfst' : G.fst e ≠ v := Ne.symm hfst
          have hsnd' : G.snd e ≠ v := Ne.symm hsnd
          simp [mixedBlockVarianceCandidateEdgeUse,
            WeightedMultigraph.Inc, hfst, hsnd, hfst', hsnd']
    _ = ∑ e ∈ Finset.univ.filter (G.Inc v),
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e b
          (choice (G.fst e) b) (choice (G.snd e) b) := by
      rw [Finset.sum_filter]
    _ = _ := by
      exact Finset.sum_subtype (Finset.univ.filter (G.Inc v))
        (by intro e; simp)
        (fun e ↦ G.mixedBlockVariance proposal edgeLabel qLaw R
          rho omega e b (choice (G.fst e) b) (choice (G.snd e) b))

theorem selectedTotalRawMixedBlockVariance_eq_star_sum
    (rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) :
    G.selectedTotalRawMixedBlockVariance
        proposal edgeLabel qLaw R rho omega choice v =
      ∑ b : Fin B, ∑ e : G.StarEdge v,
        G.mixedBlockVariance proposal edgeLabel qLaw R rho omega e.1 b
          (choice (G.fst e.1) b) (choice (G.snd e.1) b) := by
  unfold selectedTotalRawMixedBlockVariance
  apply Finset.sum_congr rfl
  intro b _
  exact G.selectedRawMixedBlockVariance_eq_star_sum
    proposal edgeLabel qLaw R rho omega choice v b

theorem selectedMixedBlockStarWeightedSquare_le
    (rho omega : ℝ)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      (G.selectedMixedBlockTotalOptionMass
        proposal edgeLabel qLaw R rho omega choice e.1 -
        G.mixedBlockTotalTarget proposal rho s e.1) ^ 2) ≤
      (B : ℝ) * G.selectedTotalRawMixedBlockVariance
        proposal edgeLabel qLaw R rho omega choice v := by
  rw [G.selectedTotalRawMixedBlockVariance_eq_star_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  exact G.selectedMixedBlockTotalOptionMass_weightedSquare_le
    proposal edgeLabel qLaw R rho omega choice e.1

theorem selectedMixedBlockStarClippedResidual_le
    (rho omega t : ℝ) (ht : 0 < t)
    (choice : ∀ v : G.V, ∀ b : Fin B,
      G.MixedGraphPackedBlockState proposal edgeLabel qLaw R b)
    (v : G.V) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      (1 - min 1 (G.selectedMixedBlockTotalOptionMass
        proposal edgeLabel qLaw R rho omega choice e.1))) ≤
      (∑ e : G.StarEdge v, G.weight e.1 *
        max 0 (1 - G.mixedBlockTotalTarget proposal rho s e.1)) +
      t * G.starWeight v +
      ((B : ℝ) * G.selectedTotalRawMixedBlockVariance
        proposal edgeLabel qLaw R rho omega choice v) / (4 * t) := by
  have ht4 : 0 ≤ 4 * t := by positivity
  have hvar := G.selectedMixedBlockStarWeightedSquare_le
    proposal edgeLabel qLaw R rho omega choice v
  have hdiv := div_le_div_of_nonneg_right hvar ht4
  have hclip := sum_clipped_residual_le_mean_deficit_add_variance
    (fun e : G.StarEdge v ↦ G.weight e.1)
    (fun e : G.StarEdge v ↦ G.selectedMixedBlockTotalOptionMass
      proposal edgeLabel qLaw R rho omega choice e.1)
    (fun e : G.StarEdge v ↦
      G.mixedBlockTotalTarget proposal rho s e.1)
    t ht (fun e ↦ (G.weight_pos e.1).le)
  exact hclip.trans (by
    simpa [starWeight, add_comm, add_left_comm, add_assoc] using
      (add_le_add_left hdiv
        ((∑ e : G.StarEdge v, G.weight e.1 *
          max 0 (1 - G.mixedBlockTotalTarget proposal rho s e.1)) +
          t * G.starWeight v)))

end WeightedMultigraph

end
end WeightedEdgeColoring
