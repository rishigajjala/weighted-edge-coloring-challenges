import WeightedEdgeColoring.SubtwoMixedGraphWeightedPackedColumn
import WeightedEdgeColoring.SubtwoMixedGraphJointSelection
import WeightedEdgeColoring.SubtwoPackedLabelRows

/-!
# Weighted-column packed-word choice for candidates and endpoint labels

The mean-relative categorical selector can carry the actual mixed candidate
rows and normalized endpoint-label count rows simultaneously.  Its common
deviation is sublinear in the physical packet scale, while each label row
is compared with its own mean rather than the larger capacity mean.
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

theorem exists_mixedGraphPackedWord_candidateAndLabelRows_lt_of_starWeight
    {L n : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
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
    (hstar : ∀ v, G.starWeight v ≤ n) :
    let scale := (L : ℝ) * mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
    let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
    let columnBound := mixedCandidateWeightedPerColorColumnBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) n
    let Rmean := 1 + meanBound
    let Ccolumn := (Fintype.card Color : ℝ) * columnBound +
      Fintype.card (Option Label)
    ∃ choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R,
      (∀ v, 0 < G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega v (choice v)) ∧
      ∀ row :
        (Σ c : Color,
          G.MixedCandidateRowAt proposal edgeLabel qLaw R c) ⊕
        (G.V × Option Label),
        FiniteCategoricalSelection.rowLoad
          (G.mixedGraphJointUse proposal edgeLabel qLaw R
            hColor n scale rho omega) row choice <
          FiniteCategoricalSelection.rowMean
            (G.paddedMixedGraphWordProbability
              proposal edgeLabel qLaw R omega)
            (G.mixedGraphJointUse proposal edgeLabel qLaw R
              hColor n scale rho omega) row +
          FinitePartialResamplingNumerics.packingDeviation
            Rmean Ccolumn := by
  classical
  let scale := (L : ℝ) * mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
  let columnBound := mixedCandidateWeightedPerColorColumnBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) n
  let Rmean := 1 + meanBound
  let Ccolumn := (Fintype.card Color : ℝ) * columnBound +
    Fintype.card (Option Label)
  let prob := G.paddedMixedGraphWordProbability
    proposal edgeLabel qLaw R omega
  let use := G.mixedGraphJointUse proposal edgeLabel qLaw R
    hColor n scale rho omega
  have hbase : 0 < mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 :=
    mixedCandidateOrientedScale_pos hrho hs homega0 hC0
  have hscale : 0 < scale := by
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    exact mul_pos hLreal hbase
  have hmeanBound : 0 < meanBound := by
    unfold meanBound
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_pos (mul_pos hnR
      (div_pos hrho (sub_pos.mpr homega1))) hscale
  have hRmean : 0 < Rmean := by dsimp [Rmean]; linarith
  have hcolumnBound : 0 ≤ columnBound := by
    unfold columnBound mixedCandidateWeightedPerColorColumnBound
    positivity
  have hCcolumn : 0 ≤ Ccolumn := by
    dsimp [Ccolumn]
    positivity
  have hCcolumn1 : 1 ≤ Ccolumn := by
    have hopt : (1 : ℝ) ≤ Fintype.card (Option Label) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr ⟨none⟩)
    have hfirst : 0 ≤ (Fintype.card Color : ℝ) * columnBound :=
      mul_nonneg (Nat.cast_nonneg _) hcolumnBound
    dsimp [Ccolumn]
    linarith
  let K := Nat.ceil Rmean + 1
  have hK : 0 < K := by omega
  have hRK : Rmean ≤ (K : ℝ) := by
    have hceil : Rmean ≤ (Nat.ceil Rmean : ℝ) := Nat.le_ceil Rmean
    have hstep : (Nat.ceil Rmean : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (Nat.le_succ (Nat.ceil Rmean))
    exact hceil.trans hstep
  have hM : 0 < mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) := by
    unfold mixedGraphAtomBound
    omega
  let dummyState : G.MixedGraphPackedState proposal edgeLabel qLaw R :=
    ⟨0, by
      change 0 < Fintype.card
        (Color → Fin (mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r)))
      exact Fintype.card_pos_iff.mpr
        ⟨fun _ ↦ ⟨0, hM⟩⟩⟩
  let dummyProb : G.MixedGraphPackedState proposal edgeLabel qLaw R → ℝ :=
    fun state ↦ if state = dummyState then 1 else 0
  have hdummy0 : ∀ state, 0 ≤ dummyProb state := by
    intro state
    by_cases hstate : state = dummyState <;> simp [dummyProb, hstate]
  have hdummySum : ∑ state, dummyProb state = 1 := by
    simp [dummyProb]
  have hprob0 : ∀ v packed, 0 ≤ prob v packed := by
    intro v packed
    exact G.paddedMixedGraphWordProbability_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs.le hqstep hr0 hleft homega0 homega1.le v packed
  have hprobSum : ∀ v, ∑ packed, prob v packed = 1 := by
    intro v
    exact G.sum_paddedMixedGraphWordProbability
      proposal edgeLabel qLaw R omega v
  have huse0 : ∀ v packed row, 0 ≤ use v packed row := by
    intro v packed row
    cases row with
    | inl cr =>
        unfold use mixedGraphJointUse scaledMixedCandidateAtomUse
        exact div_nonneg
          (mul_nonneg (Nat.cast_nonneg n)
            (G.mixedCandidateAtomUse_nonneg
              proposal edgeLabel qLaw R hq0 hqsum hqsingle
              hs.le hqstep hr0 hleft homega0 homega1.le
              hrho.le hproposal0 v cr.1
              (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
                v packed cr.1) cr.2)) hscale.le
    | inr vl =>
        exact Subtwo.packedLabelUse_nonneg hColor id
          (G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R)
          v packed vl
  have huse1 : ∀ v packed row, use v packed row ≤ 1 := by
    intro v packed row
    cases row with
    | inl cr =>
        exact G.scaledMixedCandidateAtomUse_le_one
          proposal edgeLabel qLaw R hL hmult hn hq0 hqmarg hqsingle hqsum
          hs hqstep hr0 hleft homega0 homega1.le hrho hC0
          hproposal0 hproposal v cr.1
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
            v packed cr.1) cr.2
    | inr vl =>
        exact (Subtwo.packedLabelUse_le_cap hColor id
          (G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R)
          v packed vl).trans
          (Subtwo.packedLabelCap_le_one id v vl)
  have hmean : ∀ row,
      FiniteCategoricalSelection.rowMean prob use row ≤ Rmean := by
    intro row
    cases row with
    | inl cr =>
        change (∑ v, ∑ packed,
          prob v packed *
            G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
              scale rho omega v cr.1
              (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
                v packed cr.1) cr.2) ≤ Rmean
        have heq : (∑ v, ∑ packed,
            prob v packed *
              G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
                scale rho omega v cr.1
                (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
                  v packed cr.1) cr.2) =
            ∑ v, ∑ z : G.MixedGraphAtom
              proposal edgeLabel qLaw R v cr.1,
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
        exact (G.scaledMixedCandidateAtomMean_le_one_sub_omega
          proposal edgeLabel qLaw R n scale rho omega
          hq0 hqmarg hqsingle hqsum hs.le hqstep hr0 hleft
          homega0 homega1 hrho.le hscale cr.1 cr.2).trans
          (by dsimp [Rmean]; linarith)
    | inr vl =>
        change (∑ v, ∑ packed, prob v packed *
          Subtwo.packedLabelUse hColor id
            (G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R)
            v packed vl) ≤ Rmean
        have hsingle : (∑ v, ∑ packed, prob v packed *
            Subtwo.packedLabelUse hColor id
              (G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R)
              v packed vl) ≤ 1 := by
          rw [Finset.sum_eq_single vl.1]
          · calc
              (∑ packed, prob vl.1 packed *
                Subtwo.packedLabelUse hColor id
                  (G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R)
                  vl.1 packed vl) ≤
                ∑ packed, prob vl.1 packed * 1 := by
                  apply Finset.sum_le_sum
                  intro packed _
                  exact mul_le_mul_of_nonneg_left
                    ((Subtwo.packedLabelUse_le_cap hColor id
                      (G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R)
                      vl.1 packed vl).trans
                      (Subtwo.packedLabelCap_le_one id vl.1 vl))
                    (hprob0 vl.1 packed)
              _ = 1 := by simp [hprobSum vl.1]
          · intro v _ hv
            simp [Subtwo.packedLabelUse, hv]
          · simp
        exact hsingle.trans (by dsimp [Rmean]; linarith)
  have hcolumn : ∀ v packed,
      (∑ row, use v packed row) ≤ Ccolumn := by
    intro v packed
    rw [Fintype.sum_sum_type]
    have hcapacity :
        (∑ cr : Σ c : Color,
          G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
          use v packed (Sum.inl cr)) ≤
        (Fintype.card Color : ℝ) * columnBound := by
      rw [Fintype.sum_sigma]
      change (∑ c : Color,
        ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
            scale rho omega v c
            (G.decodeMixedGraphAtom proposal edgeLabel qLaw R v packed c)
            row) ≤ (Fintype.card Color : ℝ) * columnBound
      exact G.sum_scaledMixedPackedWordCandidateUse_mul_le_weightedColumn
        proposal edgeLabel qLaw R hL hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1.le hrho hC0
        hproposal0 hproposal hstar v packed
    have hlabels :
        (∑ vl : G.V × Option Label,
          use v packed (Sum.inr vl)) ≤
        (Fintype.card (Option Label) : ℝ) := by
      calc
        (∑ vl : G.V × Option Label,
          use v packed (Sum.inr vl)) ≤
          ∑ vl : G.V × Option Label,
            Subtwo.packedLabelCap id v vl := by
          apply Finset.sum_le_sum
          intro vl _
          exact Subtwo.packedLabelUse_le_cap hColor id
            (G.mixedGraphPackedCoordinateLabel proposal edgeLabel qLaw R)
            v packed vl
        _ = (Fintype.card (Option Label) : ℝ) := by
          have hc := Subtwo.packedLabelAugmentedCap_column
            (Source := G.V)
            (Row := Σ c : Color,
              G.MixedCandidateRowAt proposal edgeLabel qLaw R c)
            (Vertex := G.V) (Label := Option Label)
            (fun _ _ ↦ (0 : ℝ)) id v
          simpa [Subtwo.packedLabelAugmentedCap] using hc
    exact (add_le_add hcapacity hlabels).trans_eq (by rfl)
  obtain ⟨choice, hpos, hrows⟩ :=
    FiniteCategoricalSelection.exists_supported_choice_rowLoad_lt_rowMean_add_deviation
      Rmean Ccolumn hRmean hCcolumn hCcolumn1 K hK hRK
      prob dummyProb use hprob0 hprobSum hdummy0 hdummySum
      huse0 huse1 hmean hcolumn
  exact ⟨choice, hpos, hrows⟩

end WeightedMultigraph

end

end WeightedEdgeColoring
