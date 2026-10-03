import WeightedEdgeColoring.SubtwoMixedGraphWeightedCandidateRows

/-! The actual mixed candidate column is bounded by star weight. -/

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

def mixedCandidateWeightedPerColorColumnBound (n : ℕ) : ℝ :=
  (n : ℝ) * (mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) : ℝ) *
      ((explicitLargeSlotBound β qstep r : ℝ) / β + 1)

theorem sum_inc_weight_eq_starWeight (v : G.V) :
    (∑ e : G.E, if G.Inc v e then G.weight e else 0) =
      G.starWeight v := by
  classical
  calc
    (∑ e : G.E, if G.Inc v e then G.weight e else 0) =
        ∑ e ∈ Finset.univ.filter (G.Inc v), G.weight e := by
      rw [← Finset.sum_filter]
    _ = ∑ e : G.StarEdge v, G.weight e.1 := by
      exact Finset.sum_subtype
        (Finset.univ.filter (G.Inc v)) (by intro e; simp)
          (fun e : G.E ↦ G.weight e)
    _ = G.starWeight v := rfl

theorem sum_scaledMixedCandidateAtomUse_le_weightedColumn
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
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c) :
    (∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        (mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0)
        rho omega source c sourceAtom row) ≤
      mixedCandidateWeightedPerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) n := by
  classical
  let scale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let M : ℝ := mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r)
  let B : ℝ := explicitLargeSlotBound β qstep r
  have hlarge :
      (∑ row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inl row)) ≤
        (M * B / β) * G.starWeight source := by
    calc
      (∑ row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inl row)) =
          ∑ e, ∑ row : G.MixedLargeCandidateRow
            proposal edgeLabel qLaw R c,
            (n : ℝ) * G.mixedLargeCandidateEdgeUse
              proposal edgeLabel qLaw R rho omega source c sourceAtom e row /
              scale := by
        unfold scaledMixedCandidateAtomUse mixedCandidateAtomUse
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ ∑ e, if G.Inc source e then M * B * (G.weight e / β)
          else 0 := by
        apply Finset.sum_le_sum
        intro e _
        simpa [scale, M, B] using
          G.sum_scaledMixedLargeRows_edge_le_weight
            proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
            hs hqstep hr0 hleft homega0 homega1 hrho hC0
            hproposal0 hproposal source c sourceAtom e
      _ = (M * B / β) * G.starWeight source := by
        calc
          (∑ e : G.E, if G.Inc source e then
              M * B * (G.weight e / β) else 0) =
              ∑ e : G.E, (M * B / β) *
                (if G.Inc source e then G.weight e else 0) := by
            apply Finset.sum_congr rfl
            intro e _
            split_ifs <;> ring
          _ = (M * B / β) *
              (∑ e : G.E, if G.Inc source e then G.weight e else 0) := by
            rw [Finset.mul_sum]
          _ = (M * B / β) * G.starWeight source := by
            rw [G.sum_inc_weight_eq_starWeight]
  have htiny :
      (∑ row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inr row)) ≤
        M * G.starWeight source := by
    calc
      (∑ row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inr row)) =
          ∑ e, ∑ row : G.MixedTinyCandidateRow
            proposal edgeLabel qLaw R c,
            (n : ℝ) * G.mixedTinyCandidateEdgeUse
              proposal edgeLabel qLaw R rho omega source c sourceAtom e row /
              scale := by
        unfold scaledMixedCandidateAtomUse mixedCandidateAtomUse
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum, Finset.sum_div]
      _ ≤ ∑ e, if G.Inc source e then M * G.weight e else 0 := by
        apply Finset.sum_le_sum
        intro e _
        simpa [scale, M] using
          G.sum_scaledMixedTinyRows_edge_le_weight
            proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
            hs hqstep hr0 hleft homega0 homega1 hrho hC0
            hproposal0 hproposal source c sourceAtom e
      _ = M * G.starWeight source := by
        calc
          (∑ e : G.E, if G.Inc source e then M * G.weight e else 0) =
              ∑ e : G.E, M *
                (if G.Inc source e then G.weight e else 0) := by
            apply Finset.sum_congr rfl
            intro e _
            split_ifs <;> ring
          _ = M * (∑ e : G.E,
              if G.Inc source e then G.weight e else 0) := by
            rw [Finset.mul_sum]
          _ = M * G.starWeight source := by
            rw [G.sum_inc_weight_eq_starWeight]
  rw [Fintype.sum_sum_type]
  have hcoef : 0 ≤ M * B / β + M := by
    dsimp [M, B]
    positivity
  have hstarR : G.starWeight source ≤ (n : ℝ) := hstar source
  calc
    (∑ row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inl row)) +
      (∑ row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inr row)) ≤
        (M * B / β + M) * G.starWeight source := by
      nlinarith [hlarge, htiny]
    _ ≤ (M * B / β + M) * n :=
      mul_le_mul_of_nonneg_left hstarR hcoef
    _ = mixedCandidateWeightedPerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) n := by
      unfold mixedCandidateWeightedPerColorColumnBound
      dsimp [M, B]
      ring

end WeightedMultigraph

end

end WeightedEdgeColoring
