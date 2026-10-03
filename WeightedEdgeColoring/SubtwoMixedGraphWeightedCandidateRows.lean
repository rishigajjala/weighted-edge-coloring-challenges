import WeightedEdgeColoring.SubtwoMixedGraphWeightedCandidateEdge

/-! Weighted edge contributions to the mixed candidate column. -/

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

theorem sum_scaledMixedLargeRows_edge_le_weight
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
    (e : G.E) :
    (∑ row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c,
      (n : ℝ) * G.mixedLargeCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row /
        mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0) ≤
      if G.Inc source e then
        (mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) *
          (explicitLargeSlotBound β qstep r : ℝ) *
          (G.weight e / β)
      else 0 := by
  classical
  let scale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let K : ℝ := (mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) : ℝ) *
    (explicitLargeSlotBound β qstep r : ℝ)
  let f : (Σ v : G.V,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c ×
        Fin (explicitLargeSlotBound β qstep r)) → ℝ :=
    fun x ↦ (n : ℝ) * G.mixedLargeCandidateEdgeUse
      proposal edgeLabel qLaw R rho omega source c sourceAtom e
      ⟨x.1, x.2.1, x.2.2⟩ / scale
  have hscale : 0 < scale := mixedCandidateOrientedScale_pos
    hrho hs homega0 hC0
  have hcard : ∀ v : G.V,
      (Fintype.card (G.MixedGraphAtom proposal edgeLabel qLaw R v c ×
        Fin (explicitLargeSlotBound β qstep r)) : ℝ) ≤ K := by
    intro v
    simpa only [K, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast (G.mixedGraphAtom_card_le
          proposal edgeLabel qLaw R v c))
        (Nat.cast_nonneg _)
  have hunit : ∀ x, f x ≤ G.weight e / β := by
    intro x
    rcases x with ⟨v, a, i⟩
    by_cases hlarge : β ≤ G.weight e
    · have hone : (n : ℝ) * G.mixedLargeCandidateEdgeUse
          proposal edgeLabel qLaw R rho omega source c sourceAtom e
            ⟨v, a, i⟩ / scale ≤ 1 := by
        apply (div_le_one hscale).2
        exact G.n_mul_mixedLargeCandidateEdgeUse_le_scale
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
          hproposal0 hproposal source c sourceAtom e ⟨v, a, i⟩
      have hratio : (1 : ℝ) ≤ G.weight e / β := by
        apply (le_div_iff₀ hβ).2
        simpa using hlarge
      exact hone.trans hratio
    · have hzero := G.mixedLargeCandidateEdgeUse_eq_zero_of_tiny
        proposal edgeLabel qLaw R rho omega source c sourceAtom e
          ⟨v, a, i⟩ (lt_of_not_ge hlarge)
      simp only [f, hzero, mul_zero, zero_div]
      exact div_nonneg (G.weight_pos e).le hβ.le
  have hsupp : ∀ x, ¬G.EndpointPairMatches x.1 source e → f x = 0 := by
    intro x hnot
    rcases x with ⟨v, a, i⟩
    unfold EndpointPairMatches at hnot
    simp only [not_or] at hnot
    simp [f, mixedLargeCandidateEdgeUse, hnot.1, hnot.2]
  have hsum := G.sum_sigma_endpointPair_le_coeff K (G.weight e / β)
    (div_nonneg (G.weight_pos e).le hβ.le) hcard source e f hunit hsupp
  have hroweq :
      (∑ row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c,
        (n : ℝ) * G.mixedLargeCandidateEdgeUse
          proposal edgeLabel qLaw R rho omega source c sourceAtom e row /
          scale) = ∑ x, f x := by
    exact Fintype.sum_equiv
      (G.mixedLargeCandidateRowEquiv proposal edgeLabel qLaw R c)
      _ _ (fun _ ↦ rfl)
  rw [hroweq]
  simpa only [K, f] using hsum

theorem sum_scaledMixedTinyRows_edge_le_weight
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
    (e : G.E) :
    (∑ row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c,
      (n : ℝ) * G.mixedTinyCandidateEdgeUse
        proposal edgeLabel qLaw R rho omega source c sourceAtom e row /
        mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0) ≤
      if G.Inc source e then
        (mixedGraphAtomBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) : ℝ) * G.weight e
      else 0 := by
  classical
  let scale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let K : ℝ := mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r)
  let f : (Σ v : G.V,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c) → ℝ :=
    fun x ↦ (n : ℝ) * G.mixedTinyCandidateEdgeUse
      proposal edgeLabel qLaw R rho omega source c sourceAtom e
      ⟨x.1, x.2⟩ / scale
  have hscale : 0 < scale := mixedCandidateOrientedScale_pos
    hrho hs homega0 hC0
  have hcard : ∀ v : G.V,
      (Fintype.card (G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ)
        ≤ K := by
    intro v
    dsimp [K]
    exact_mod_cast (G.mixedGraphAtom_card_le proposal edgeLabel qLaw R v c)
  have hunit : ∀ x, f x ≤ G.weight e := by
    intro x
    rcases x with ⟨v, a⟩
    apply (div_le_iff₀ hscale).2
    exact G.n_mul_mixedTinyCandidateEdgeUse_le_weight_scale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
      hproposal0 hproposal source c sourceAtom e ⟨v, a⟩
  have hsupp : ∀ x, ¬G.EndpointPairMatches x.1 source e → f x = 0 := by
    intro x hnot
    rcases x with ⟨v, a⟩
    unfold EndpointPairMatches at hnot
    simp only [not_or] at hnot
    simp [f, mixedTinyCandidateEdgeUse, hnot.1, hnot.2]
  have hsum := G.sum_sigma_endpointPair_le_coeff K (G.weight e)
    (G.weight_pos e).le hcard source e f hunit hsupp
  have hroweq :
      (∑ row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c,
        (n : ℝ) * G.mixedTinyCandidateEdgeUse
          proposal edgeLabel qLaw R rho omega source c sourceAtom e row /
          scale) = ∑ x, f x := by
    exact Fintype.sum_equiv
      (G.mixedTinyCandidateRowEquiv proposal edgeLabel qLaw R c)
      _ _ (fun _ ↦ rfl)
  rw [hroweq]
  simpa only [K, f] using hsum

end WeightedMultigraph

end

end WeightedEdgeColoring
