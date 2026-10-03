import WeightedEdgeColoring.SubtwoMixedGraphCandidateRowCap

/-!
# Column sums for actual mixed labelled candidate rows

The mixed atom count is a fixed constant.  For one source and one edge,
only rows centered at the opposite endpoint can contribute.  Thus the
number of possibly positive large and tiny candidate coefficients per edge
is at most `M * (B + 1)`, where `M` is the fixed mixed atom alphabet and
`B` is the fixed padded large-slot count.  A star-degree bound then gives
an `O(n)` per-color selector column.
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

private theorem sum_mixedLargeCandidateRows
    (c : Color)
    (f : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c → ℝ) :
    (∑ row, f row) =
      ∑ v, ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        ∑ i, f { center := v, candidate := a, slot := i } := by
  calc
    (∑ row, f row) =
        ∑ x : Σ v : G.V,
          G.MixedGraphAtom proposal edgeLabel qLaw R v c ×
            Fin (explicitLargeSlotBound β qstep r),
          f ((G.mixedLargeCandidateRowEquiv
            proposal edgeLabel qLaw R c).symm x) := by
      exact Fintype.sum_equiv
        (G.mixedLargeCandidateRowEquiv proposal edgeLabel qLaw R c)
        _ _ (fun _ ↦ rfl)
    _ = ∑ v, ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        ∑ i, f { center := v, candidate := a, slot := i } := by
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      rfl

private theorem sum_mixedTinyCandidateRows
    (c : Color)
    (f : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c → ℝ) :
    (∑ row, f row) =
      ∑ v, ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        f { center := v, candidate := a } := by
  calc
    (∑ row, f row) =
        ∑ x : Σ v : G.V,
          G.MixedGraphAtom proposal edgeLabel qLaw R v c,
          f ((G.mixedTinyCandidateRowEquiv
            proposal edgeLabel qLaw R c).symm x) := by
      exact Fintype.sum_equiv
        (G.mixedTinyCandidateRowEquiv proposal edgeLabel qLaw R c)
        _ _ (fun _ ↦ rfl)
    _ = ∑ v, ∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
        f { center := v, candidate := a } := by
      simp only [Fintype.sum_sigma]
      rfl

def mixedCandidatePerColorColumnBound (D n : ℕ) : ℝ :=
  (D : ℝ) * n *
    (mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) : ℝ) *
    ((explicitLargeSlotBound β qstep r : ℝ) + 1)

private theorem sum_sigma_endpointPair_le
    {A : G.V → Type*} [∀ v, Fintype (A v)]
    (K : ℝ) (hcard : ∀ v, (Fintype.card (A v) : ℝ) ≤ K)
    (source : G.V) (e : G.E) (f : (Σ v, A v) → ℝ)
    (hunit : ∀ x, f x ≤ 1)
    (hsupp : ∀ x, ¬G.EndpointPairMatches x.1 source e → f x = 0) :
    (∑ x, f x) ≤ if G.Inc source e then K else 0 := by
  classical
  rw [Fintype.sum_sigma]
  by_cases hfst : source = G.fst e
  · subst source
    have hsnd : G.snd e ≠ G.fst e := (G.noLoop e).symm
    simp only [WeightedMultigraph.Inc, eq_self, true_or, if_true]
    calc
      (∑ v, ∑ a : A v, f ⟨v, a⟩) = ∑ a : A (G.snd e), f ⟨G.snd e, a⟩ := by
        apply Fintype.sum_eq_single (G.snd e)
        intro v hv
        apply Finset.sum_eq_zero
        intro a _
        exact hsupp ⟨v, a⟩ (by simp [EndpointPairMatches, hv, G.noLoop e])
      _ ≤ ∑ _a : A (G.snd e), (1 : ℝ) :=
        Finset.sum_le_sum fun a _ ↦ hunit ⟨G.snd e, a⟩
      _ = (Fintype.card (A (G.snd e)) : ℝ) := by simp
      _ ≤ K := hcard _
  · by_cases hsnd : source = G.snd e
    · subst source
      simp only [WeightedMultigraph.Inc, eq_self, or_true, if_true]
      calc
        (∑ v, ∑ a : A v, f ⟨v, a⟩) = ∑ a : A (G.fst e), f ⟨G.fst e, a⟩ := by
          apply Fintype.sum_eq_single (G.fst e)
          intro v hv
          apply Finset.sum_eq_zero
          intro a _
          exact hsupp ⟨v, a⟩ (by simp [EndpointPairMatches, hv, hfst])
        _ ≤ ∑ _a : A (G.fst e), (1 : ℝ) :=
          Finset.sum_le_sum fun a _ ↦ hunit ⟨G.fst e, a⟩
        _ = (Fintype.card (A (G.fst e)) : ℝ) := by simp
        _ ≤ K := hcard _
    · have hnone : ¬G.Inc source e := by
        simp [WeightedMultigraph.Inc, Ne.symm hfst, Ne.symm hsnd]
      rw [if_neg hnone]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro v _
      apply Finset.sum_eq_zero
      intro a _
      exact hsupp ⟨v, a⟩ (by simp [EndpointPairMatches, hfst, hsnd])

private theorem sum_scaledMixedLargeRows_edge_le
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
          (explicitLargeSlotBound β qstep r : ℝ)
      else 0 := by
  classical
  let scale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hscale : 0 < scale := mixedCandidateOrientedScale_pos hrho
    hs homega0 hC0
  rw [G.sum_mixedLargeCandidateRows proposal edgeLabel qLaw R c]
  let K : ℝ := (mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) : ℝ) *
    (explicitLargeSlotBound β qstep r : ℝ)
  let f : (Σ v : G.V,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c ×
        Fin (explicitLargeSlotBound β qstep r)) → ℝ :=
    fun x ↦ (n : ℝ) * G.mixedLargeCandidateEdgeUse
      proposal edgeLabel qLaw R rho omega source c sourceAtom e
      ⟨x.1, x.2.1, x.2.2⟩ / scale
  have hcard : ∀ v : G.V,
      (Fintype.card (G.MixedGraphAtom proposal edgeLabel qLaw R v c ×
        Fin (explicitLargeSlotBound β qstep r)) : ℝ) ≤ K := by
    intro v
    simpa only [K, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
      mul_le_mul_of_nonneg_right
        (by exact_mod_cast (G.mixedGraphAtom_card_le
          proposal edgeLabel qLaw R v c))
        (Nat.cast_nonneg _)
  have hunit : ∀ x, f x ≤ 1 := by
    intro x
    rcases x with ⟨v, a, i⟩
    apply (div_le_one hscale).2
    exact G.n_mul_mixedLargeCandidateEdgeUse_le_scale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
      hproposal0 hproposal source c sourceAtom e ⟨v, a, i⟩
  have hsupp : ∀ x, ¬G.EndpointPairMatches x.1 source e → f x = 0 := by
    intro x hnot
    rcases x with ⟨v, a, i⟩
    unfold EndpointPairMatches at hnot
    simp only [not_or] at hnot
    simp [f, mixedLargeCandidateEdgeUse, hnot.1, hnot.2]
  have hsum := G.sum_sigma_endpointPair_le K hcard source e f hunit hsupp
  simpa only [K, f, Fintype.sum_sigma, Fintype.sum_prod_type] using hsum

private theorem sum_scaledMixedTinyRows_edge_le
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
          (β := β) (qstep := qstep) (r := r) : ℝ)
      else 0 := by
  classical
  let scale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hscale : 0 < scale := mixedCandidateOrientedScale_pos hrho
    hs homega0 hC0
  rw [G.sum_mixedTinyCandidateRows proposal edgeLabel qLaw R c]
  let K : ℝ := (mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) : ℝ)
  let f : (Σ v : G.V,
      G.MixedGraphAtom proposal edgeLabel qLaw R v c) → ℝ :=
    fun x ↦ (n : ℝ) * G.mixedTinyCandidateEdgeUse
      proposal edgeLabel qLaw R rho omega source c sourceAtom e
      ⟨x.1, x.2⟩ / scale
  have hcard : ∀ v : G.V,
      (Fintype.card (G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ)
        ≤ K := by
    intro v
    dsimp [K]
    exact_mod_cast (G.mixedGraphAtom_card_le
      proposal edgeLabel qLaw R v c)
  have hunit : ∀ x, f x ≤ 1 := by
    intro x
    rcases x with ⟨v, a⟩
    apply (div_le_one hscale).2
    exact G.n_mul_mixedTinyCandidateEdgeUse_le_scale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs.le hqstep hr0 hleft homega0 homega1 hrho.le hC0.le
      hproposal0 hproposal source c sourceAtom e ⟨v, a⟩
  have hsupp : ∀ x, ¬G.EndpointPairMatches x.1 source e → f x = 0 := by
    intro x hnot
    rcases x with ⟨v, a⟩
    unfold EndpointPairMatches at hnot
    simp only [not_or] at hnot
    simp [f, mixedTinyCandidateEdgeUse, hnot.1, hnot.2]
  have hsum := G.sum_sigma_endpointPair_le K hcard source e f hunit hsupp
  simpa only [K, f, Fintype.sum_sigma] using hsum

theorem sum_scaledMixedCandidateAtomUse_le_column
    {n D : ℕ} (hn : 0 < n)
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
    (hdegree : ∀ v, Fintype.card (G.StarEdge v) ≤ D * n)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c) :
    (∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        (mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0)
        rho omega source c sourceAtom row) ≤
      mixedCandidatePerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) D n := by
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
        M * B * (Fintype.card (G.StarEdge source) : ℝ) := by
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
      _ ≤ ∑ e, if G.Inc source e then M * B else 0 := by
        apply Finset.sum_le_sum
        intro e _
        simpa [scale, M, B] using
          G.sum_scaledMixedLargeRows_edge_le proposal edgeLabel qLaw R
            hn hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
            homega0 homega1 hrho hC0 hproposal0 hproposal
            source c sourceAtom e
      _ = M * B * (Fintype.card (G.StarEdge source) : ℝ) := by
        calc
          (∑ e, if G.Inc source e then M * B else 0) =
              ∑ e ∈ Finset.univ.filter (G.Inc source), M * B := by
            rw [← Finset.sum_filter]
          _ = ∑ _e : G.StarEdge source, M * B := by
            exact Finset.sum_subtype
              (Finset.univ.filter (G.Inc source))
              (by intro e; simp) (fun _e : G.E ↦ M * B)
          _ = M * B * (Fintype.card (G.StarEdge source) : ℝ) := by
            simp
            ring
  have htiny :
      (∑ row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inr row)) ≤
        M * (Fintype.card (G.StarEdge source) : ℝ) := by
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
      _ ≤ ∑ e, if G.Inc source e then M else 0 := by
        apply Finset.sum_le_sum
        intro e _
        simpa [scale, M] using
          G.sum_scaledMixedTinyRows_edge_le proposal edgeLabel qLaw R
            hn hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
            homega0 homega1 hrho hC0 hproposal0 hproposal
            source c sourceAtom e
      _ = M * (Fintype.card (G.StarEdge source) : ℝ) := by
        calc
          (∑ e, if G.Inc source e then M else 0) =
              ∑ e ∈ Finset.univ.filter (G.Inc source), M := by
            rw [← Finset.sum_filter]
          _ = ∑ _e : G.StarEdge source, M := by
            exact Finset.sum_subtype
              (Finset.univ.filter (G.Inc source))
              (by intro e; simp) (fun _e : G.E ↦ M)
          _ = M * (Fintype.card (G.StarEdge source) : ℝ) := by
            simp
            ring
  rw [Fintype.sum_sum_type]
  have hdegreeR : (Fintype.card (G.StarEdge source) : ℝ) ≤
      (D : ℝ) * n := by
    exact_mod_cast (hdegree source)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  calc
    (∑ row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inl row)) +
      (∑ row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n scale
          rho omega source c sourceAtom (Sum.inr row)) ≤
        M * B * (Fintype.card (G.StarEdge source) : ℝ) +
          M * (Fintype.card (G.StarEdge source) : ℝ) :=
      add_le_add hlarge htiny
    _ ≤ mixedCandidatePerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) D n := by
      unfold mixedCandidatePerColorColumnBound
      dsimp [M, B]
      nlinarith [mul_nonneg hM hB]

theorem sum_scaledMixedCandidateAtomUse_mul_le_column
    {L n D : ℕ} (hL : 0 < L) (hn : 0 < n)
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
    (hdegree : ∀ v, Fintype.card (G.StarEdge v) ≤ D * n)
    (source : G.V) (c : Color)
    (sourceAtom : G.MixedGraphAtom proposal edgeLabel qLaw R source c) :
    (∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0)
        rho omega source c sourceAtom row) ≤
      mixedCandidatePerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) D n := by
  let baseScale := mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hbase : 0 < baseScale := mixedCandidateOrientedScale_pos
    hrho hs homega0 hC0
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hscale : 0 < (L : ℝ) * baseScale := by positivity
  calc
    (∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
        ((L : ℝ) * baseScale) rho omega source c sourceAtom row) ≤
        ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
          G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
            baseScale rho omega source c sourceAtom row := by
      apply Finset.sum_le_sum
      intro row _
      unfold scaledMixedCandidateAtomUse
      apply (div_le_div_iff₀ hscale hbase).2
      have huse := G.mixedCandidateAtomUse_nonneg
        proposal edgeLabel qLaw R hq0 hqsum hqsingle
        hs.le hqstep hr0 hleft homega0 homega1 hrho.le hproposal0
        source c sourceAtom row
      have hnum : 0 ≤ (n : ℝ) *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw R
            rho omega source c sourceAtom row :=
        mul_nonneg (Nat.cast_nonneg n) huse
      exact mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_right hLreal hbase.le) hnum
    _ ≤ mixedCandidatePerColorColumnBound (Label := Label)
        (β := β) (qstep := qstep) (r := r) D n := by
      simpa [baseScale] using
        G.sum_scaledMixedCandidateAtomUse_le_column
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs hqstep hr0 hleft homega0 homega1 hrho hC0
          hproposal0 hproposal hdegree source c sourceAtom

theorem sum_scaledMixedPackedWordCandidateUse_mul_le_column
    {L n D : ℕ} (hL : 0 < L) (hn : 0 < n)
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
    (hdegree : ∀ v, Fintype.card (G.StarEdge v) ≤ D * n)
    (source : G.V)
    (packed : G.MixedGraphPackedState proposal edgeLabel qLaw R) :
    (∑ c : Color,
      ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
          ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0)
          rho omega source c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R source packed c)
          row) ≤
      (Fintype.card Color : ℝ) *
        mixedCandidatePerColorColumnBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) D n := by
  calc
    (∑ c : Color,
      ∑ row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R n
          ((L : ℝ) * mixedCandidateOrientedScale (Label := Label)
            (β := β) (qstep := qstep) (r := r) rho s omega C0)
          rho omega source c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R source packed c)
          row) ≤
        ∑ _c : Color,
          mixedCandidatePerColorColumnBound (Label := Label)
            (β := β) (qstep := qstep) (r := r) D n := by
      apply Finset.sum_le_sum
      intro c _
      exact G.sum_scaledMixedCandidateAtomUse_mul_le_column
        proposal edgeLabel qLaw R hL hn hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 hrho hC0
        hproposal0 hproposal hdegree source c
        (G.decodeMixedGraphAtom proposal edgeLabel qLaw R source packed c)
    _ = (Fintype.card Color : ℝ) *
        mixedCandidatePerColorColumnBound (Label := Label)
          (β := β) (qstep := qstep) (r := r) D n := by simp

end WeightedMultigraph

end

end WeightedEdgeColoring
