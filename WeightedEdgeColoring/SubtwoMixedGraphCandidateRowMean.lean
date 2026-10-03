import WeightedEdgeColoring.SubtwoMixedGraphCandidateMeans

/-!
# Actual mixed candidate row means

The source endpoint is averaged before selecting candidate slots.  This
reduces a candidate row mean to the center's one-atom local slot or tiny
reservoir load, with its true endpoint label still encoded in the atom.
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

theorem mixedGraphLargeAssign_le_edgeMass
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (v : G.V) (c : Color) (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a i ≤
      G.mixedGraphLargeEdgeMass proposal s β e.1 c := by
  have hsingle :
      G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a i ≤
        ∑ j, G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a j :=
    Finset.single_le_sum
      (fun j _ ↦ G.mixedGraphLargeAssign_nonneg
        proposal edgeLabel qLaw R hq0 v c e a j)
      (Finset.mem_univ i)
  exact hsingle.trans (G.sum_mixedGraphLargeAssign_le_edgeMass
    proposal edgeLabel qLaw R hq0 hqmarg hqsingle v c e a)

theorem sum_mixedGraphLargeAssign_star_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    (∑ e : G.StarEdge v,
      G.mixedGraphLargeAssign proposal edgeLabel qLaw R v c e a i) ≤
      G.mixedGraphProbability proposal edgeLabel qLaw R v c a := by
  simpa [mixedGraphLargeAssign, mixedGraphProbability] using
    G.sum_mixedLabelGraphLargeAssign_star_le
      (edgeLabel v) (fun e : G.StarEdge v ↦ proposal e.1 c)
      (qLaw v c) (R v c)
      (hq0 v c) (hqsum v c) (hqsingle v c)
      hs hqstep hr0 hleft a i

theorem sum_weight_mul_mixedGraphTinyAssign_star_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      G.mixedGraphTinyAssign proposal edgeLabel qLaw R v c e a) ≤
      G.mixedGraphProbability proposal edgeLabel qLaw R v c a := by
  simpa [mixedGraphTinyAssign, mixedGraphProbability] using
    G.sum_weight_mul_mixedLabelGraphTinyAssign_le
      (edgeLabel v) (fun e : G.StarEdge v ↦ proposal e.1 c)
      (qLaw v c) (R v c)
      (hq0 v c) (hqsum v c) (hqsingle v c)
      hs hqstep hr0 hleft a

private theorem mixedLargeCandidateEdgeMean_eq
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (c : Color)
    (row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c)
    (e : G.E) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c z e row) =
      rho /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega row.center c row.candidate *
        (if h : G.Inc row.center e then
          G.mixedGraphLargeAssign proposal edgeLabel qLaw R
            row.center c ⟨e, h⟩ row.candidate row.slot else 0) := by
  classical
  rcases row with ⟨center, candidate, slot⟩
  by_cases hfst : center = G.fst e
  · subst center
    have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
    rw [Finset.sum_eq_single (G.snd e)]
    · simp only [mixedLargeCandidateEdgeUse]
      have htrue : True ∧ True := ⟨True.intro, True.intro⟩
      have hinc : G.Inc (G.fst e) e := Or.inl rfl
      have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.fst e)) =
          G.fstStarEdge e := by apply Subtype.ext; rfl
      simp_rw [dif_pos htrue]
      rw [dif_pos hinc]
      by_cases hy : G.mixedGraphLargeEdgeMass proposal s β e c = 0
      · have hle := G.mixedGraphLargeAssign_le_edgeMass
          proposal edgeLabel qLaw R hq0 hqmarg hqsingle
          (G.fst e) c (G.fstStarEdge e) candidate slot
        change G.mixedGraphLargeAssign proposal edgeLabel qLaw R
          (G.fst e) c (G.fstStarEdge e) candidate slot ≤
          G.mixedGraphLargeEdgeMass proposal s β e c at hle
        have hassign0 :
            G.mixedGraphLargeAssign proposal edgeLabel qLaw R
              (G.fst e) c (G.fstStarEdge e) candidate slot = 0 :=
          le_antisymm (by simpa only [hy] using hle)
            (G.mixedGraphLargeAssign_nonneg
              proposal edgeLabel qLaw R hq0
              (G.fst e) c (G.fstStarEdge e) candidate slot)
        simp [mixedGraphLargeProductMass, pairedOption, hy,
          hstarEdge, hassign0]
      · rw [G.mixedGraphLargeProductMass_right_expectation
          proposal edgeLabel qLaw R rho omega
          hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
          homega0 homega1 e c hy candidate slot]
        simp [hstarEdge, mul_div_assoc', mul_comm, mul_left_comm]
    · intro source _hsource hsource
      have hnotMatch : ¬G.EndpointPairMatches (G.fst e) source e := by
        intro h
        rcases h with h | h
        · exact hsource h.2
        · exact hne h.1.symm
      have hedge0 : ∀ z : G.MixedGraphAtom
          proposal edgeLabel qLaw R source c,
          G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c z e ⟨G.fst e, candidate, slot⟩ = 0 := by
        intro z
        unfold EndpointPairMatches at hnotMatch
        simp only [not_or] at hnotMatch
        simp [mixedLargeCandidateEdgeUse, hnotMatch.1, hnotMatch.2]
      simp only [hedge0, mul_zero, Finset.sum_const_zero]
    · simp

  · by_cases hsnd : center = G.snd e
    · subst center
      rw [Finset.sum_eq_single (G.fst e)]
      · have hnot1 : ¬(G.snd e = G.fst e ∧ G.fst e = G.snd e) :=
          fun h ↦ hfst h.1
        simp only [mixedLargeCandidateEdgeUse]
        have htrue : True ∧ True := ⟨True.intro, True.intro⟩
        have hinc : G.Inc (G.snd e) e := Or.inr rfl
        have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.snd e)) =
            G.sndStarEdge e := by apply Subtype.ext; rfl
        simp_rw [dif_neg hnot1, dif_pos htrue]
        rw [dif_pos hinc]
        by_cases hy : G.mixedGraphLargeEdgeMass proposal s β e c = 0
        · have hle := G.mixedGraphLargeAssign_le_edgeMass
            proposal edgeLabel qLaw R hq0 hqmarg hqsingle
            (G.snd e) c (G.sndStarEdge e) candidate slot
          change G.mixedGraphLargeAssign proposal edgeLabel qLaw R
            (G.snd e) c (G.sndStarEdge e) candidate slot ≤
            G.mixedGraphLargeEdgeMass proposal s β e c at hle
          have hassign0 :
              G.mixedGraphLargeAssign proposal edgeLabel qLaw R
                (G.snd e) c (G.sndStarEdge e) candidate slot = 0 :=
            le_antisymm (by simpa only [hy] using hle)
              (G.mixedGraphLargeAssign_nonneg
                proposal edgeLabel qLaw R hq0
                (G.snd e) c (G.sndStarEdge e) candidate slot)
          simp [mixedGraphLargeProductMass, pairedOption, hy,
            hstarEdge, hassign0]
        · rw [G.mixedGraphLargeProductMass_left_expectation
            proposal edgeLabel qLaw R rho omega
            hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
            homega0 homega1 e c hy candidate slot]
          simp [hstarEdge, mul_div_assoc', mul_comm, mul_left_comm]
      · intro source _hsource hsource
        have hnotMatch : ¬G.EndpointPairMatches (G.snd e) source e := by
          intro h
          rcases h with h | h
          · exact hfst h.1
          · exact hsource h.2
        have hedge0 : ∀ z : G.MixedGraphAtom
            proposal edgeLabel qLaw R source c,
            G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e ⟨G.snd e, candidate, slot⟩ = 0 := by
          intro z
          unfold EndpointPairMatches at hnotMatch
          simp only [not_or] at hnotMatch
          simp [mixedLargeCandidateEdgeUse, hnotMatch.1, hnotMatch.2]
        simp only [hedge0, mul_zero, Finset.sum_const_zero]
      · simp
    · have hnotMatch : ∀ source,
          ¬G.EndpointPairMatches center source e := by
        intro source h
        rcases h with h | h
        · exact hfst h.1
        · exact hsnd h.1
      have hnotInc : ¬G.Inc center e := by
        intro hinc
        rcases hinc with h | h
        · exact hfst h.symm
        · exact hsnd h.symm
      rw [dif_neg hnotInc]
      have hedge0 : ∀ source
          (z : G.MixedGraphAtom proposal edgeLabel qLaw R source c),
          G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c z e ⟨center, candidate, slot⟩ = 0 := by
        intro source z
        have h := hnotMatch source
        unfold EndpointPairMatches at h
        simp only [not_or] at h
        simp [mixedLargeCandidateEdgeUse, h.1, h.2]
      simp only [hedge0, mul_zero, Finset.sum_const_zero]

theorem mixedLargeCandidateAtomMean_eq
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (c : Color)
    (row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw R
            rho omega source c z (Sum.inl row)) =
      rho /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega row.center c row.candidate *
        (∑ e : G.StarEdge row.center,
          G.mixedGraphLargeAssign proposal edgeLabel qLaw R
            row.center c e row.candidate row.slot) := by
  classical
  let k := rho /
    G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega row.center c row.candidate
  have hstar :
      (∑ e : G.StarEdge row.center,
        G.mixedGraphLargeAssign proposal edgeLabel qLaw R
          row.center c e row.candidate row.slot) =
      ∑ e : G.E, if h : G.Inc row.center e then
        G.mixedGraphLargeAssign proposal edgeLabel qLaw R
          row.center c ⟨e, h⟩ row.candidate row.slot else 0 := by
    symm
    calc
      (∑ e : G.E, if h : G.Inc row.center e then
          G.mixedGraphLargeAssign proposal edgeLabel qLaw R
            row.center c ⟨e, h⟩ row.candidate row.slot else 0) =
          ∑ e ∈ Finset.univ.filter (G.Inc row.center),
            if h : G.Inc row.center e then
              G.mixedGraphLargeAssign proposal edgeLabel qLaw R
                row.center c ⟨e, h⟩ row.candidate row.slot else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases hinc : G.Inc row.center e <;> simp [hinc]
      _ = ∑ e : G.StarEdge row.center,
          if h : G.Inc row.center e.1 then
            G.mixedGraphLargeAssign proposal edgeLabel qLaw R
              row.center c ⟨e.1, h⟩ row.candidate row.slot else 0 := by
        exact Finset.sum_subtype (p := G.Inc row.center)
          (Finset.univ.filter (G.Inc row.center))
          (by intro e; simp)
          (fun e ↦ if h : G.Inc row.center e then
            G.mixedGraphLargeAssign proposal edgeLabel qLaw R
              row.center c ⟨e, h⟩ row.candidate row.slot else 0)
      _ = ∑ e : G.StarEdge row.center,
          G.mixedGraphLargeAssign proposal edgeLabel qLaw R
            row.center c e row.candidate row.slot := by
        apply Finset.sum_congr rfl
        intro e _
        simp [e.property]
  unfold mixedCandidateAtomUse
  change (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          (∑ e : G.E,
            G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e row)) = _
  calc
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          (∑ e : G.E,
            G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e row)) =
      ∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        ∑ e : G.E,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega source c z *
            G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e row := by
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro z _
        rw [Finset.mul_sum]
    _ = ∑ e : G.E, ∑ source : G.V,
          ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
            G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
              omega source c z *
              G.mixedLargeCandidateEdgeUse proposal edgeLabel qLaw R
                rho omega source c z e row := by
      conv_lhs =>
        arg 2
        ext source
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = ∑ e : G.E,
          k * (if h : G.Inc row.center e then
            G.mixedGraphLargeAssign proposal edgeLabel qLaw R
              row.center c ⟨e, h⟩ row.candidate row.slot else 0) := by
      apply Finset.sum_congr rfl
      intro e _
      exact G.mixedLargeCandidateEdgeMean_eq
        proposal edgeLabel qLaw R rho omega hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 c row e
    _ = k * (∑ e : G.E, if h : G.Inc row.center e then
          G.mixedGraphLargeAssign proposal edgeLabel qLaw R
            row.center c ⟨e, h⟩ row.candidate row.slot else 0) := by
      rw [Finset.mul_sum]
    _ = rho /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega row.center c row.candidate *
        (∑ e : G.StarEdge row.center,
          G.mixedGraphLargeAssign proposal edgeLabel qLaw R
            row.center c e row.candidate row.slot) := by
      rw [← hstar]

theorem mixedLargeCandidateAtomMean_le_one_sub_omega
    (rho omega : ℝ)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hrho : 0 ≤ rho) (c : Color)
    (row : G.MixedLargeCandidateRow proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw R
            rho omega source c z (Sum.inl row)) ≤
      rho / (1 - omega) := by
  rw [G.mixedLargeCandidateAtomMean_eq proposal edgeLabel qLaw R
    rho omega hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
    homega0 homega1.le c row]
  let A := ∑ e : G.StarEdge row.center,
    G.mixedGraphLargeAssign proposal edgeLabel qLaw R
      row.center c e row.candidate row.slot
  let p := G.mixedGraphProbability proposal edgeLabel qLaw R
    row.center c row.candidate
  let lam := G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
    omega row.center c row.candidate
  have hA : A ≤ p := G.sum_mixedGraphLargeAssign_star_le
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft row.center c row.candidate row.slot
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun e _ ↦
    G.mixedGraphLargeAssign_nonneg proposal edgeLabel qLaw R
      hq0 row.center c e row.candidate row.slot
  have hlam : 0 < lam := G.smoothedMixedGraphProbability_pos
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1.le
    row.center c row.candidate
  have hone : 0 < 1 - omega := sub_pos.mpr homega1
  have hbase : (1 - omega) * p ≤ lam := by
    unfold lam smoothedMixedGraphProbability
    exact le_add_of_nonneg_right
      (div_nonneg homega0.le (Nat.cast_nonneg _))
  have hratio : A / lam ≤ 1 / (1 - omega) := by
    apply (div_le_div_iff₀ hlam hone).2
    calc
      A * (1 - omega) ≤ p * (1 - omega) :=
        mul_le_mul_of_nonneg_right hA hone.le
      _ = (1 - omega) * p := by ring
      _ ≤ lam := hbase
      _ = 1 * lam := by ring
  calc
    rho / lam * A = rho * (A / lam) := by ring
    _ ≤ rho * (1 / (1 - omega)) :=
      mul_le_mul_of_nonneg_left hratio hrho
    _ = rho / (1 - omega) := by ring

end WeightedMultigraph

end

end WeightedEdgeColoring
