import WeightedEdgeColoring.SubtwoMixedGraphCandidateRowMean

/-!
# Tiny mixed candidate row means

The same single-label mixed atom used for large slots carries a tiny
reservoir.  The candidate coefficient includes the physical edge weight,
so its expected row load is the local weighted reservoir use.
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

private theorem mixedTinyCandidateEdgeMean_eq
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
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c)
    (e : G.E) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c z e row) =
      rho /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega row.center c row.candidate *
        (if h : G.Inc row.center e then
          G.weight e *
            G.mixedGraphTinyAssign proposal edgeLabel qLaw R
              row.center c ⟨e, h⟩ row.candidate else 0) := by
  classical
  rcases row with ⟨center, candidate⟩
  by_cases hfst : center = G.fst e
  · subst center
    have hne : G.snd e ≠ G.fst e := (G.noLoop e).symm
    rw [Finset.sum_eq_single (G.snd e)]
    · simp only [mixedTinyCandidateEdgeUse]
      have htrue : True ∧ True := ⟨True.intro, True.intro⟩
      have hinc : G.Inc (G.fst e) e := Or.inl rfl
      have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.fst e)) =
          G.fstStarEdge e := by apply Subtype.ext; rfl
      simp_rw [dif_pos htrue]
      rw [dif_pos hinc]
      by_cases hy : G.mixedGraphTinyEdgeMass proposal s β e c = 0
      · have hle := G.mixedGraphTinyAssign_le_edgeMass
          proposal edgeLabel qLaw R hq0 hqmarg hqsingle
          (G.fst e) c (G.fstStarEdge e) candidate
        change G.mixedGraphTinyAssign proposal edgeLabel qLaw R
          (G.fst e) c (G.fstStarEdge e) candidate ≤
          G.mixedGraphTinyEdgeMass proposal s β e c at hle
        have hassign0 :
            G.mixedGraphTinyAssign proposal edgeLabel qLaw R
              (G.fst e) c (G.fstStarEdge e) candidate = 0 :=
          le_antisymm (by simpa only [hy] using hle)
            (G.mixedGraphTinyAssign_nonneg
              proposal edgeLabel qLaw R hq0
              (G.fst e) c (G.fstStarEdge e) candidate)
        simp [mixedGraphTinyProductMass, pairedOption, hy,
          hstarEdge, hassign0]
      · have hexpect := G.mixedGraphTinyProductMass_right_expectation
          proposal edgeLabel qLaw R rho omega
          hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
          homega0 homega1 e c hy candidate
        calc
          (∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c,
            G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
              omega (G.snd e) c z *
              (G.weight e * G.mixedGraphTinyProductMass
                proposal edgeLabel qLaw R rho omega e c candidate z)) =
              G.weight e *
                (∑ z : G.MixedGraphAtom
                  proposal edgeLabel qLaw R (G.snd e) c,
                  G.smoothedMixedGraphProbability
                    proposal edgeLabel qLaw R omega (G.snd e) c z *
                    G.mixedGraphTinyProductMass
                      proposal edgeLabel qLaw R rho omega e c candidate z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            ring
          _ = G.weight e *
              (rho * G.mixedGraphTinyAssign proposal edgeLabel qLaw R
                (G.fst e) c (G.fstStarEdge e) candidate /
                G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
                  omega (G.fst e) c candidate) := by rw [hexpect]
          _ = rho /
              G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
                omega (G.fst e) c candidate *
              (G.weight e * G.mixedGraphTinyAssign
                proposal edgeLabel qLaw R (G.fst e) c ⟨e, hinc⟩
                  candidate) := by simp [hstarEdge]; ring
    · intro source _ hsource
      have hnotMatch : ¬G.EndpointPairMatches (G.fst e) source e := by
        intro h
        rcases h with h | h
        · exact hsource h.2
        · exact hne h.1.symm
      have hedge0 : ∀ z : G.MixedGraphAtom
          proposal edgeLabel qLaw R source c,
          G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c z e ⟨G.fst e, candidate⟩ = 0 := by
        intro z
        unfold EndpointPairMatches at hnotMatch
        simp only [not_or] at hnotMatch
        simp [mixedTinyCandidateEdgeUse, hnotMatch.1, hnotMatch.2]
      simp only [hedge0, mul_zero, Finset.sum_const_zero]

    · simp
  · by_cases hsnd : center = G.snd e
    · subst center
      rw [Finset.sum_eq_single (G.fst e)]
      · have hnot1 : ¬(G.snd e = G.fst e ∧ G.fst e = G.snd e) :=
          fun h ↦ hfst h.1
        simp only [mixedTinyCandidateEdgeUse]
        have htrue : True ∧ True := ⟨True.intro, True.intro⟩
        have hinc : G.Inc (G.snd e) e := Or.inr rfl
        have hstarEdge : (⟨e, hinc⟩ : G.StarEdge (G.snd e)) =
            G.sndStarEdge e := by apply Subtype.ext; rfl
        simp_rw [dif_neg hnot1, dif_pos htrue]
        rw [dif_pos hinc]
        by_cases hy : G.mixedGraphTinyEdgeMass proposal s β e c = 0
        · have hle := G.mixedGraphTinyAssign_le_edgeMass
            proposal edgeLabel qLaw R hq0 hqmarg hqsingle
            (G.snd e) c (G.sndStarEdge e) candidate
          change G.mixedGraphTinyAssign proposal edgeLabel qLaw R
            (G.snd e) c (G.sndStarEdge e) candidate ≤
            G.mixedGraphTinyEdgeMass proposal s β e c at hle
          have hassign0 :
              G.mixedGraphTinyAssign proposal edgeLabel qLaw R
                (G.snd e) c (G.sndStarEdge e) candidate = 0 :=
            le_antisymm (by simpa only [hy] using hle)
              (G.mixedGraphTinyAssign_nonneg
                proposal edgeLabel qLaw R hq0
                (G.snd e) c (G.sndStarEdge e) candidate)
          simp [mixedGraphTinyProductMass, pairedOption, hy,
            hstarEdge, hassign0]
        · have hexpect := G.mixedGraphTinyProductMass_left_expectation
            proposal edgeLabel qLaw R rho omega
            hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
            homega0 homega1 e c hy candidate
          calc
            (∑ z : G.MixedGraphAtom
              proposal edgeLabel qLaw R (G.fst e) c,
              G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
                omega (G.fst e) c z *
                (G.weight e * G.mixedGraphTinyProductMass
                  proposal edgeLabel qLaw R rho omega e c z candidate)) =
                G.weight e *
                  (∑ z : G.MixedGraphAtom
                    proposal edgeLabel qLaw R (G.fst e) c,
                    G.smoothedMixedGraphProbability
                      proposal edgeLabel qLaw R omega (G.fst e) c z *
                      G.mixedGraphTinyProductMass
                        proposal edgeLabel qLaw R rho omega e c z candidate) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z _
              ring
            _ = G.weight e *
                (rho * G.mixedGraphTinyAssign proposal edgeLabel qLaw R
                  (G.snd e) c (G.sndStarEdge e) candidate /
                  G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
                    omega (G.snd e) c candidate) := by rw [hexpect]
            _ = rho /
                G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
                  omega (G.snd e) c candidate *
                (G.weight e * G.mixedGraphTinyAssign
                  proposal edgeLabel qLaw R (G.snd e) c ⟨e, hinc⟩
                    candidate) := by simp [hstarEdge]; ring
      · intro source _ hsource
        have hnotMatch : ¬G.EndpointPairMatches (G.snd e) source e := by
          intro h
          rcases h with h | h
          · exact hfst h.1
          · exact hsource h.2
        have hedge0 : ∀ z : G.MixedGraphAtom
            proposal edgeLabel qLaw R source c,
            G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e ⟨G.snd e, candidate⟩ = 0 := by
          intro z
          unfold EndpointPairMatches at hnotMatch
          simp only [not_or] at hnotMatch
          simp [mixedTinyCandidateEdgeUse, hnotMatch.1, hnotMatch.2]
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
          G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
            rho omega source c z e ⟨center, candidate⟩ = 0 := by
        intro source z
        have h := hnotMatch source
        unfold EndpointPairMatches at h
        simp only [not_or] at h
        simp [mixedTinyCandidateEdgeUse, h.1, h.2]
      simp only [hedge0, mul_zero, Finset.sum_const_zero]

theorem mixedTinyCandidateAtomMean_eq
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
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw R
            rho omega source c z (Sum.inr row)) =
      rho /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega row.center c row.candidate *
        (∑ e : G.StarEdge row.center, G.weight e.1 *
          G.mixedGraphTinyAssign proposal edgeLabel qLaw R
            row.center c e row.candidate) := by
  classical
  let k := rho /
    G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega row.center c row.candidate
  have hstar :
      (∑ e : G.StarEdge row.center, G.weight e.1 *
        G.mixedGraphTinyAssign proposal edgeLabel qLaw R
          row.center c e row.candidate) =
      ∑ e : G.E, if h : G.Inc row.center e then
        G.weight e *
          G.mixedGraphTinyAssign proposal edgeLabel qLaw R
            row.center c ⟨e, h⟩ row.candidate else 0 := by
    symm
    calc
      (∑ e : G.E, if h : G.Inc row.center e then
          G.weight e *
            G.mixedGraphTinyAssign proposal edgeLabel qLaw R
              row.center c ⟨e, h⟩ row.candidate else 0) =
          ∑ e ∈ Finset.univ.filter (G.Inc row.center),
            if h : G.Inc row.center e then
              G.weight e *
                G.mixedGraphTinyAssign proposal edgeLabel qLaw R
                  row.center c ⟨e, h⟩ row.candidate else 0 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases hinc : G.Inc row.center e <;> simp [hinc]
      _ = ∑ e : G.StarEdge row.center,
          if h : G.Inc row.center e.1 then
            G.weight e.1 *
              G.mixedGraphTinyAssign proposal edgeLabel qLaw R
                row.center c ⟨e.1, h⟩ row.candidate else 0 := by
        exact Finset.sum_subtype (p := G.Inc row.center)
          (Finset.univ.filter (G.Inc row.center))
          (by intro e; simp)
          (fun e ↦ if h : G.Inc row.center e then
            G.weight e *
              G.mixedGraphTinyAssign proposal edgeLabel qLaw R
                row.center c ⟨e, h⟩ row.candidate else 0)
      _ = ∑ e : G.StarEdge row.center, G.weight e.1 *
          G.mixedGraphTinyAssign proposal edgeLabel qLaw R
            row.center c e row.candidate := by
        apply Finset.sum_congr rfl
        intro e _
        simp [e.property]
  unfold mixedCandidateAtomUse
  change (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          (∑ e : G.E,
            G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e row)) = _
  calc
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          (∑ e : G.E,
            G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e row)) =
      ∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        ∑ e : G.E,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega source c z *
            G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
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
            G.mixedTinyCandidateEdgeUse proposal edgeLabel qLaw R
              rho omega source c z e row := by
      conv_lhs =>
        arg 2
        ext source
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = ∑ e : G.E,
          k * (if h : G.Inc row.center e then
            G.weight e *
              G.mixedGraphTinyAssign proposal edgeLabel qLaw R
                row.center c ⟨e, h⟩ row.candidate else 0) := by
      apply Finset.sum_congr rfl
      intro e _
      exact G.mixedTinyCandidateEdgeMean_eq
        proposal edgeLabel qLaw R rho omega hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 c row e
    _ = k * (∑ e : G.E, if h : G.Inc row.center e then
          G.weight e *
            G.mixedGraphTinyAssign proposal edgeLabel qLaw R
              row.center c ⟨e, h⟩ row.candidate else 0) := by
      rw [Finset.mul_sum]
    _ = rho /
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega row.center c row.candidate *
        (∑ e : G.StarEdge row.center, G.weight e.1 *
          G.mixedGraphTinyAssign proposal edgeLabel qLaw R
            row.center c e row.candidate) := by
      rw [← hstar]

theorem mixedTinyCandidateAtomMean_le_one_sub_omega
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
    (row : G.MixedTinyCandidateRow proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      ∑ z : G.MixedGraphAtom proposal edgeLabel qLaw R source c,
        G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
          omega source c z *
          G.mixedCandidateAtomUse proposal edgeLabel qLaw R
            rho omega source c z (Sum.inr row)) ≤
      rho / (1 - omega) := by
  rw [G.mixedTinyCandidateAtomMean_eq proposal edgeLabel qLaw R
    rho omega hq0 hqmarg hqsingle hqsum hs hqstep hr0 hleft
    homega0 homega1.le c row]
  let A := ∑ e : G.StarEdge row.center, G.weight e.1 *
    G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      row.center c e row.candidate
  let p := G.mixedGraphProbability proposal edgeLabel qLaw R
    row.center c row.candidate
  let lam := G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
    omega row.center c row.candidate
  have hA : A ≤ p := G.sum_weight_mul_mixedGraphTinyAssign_star_le
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft row.center c row.candidate
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun e _ ↦
    mul_nonneg (G.weight_nonneg e.1)
      (G.mixedGraphTinyAssign_nonneg proposal edgeLabel qLaw R
        hq0 row.center c e row.candidate)
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
