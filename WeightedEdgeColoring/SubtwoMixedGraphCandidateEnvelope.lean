import WeightedEdgeColoring.SubtwoMixedGraphCandidateRows

/-!
# Diffuse edge envelope after endpoint-label mixing

The conditional proposal for a rare label can be large.  The mixed atom
returns to the original edge mass before the paired-option denominator is
formed.  This gives an oriented candidate coefficient bound using only the
original diffuse proposal and the fixed mixed atom alphabet.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

private theorem mixed_scaled_sum_pair_le
    {I : Type*} [Fintype I]
    (N rho y lambdaP lambdaQ L cap a : ℝ) (b : I → ℝ)
    (hN0 : 0 ≤ N) (hrho0 : 0 ≤ rho) (hy0 : 0 ≤ y)
    (hlambdaP : 0 < lambdaP) (hlambdaQ : 0 < lambdaQ)
    (hL0 : 0 ≤ L) (hcap0 : 0 ≤ cap)
    (hLP : 1 ≤ L * lambdaP) (hLQ : 1 ≤ L * lambdaQ)
    (ha0 : 0 ≤ a) (ha : a ≤ y)
    (hb0 : ∀ i, 0 ≤ b i) (hb : ∑ i, b i ≤ y)
    (hNy : N * y ≤ cap) :
    N * (∑ i, rho * a * b i / (y * lambdaP * lambdaQ)) ≤
      rho * cap * L ^ 2 := by
  by_cases hy : y = 0
  · have haZero : a = 0 := le_antisymm (ha.trans_eq hy) ha0
    simp [hy, haZero]
    positivity
  have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hbsum0 : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ ↦ hb0 i
  have haDiv : a / lambdaP ≤ y * L := by
    apply (div_le_iff₀ hlambdaP).2
    calc
      a ≤ y := ha
      _ ≤ y * (L * lambdaP) := by
        simpa using mul_le_mul_of_nonneg_left hLP hy0
      _ = y * L * lambdaP := by ring
  have hbDiv : (∑ i, b i) / lambdaQ ≤ y * L := by
    apply (div_le_iff₀ hlambdaQ).2
    calc
      (∑ i, b i) ≤ y := hb
      _ ≤ y * (L * lambdaQ) := by
        simpa using mul_le_mul_of_nonneg_left hLQ hy0
      _ = y * L * lambdaQ := by ring
  have hrewrite :
      (∑ i, rho * a * b i / (y * lambdaP * lambdaQ)) =
        (rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ) := by
    calc
      (∑ i, rho * a * b i / (y * lambdaP * lambdaQ)) =
          ∑ i, (rho / y) * (a / lambdaP) * (b i / lambdaQ) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [hy, hlambdaP.ne', hlambdaQ.ne']
      _ = (rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ) := by
        rw [Finset.sum_div, Finset.mul_sum]
  rw [hrewrite]
  have hrhoDiv0 : 0 ≤ rho / y := div_nonneg hrho0 hypos.le
  have haDiv0 : 0 ≤ a / lambdaP := div_nonneg ha0 hlambdaP.le
  have hbDiv0 : 0 ≤ (∑ i, b i) / lambdaQ :=
    div_nonneg hbsum0 hlambdaQ.le
  calc
    N * ((rho / y) * (a / lambdaP) * ((∑ i, b i) / lambdaQ)) ≤
        N * ((rho / y) * (y * L) * (y * L)) := by
      gcongr
    _ = rho * (N * y) * L ^ 2 := by field_simp [hy]
    _ ≤ rho * cap * L ^ 2 := by gcongr

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

def mixedGraphCandidateCapacityScale
    (rho s omega C0 : ℝ) : ℝ :=
  rho * s * C0 *
    ((mixedGraphAtomBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) : ℝ) / omega) ^ 2

theorem n_mul_sum_mixedGraphLargeProductMass_le_scale
    {n : ℕ} (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c)
    (i : Fin (explicitLargeSlotBound β qstep r)) :
    (n : ℝ) * (∑ j,
      G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
        rho omega e c a b i j) ≤
      mixedGraphCandidateCapacityScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  let y := G.mixedGraphLargeEdgeMass proposal s β e c
  let L : ℝ := (mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) : ℝ) / omega
  let lambdaP := G.smoothedMixedGraphProbability
    proposal edgeLabel qLaw R omega (G.fst e) c a
  let lambdaQ := G.smoothedMixedGraphProbability
    proposal edgeLabel qLaw R omega (G.snd e) c b
  let aP := G.mixedGraphLargeAssign proposal edgeLabel qLaw R
    (G.fst e) c (G.fstStarEdge e) a i
  let bQ := fun j ↦ G.mixedGraphLargeAssign proposal edgeLabel qLaw R
    (G.snd e) c (G.sndStarEdge e) b j
  have hy0 : 0 ≤ y := by
    unfold y mixedGraphLargeEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_rfl
  have hNy : (n : ℝ) * y ≤ s * C0 := by
    unfold y mixedGraphLargeEdgeMass
    split
    · calc
        (n : ℝ) * (s * proposal e c) ≤
            (n : ℝ) * (s * (C0 / (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
          exact mul_le_mul_of_nonneg_left (hproposal e c) hs
        _ = s * C0 := by field_simp [Nat.ne_of_gt hn]
    · simpa using mul_nonneg hs hC0
  have hP0 : 0 ≤ aP :=
    G.mixedGraphLargeAssign_nonneg proposal edgeLabel qLaw R
      hq0 (G.fst e) c (G.fstStarEdge e) a i
  have hP : aP ≤ y := by
    have hsingle : aP ≤ ∑ j,
        G.mixedGraphLargeAssign proposal edgeLabel qLaw R
          (G.fst e) c (G.fstStarEdge e) a j :=
      Finset.single_le_sum
        (fun j _ ↦ G.mixedGraphLargeAssign_nonneg
          proposal edgeLabel qLaw R hq0
          (G.fst e) c (G.fstStarEdge e) a j)
        (Finset.mem_univ i)
    exact hsingle.trans
      (G.sum_mixedGraphLargeAssign_le_edgeMass
        proposal edgeLabel qLaw R hq0 hqmarg hqsingle
        (G.fst e) c (G.fstStarEdge e) a)
  have hQ0 : ∀ j, 0 ≤ bQ j := fun j ↦
    G.mixedGraphLargeAssign_nonneg proposal edgeLabel qLaw R
      hq0 (G.snd e) c (G.sndStarEdge e) b j
  have hQ : (∑ j, bQ j) ≤ y :=
    G.sum_mixedGraphLargeAssign_le_edgeMass
      proposal edgeLabel qLaw R hq0 hqmarg hqsingle
      (G.snd e) c (G.sndStarEdge e) b
  have hlamP : 0 < lambdaP :=
    G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a
  have hlamQ : 0 < lambdaQ :=
    G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b
  have hLP : 1 ≤ L * lambdaP :=
    G.one_le_mixedGraphAtomRatio_mul_smoothedProbability
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a
  have hLQ : 1 ≤ L * lambdaQ :=
    G.one_le_mixedGraphAtomRatio_mul_smoothedProbability
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b
  have hL0 : 0 ≤ L := by
    unfold L mixedGraphAtomBound
    positivity
  have hpair := mixed_scaled_sum_pair_le
    (n : ℝ) rho y lambdaP lambdaQ L (s * C0) aP bQ
    (Nat.cast_nonneg n) hrho hy0 hlamP hlamQ hL0
    (mul_nonneg hs hC0) hLP hLQ hP0 hP hQ0 hQ hNy
  by_cases hy : y = 0
  · have hscale0 : 0 ≤
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
      unfold mixedGraphCandidateCapacityScale
      positivity
    simpa [mixedGraphLargeProductMass, pairedOption, y, hy] using hscale0
  · simpa [mixedGraphLargeProductMass, pairedOption, y, L,
      mixedGraphCandidateCapacityScale, hy, aP, bQ, lambdaP, lambdaQ,
      mul_assoc]
      using hpair

theorem n_mul_mixedGraphTinyProductMass_le_scale
    {n : ℕ} (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) :
    (n : ℝ) * G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
      rho omega e c a b ≤
      mixedGraphCandidateCapacityScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  let y := G.mixedGraphTinyEdgeMass proposal s β e c
  let L : ℝ := (mixedGraphAtomBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) : ℝ) / omega
  let lambdaP := G.smoothedMixedGraphProbability
    proposal edgeLabel qLaw R omega (G.fst e) c a
  let lambdaQ := G.smoothedMixedGraphProbability
    proposal edgeLabel qLaw R omega (G.snd e) c b
  let aP := G.mixedGraphTinyAssign proposal edgeLabel qLaw R
    (G.fst e) c (G.fstStarEdge e) a
  let bQ : Fin 1 → ℝ := fun _ ↦ G.mixedGraphTinyAssign
    proposal edgeLabel qLaw R (G.snd e) c (G.sndStarEdge e) b
  have hy0 : 0 ≤ y := by
    unfold y mixedGraphTinyEdgeMass
    split
    · exact mul_nonneg hs (hproposal0 e c)
    · exact le_rfl
  have hNy : (n : ℝ) * y ≤ s * C0 := by
    unfold y mixedGraphTinyEdgeMass
    split
    · calc
        (n : ℝ) * (s * proposal e c) ≤
            (n : ℝ) * (s * (C0 / (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
          exact mul_le_mul_of_nonneg_left (hproposal e c) hs
        _ = s * C0 := by field_simp [Nat.ne_of_gt hn]
    · simpa using mul_nonneg hs hC0
  have hP0 : 0 ≤ aP :=
    G.mixedGraphTinyAssign_nonneg proposal edgeLabel qLaw R
      hq0 (G.fst e) c (G.fstStarEdge e) a
  have hP : aP ≤ y :=
    G.mixedGraphTinyAssign_le_edgeMass
      proposal edgeLabel qLaw R hq0 hqmarg hqsingle
      (G.fst e) c (G.fstStarEdge e) a
  have hQ0 : ∀ j, 0 ≤ bQ j := fun _ ↦
    G.mixedGraphTinyAssign_nonneg proposal edgeLabel qLaw R
      hq0 (G.snd e) c (G.sndStarEdge e) b
  have hQ : (∑ j, bQ j) ≤ y := by
    simpa [bQ] using
      (G.mixedGraphTinyAssign_le_edgeMass
        proposal edgeLabel qLaw R hq0 hqmarg hqsingle
        (G.snd e) c (G.sndStarEdge e) b)
  have hlamP : 0 < lambdaP :=
    G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a
  have hlamQ : 0 < lambdaQ :=
    G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b
  have hLP : 1 ≤ L * lambdaP :=
    G.one_le_mixedGraphAtomRatio_mul_smoothedProbability
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a
  have hLQ : 1 ≤ L * lambdaQ :=
    G.one_le_mixedGraphAtomRatio_mul_smoothedProbability
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b
  have hL0 : 0 ≤ L := by
    unfold L mixedGraphAtomBound
    positivity
  have hpair := mixed_scaled_sum_pair_le
    (n : ℝ) rho y lambdaP lambdaQ L (s * C0) aP bQ
    (Nat.cast_nonneg n) hrho hy0 hlamP hlamQ hL0
    (mul_nonneg hs hC0) hLP hLQ hP0 hP hQ0 hQ hNy
  by_cases hy : y = 0
  · have hscale0 : 0 ≤
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
      unfold mixedGraphCandidateCapacityScale
      positivity
    simpa [mixedGraphTinyProductMass, pairedOption, y, hy] using hscale0
  · simpa [mixedGraphTinyProductMass, pairedOption, y, L,
      mixedGraphCandidateCapacityScale, hy, aP, bQ, lambdaP, lambdaQ,
      mul_assoc] using hpair

theorem n_mul_weight_mul_mixedGraphTinyProductMass_le
    {n : ℕ} (hn : 0 < n)
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hC0 : 0 ≤ C0)
    (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) :
    (n : ℝ) * (G.weight e *
      G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
        rho omega e c a b) ≤
      G.weight e * mixedGraphCandidateCapacityScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  have hproduct := G.n_mul_mixedGraphTinyProductMass_le_scale
    proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho hC0
    hproposal0 hproposal e c a b
  calc
    (n : ℝ) * (G.weight e *
      G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
        rho omega e c a b) =
      G.weight e * ((n : ℝ) *
        G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
          rho omega e c a b) := by ring
    _ ≤ G.weight e * mixedGraphCandidateCapacityScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 :=
      mul_le_mul_of_nonneg_left hproduct (G.weight_nonneg e)

end WeightedMultigraph

end

end WeightedEdgeColoring
