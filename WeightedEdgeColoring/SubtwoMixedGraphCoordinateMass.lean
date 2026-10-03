import WeightedEdgeColoring.SubtwoMixedGraphTwoSidedCandidateEnvelope

/-!
# A bounded coordinate kernel for mixed labelled atoms

The complete raw option mass of one edge and one colour is a nonnegative
kernel of the two endpoint atoms.  Its pointwise bound is O(1/n), which is
the required input to the finite two-word block variance theorem.
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

def mixedGraphCoordinateOptionMass (rho omega : ℝ)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) : ℝ :=
  (∑ i, ∑ j,
      G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
        rho omega e c a b i j) +
    G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
      rho omega e c a b

theorem mixedGraphCoordinateOptionMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) :
    0 ≤ G.mixedGraphCoordinateOptionMass
      proposal edgeLabel qLaw R rho omega e c a b := by
  unfold mixedGraphCoordinateOptionMass
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact G.mixedGraphLargeProductMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 e c a b i j
  · exact G.mixedGraphTinyProductMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 e c a b

theorem n_mul_mixedGraphCoordinateOptionMass_le_orientedScale
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
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) :
    (n : ℝ) * G.mixedGraphCoordinateOptionMass
      proposal edgeLabel qLaw R rho omega e c a b ≤
      mixedCandidateOrientedScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0 := by
  let base := mixedGraphCandidateCapacityScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  have hlarge : (n : ℝ) *
      (∑ i, ∑ j, G.mixedGraphLargeProductMass
        proposal edgeLabel qLaw R rho omega e c a b i j) ≤
        (explicitLargeSlotBound β qstep r : ℝ) * base := by
    rw [Finset.mul_sum]
    calc
      (∑ i, (n : ℝ) * ∑ j,
        G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
          rho omega e c a b i j) ≤ ∑ _i, base := by
        apply Finset.sum_le_sum
        intro i _
        exact G.n_mul_sum_mixedGraphLargeProductMass_le_scale
          proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
          hs hqstep hr0 hleft homega0 homega1 hrho hC0
          hproposal0 hproposal e c a b i
      _ = (explicitLargeSlotBound β qstep r : ℝ) * base := by simp
  have htiny : (n : ℝ) * G.mixedGraphTinyProductMass
      proposal edgeLabel qLaw R rho omega e c a b ≤ base :=
    G.n_mul_mixedGraphTinyProductMass_le_scale
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal e c a b
  unfold mixedGraphCoordinateOptionMass
  dsimp [mixedCandidateOrientedScale]
  nlinarith [hlarge, htiny]

theorem expected_mixedGraphCoordinateOptionMass
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (f : G.StarEdge v),
      (∑ S, if f ∈ S then qLaw v c S else 0) = proposal f.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (e : G.E) (c : Color) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega (G.fst e) c a *
        ∑ b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega (G.snd e) c b *
            G.mixedGraphCoordinateOptionMass
              proposal edgeLabel qLaw R rho omega e c a b) =
      rho * s * proposal e c := by
  classical
  let pA := G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
    omega (G.fst e) c
  let pB := G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
    omega (G.snd e) c
  have hlarge :
      (∑ a, pA a * ∑ b, pB b *
        (∑ i, ∑ j, G.mixedGraphLargeProductMass
          proposal edgeLabel qLaw R rho omega e c a b i j)) =
        rho * G.mixedGraphLargeEdgeMass proposal s β e c := by
    have hreorder :
        (∑ a, pA a * ∑ b, pB b *
          (∑ i, ∑ j, G.mixedGraphLargeProductMass
            proposal edgeLabel qLaw R rho omega e c a b i j)) =
        ∑ a, pA a * ∑ i, ∑ b, pB b *
          ∑ j, G.mixedGraphLargeProductMass
            proposal edgeLabel qLaw R rho omega e c a b i j := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    rw [hreorder]
    by_cases hy : G.mixedGraphLargeEdgeMass proposal s β e c = 0
    · simp [mixedGraphLargeProductMass, pairedOption, hy]
    · exact G.sum_mixedGraphLargeProductMass
        proposal edgeLabel qLaw R hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 e c hy
  have htiny :
      (∑ a, pA a * ∑ b, pB b *
        G.mixedGraphTinyProductMass
          proposal edgeLabel qLaw R rho omega e c a b) =
        rho * G.mixedGraphTinyEdgeMass proposal s β e c := by
    by_cases hy : G.mixedGraphTinyEdgeMass proposal s β e c = 0
    · simp [mixedGraphTinyProductMass, pairedOption, hy]
    · exact G.sum_mixedGraphTinyProductMass
        proposal edgeLabel qLaw R hq0 hqmarg hqsingle hqsum
        hs hqstep hr0 hleft homega0 homega1 e c hy
  change (∑ a, pA a * ∑ b, pB b *
    G.mixedGraphCoordinateOptionMass
      proposal edgeLabel qLaw R rho omega e c a b) = _
  unfold mixedGraphCoordinateOptionMass
  simp only [mul_add, Finset.sum_add_distrib]
  have hsplit :
      G.mixedGraphLargeEdgeMass proposal s β e c +
        G.mixedGraphTinyEdgeMass proposal s β e c =
      s * proposal e c := by
    unfold mixedGraphLargeEdgeMass mixedGraphTinyEdgeMass
    by_cases hw : β ≤ G.weight e
    · simp [hw, not_lt.mpr hw]
    · simp [hw, lt_of_not_ge hw]
  rw [hlarge, htiny, ← mul_add, hsplit]
  ring

end WeightedMultigraph

end
end WeightedEdgeColoring
