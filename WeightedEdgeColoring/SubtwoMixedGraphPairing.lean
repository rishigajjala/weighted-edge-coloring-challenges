import WeightedEdgeColoring.SubtwoMixedGraphAtoms
import WeightedEdgeColoring.CoupledProfiles

/-!
# Two-endpoint coupling of mixed endpoint-label atoms

The local labels at the two ends of an edge may be different.  Their
conditional proposals therefore cannot be fed directly into the old
color-dependent coupling.  The mixed atoms restore the common edge mass
`s * proposal e c` at each end.  This module pairs those concrete atoms and
proves the resulting expected option mass is `rho * s * proposal e c`.
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

abbrev MixedGraphAtom (v : G.V) (c : Color) :=
  G.MixedLabelGraphAtom (edgeLabel v)
    (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) (R v c)

def mixedGraphProbability (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ :=
  G.mixedLabelGraphAtomProbability (edgeLabel v)
    (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) (R v c) a

def mixedGraphLargeAssign (v : G.V) (c : Color)
    (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c)
    (i : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  G.mixedLabelGraphLargeAssign (edgeLabel v)
    (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) (R v c) e a i

def mixedGraphTinyAssign (v : G.V) (c : Color)
    (e : G.StarEdge v)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ :=
  G.mixedLabelGraphTinyAssign (edgeLabel v)
    (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) (R v c) e a

def smoothedMixedGraphProbability (omega : ℝ)
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ :=
  (1 - omega) * G.mixedGraphProbability proposal edgeLabel qLaw R v c a +
    omega / Fintype.card (G.MixedGraphAtom proposal edgeLabel qLaw R v c)

theorem sum_smoothedMixedGraphProbability (omega : ℝ)
    (v : G.V) (c : Color) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R omega v c a) = 1 := by
  classical
  have hcard : Fintype.card
      (G.MixedGraphAtom proposal edgeLabel qLaw R v c) ≠ 0 := by
    exact Fintype.card_ne_zero
  have hcardR : (Fintype.card
      (G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ) ≠ 0 := by
    exact_mod_cast hcard
  unfold smoothedMixedGraphProbability
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsum := G.sum_mixedLabelGraphAtomProbability
    (edgeLabel v) (fun e : G.StarEdge v ↦ proposal e.1 c)
    (qLaw v c) (R v c)
  change (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R v c,
    G.mixedGraphProbability proposal edgeLabel qLaw R v c a) = 1 at hsum
  rw [hsum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcast : (↑(Fintype.card
      (G.MixedGraphAtom proposal edgeLabel qLaw R v c)) : ℝ) ≠ 0 := hcardR
  field_simp [hcast]
  ring

theorem smoothedMixedGraphProbability_pos
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (v : G.V) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R v c) :
    0 < G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega v c a := by
  have hbase : 0 ≤ G.mixedGraphProbability proposal edgeLabel qLaw R v c a :=
    G.mixedLabelGraphAtomProbability_nonneg
      (edgeLabel v) (fun e : G.StarEdge v ↦ proposal e.1 c)
      (qLaw v c) (R v c) (hq0 v c) (hqsum v c)
      (hqsingle v c) hs hqstep hr0 hleft a
  have hcard : 0 < (Fintype.card
      (G.MixedGraphAtom proposal edgeLabel qLaw R v c) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold smoothedMixedGraphProbability
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr homega1) hbase)
    (div_pos homega0 hcard)

def mixedGraphLargeEdgeMass (s β : ℝ) (e : G.E) (c : Color) : ℝ :=
  if β ≤ G.weight e then s * proposal e c else 0

def mixedGraphTinyEdgeMass (s β : ℝ) (e : G.E) (c : Color) : ℝ :=
  if G.weight e < β then s * proposal e c else 0

/-- The two local endpoint assignments couple against their common
unconditioned edge mass. -/
def mixedGraphLargeProductMass (rho omega : ℝ)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c)
    (i j : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  pairedOption rho
    (G.mixedGraphLargeEdgeMass proposal s β e c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.fst e) c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.snd e) c)
    (fun a i ↦ G.mixedGraphLargeAssign proposal edgeLabel qLaw R
      (G.fst e) c (G.fstStarEdge e) a i)
    (fun b j ↦ G.mixedGraphLargeAssign proposal edgeLabel qLaw R
      (G.snd e) c (G.sndStarEdge e) b j)
    a b i j

def mixedGraphTinyProductMass (rho omega : ℝ)
    (e : G.E) (c : Color)
    (a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c)
    (b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c) : ℝ :=
  pairedOption rho
    (G.mixedGraphTinyEdgeMass proposal s β e c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.fst e) c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.snd e) c)
    (fun a (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.fst e) c (G.fstStarEdge e) a)
    (fun b (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.snd e) c (G.sndStarEdge e) b)
    a b 0 0

theorem sum_mixedGraphLargeProductMass
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (e : G.E) (c : Color)
    (hy : G.mixedGraphLargeEdgeMass proposal s β e c ≠ 0) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega (G.fst e) c a * ∑ i,
        ∑ b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega (G.snd e) c b * ∑ j,
            G.mixedGraphLargeProductMass proposal edgeLabel qLaw R
              rho omega e c a b i j) =
      rho * G.mixedGraphLargeEdgeMass proposal s β e c := by
  unfold mixedGraphLargeProductMass
  apply sum_pairedOption
  · exact hy
  · intro a
    exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).ne'
  · intro b
    exact (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).ne'
  · simpa [mixedGraphLargeEdgeMass, mixedGraphLargeAssign] using
      G.sum_mixedLabelGraphLargeAssign
        (edgeLabel (G.fst e))
        (fun f : G.StarEdge (G.fst e) ↦ proposal f.1 c)
        (qLaw (G.fst e) c) (R (G.fst e) c)
        (hq0 (G.fst e) c) (hqmarg (G.fst e) c)
        (hqsingle (G.fst e) c) (G.fstStarEdge e)
  · simpa [mixedGraphLargeEdgeMass, mixedGraphLargeAssign] using
      G.sum_mixedLabelGraphLargeAssign
        (edgeLabel (G.snd e))
        (fun f : G.StarEdge (G.snd e) ↦ proposal f.1 c)
        (qLaw (G.snd e) c) (R (G.snd e) c)
        (hq0 (G.snd e) c) (hqmarg (G.snd e) c)
        (hqsingle (G.snd e) c) (G.sndStarEdge e)

theorem sum_mixedGraphTinyProductMass
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqmarg : ∀ v c (e : G.StarEdge v),
      (∑ S, if e ∈ S then qLaw v c S else 0) = proposal e.1 c)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ e ∈ S, edgeLabel v e = label)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (e : G.E) (c : Color)
    (hy : G.mixedGraphTinyEdgeMass proposal s β e c ≠ 0) :
    (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c,
      G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
        omega (G.fst e) c a *
        ∑ b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c,
          G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
            omega (G.snd e) c b *
            G.mixedGraphTinyProductMass proposal edgeLabel qLaw R
              rho omega e c a b) =
      rho * G.mixedGraphTinyEdgeMass proposal s β e c := by
  have hU :
      (∑ a : G.MixedGraphAtom proposal edgeLabel qLaw R (G.fst e) c,
        ∑ _i : Fin 1,
          G.mixedGraphTinyAssign proposal edgeLabel qLaw R
            (G.fst e) c (G.fstStarEdge e) a) =
        G.mixedGraphTinyEdgeMass proposal s β e c := by
    simpa [mixedGraphTinyEdgeMass, mixedGraphTinyAssign] using
      (G.sum_mixedLabelGraphTinyAssign
        (edgeLabel (G.fst e))
        (fun f : G.StarEdge (G.fst e) ↦ proposal f.1 c)
        (qLaw (G.fst e) c) (R (G.fst e) c)
        (hq0 (G.fst e) c) (hqmarg (G.fst e) c)
        (hqsingle (G.fst e) c) (G.fstStarEdge e))
  have hV :
      (∑ b : G.MixedGraphAtom proposal edgeLabel qLaw R (G.snd e) c,
        ∑ _j : Fin 1,
          G.mixedGraphTinyAssign proposal edgeLabel qLaw R
            (G.snd e) c (G.sndStarEdge e) b) =
        G.mixedGraphTinyEdgeMass proposal s β e c := by
    simpa [mixedGraphTinyEdgeMass, mixedGraphTinyAssign] using
      (G.sum_mixedLabelGraphTinyAssign
        (edgeLabel (G.snd e))
        (fun f : G.StarEdge (G.snd e) ↦ proposal f.1 c)
        (qLaw (G.snd e) c) (R (G.snd e) c)
        (hq0 (G.snd e) c) (hqmarg (G.snd e) c)
        (hqsingle (G.snd e) c) (G.sndStarEdge e))
  have h := sum_pairedOption rho
    (G.mixedGraphTinyEdgeMass proposal s β e c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.fst e) c)
    (G.smoothedMixedGraphProbability proposal edgeLabel qLaw R
      omega (G.snd e) c)
    (fun a (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.fst e) c (G.fstStarEdge e) a)
    (fun b (_ : Fin 1) ↦ G.mixedGraphTinyAssign proposal edgeLabel qLaw R
      (G.snd e) c (G.sndStarEdge e) b)
    hy
    (fun a ↦ (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.fst e) c a).ne')
    (fun b ↦ (G.smoothedMixedGraphProbability_pos
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 (G.snd e) c b).ne')
    hU hV
  simpa [mixedGraphTinyProductMass] using h

end WeightedMultigraph

end

end WeightedEdgeColoring
