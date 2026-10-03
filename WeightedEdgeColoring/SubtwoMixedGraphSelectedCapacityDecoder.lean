import WeightedEdgeColoring.SubtwoMixedGraphCandidateSelection

/-!
# Decode selected mixed candidate capacities

The finite selector controls coefficients scaled by `n / scale`.
The actual large-slot matching and tiny-reservoir steps consume raw sums
of paired option masses.  The following identities and bounds transfer
the same selected packed word to those raw sums.
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

def selectedMixedCandidateCapacityLoad
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (c : Color)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) : ℝ :=
  ∑ source : G.V,
    G.mixedCandidateAtomUse proposal edgeLabel qLaw R rho omega
      source c
      (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
        source (choice source) c) row

def selectedMixedLargeCandidateRow
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (center : G.V) (c : Color)
    (slot : Fin (explicitLargeSlotBound β qstep r)) :
    G.MixedLargeCandidateRow proposal edgeLabel qLaw R c :=
  ⟨center,
    G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      center (choice center) c, slot⟩

def selectedMixedTinyCandidateRow
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (center : G.V) (c : Color) :
    G.MixedTinyCandidateRow proposal edgeLabel qLaw R c :=
  ⟨center,
    G.decodeMixedGraphAtom proposal edgeLabel qLaw R
      center (choice center) c⟩

theorem sum_scaledMixedCandidateAtomUse_eq_selectedLoad
    (n : ℕ) (scale rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (c : Color)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c) :
    (∑ source : G.V,
      G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
        n scale rho omega source c
        (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
          source (choice source) c) row) =
      (n : ℝ) *
        G.selectedMixedCandidateCapacityLoad
          proposal edgeLabel qLaw R rho omega choice c row / scale := by
  simp_rw [scaledMixedCandidateAtomUse]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  rfl

theorem selectedMixedCandidateCapacityLoad_lt
    {n : ℕ} (hn : 0 < n)
    (scale rho omega deviation : ℝ) (hscale : 0 < scale)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (c : Color)
    (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c)
    (hrow :
      (∑ source : G.V,
        G.scaledMixedCandidateAtomUse proposal edgeLabel qLaw R
          n scale rho omega source c
          (G.decodeMixedGraphAtom proposal edgeLabel qLaw R
            source (choice source) c) row) <
        (n : ℝ) * (rho / (1 - omega)) / scale + deviation) :
    G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
      rho omega choice c row <
        rho / (1 - omega) + scale / (n : ℝ) * deviation := by
  rw [G.sum_scaledMixedCandidateAtomUse_eq_selectedLoad
    proposal edgeLabel qLaw R n scale rho omega choice c row] at hrow
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let base := rho / (1 - omega)
  have hrow' :
      (n : ℝ) * G.selectedMixedCandidateCapacityLoad
          proposal edgeLabel qLaw R rho omega choice c row / scale <
        ((n : ℝ) * base + scale * deviation) / scale := by
    calc
      _ < (n : ℝ) * base / scale + deviation := hrow
      _ = ((n : ℝ) * base + scale * deviation) / scale := by
        field_simp
        <;> ring
  have hnum := (div_lt_div_iff_of_pos_right hscale).1 hrow'
  have hnum' :
      G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
          rho omega choice c row * (n : ℝ) <
        (n : ℝ) * base + scale * deviation := by
    simpa [mul_comm] using hnum
  calc
    _ < ((n : ℝ) * base + scale * deviation) / (n : ℝ) :=
      (lt_div_iff₀ hnR).2 hnum'
    _ = _ := by
      unfold base
      field_simp
      <;> ring

theorem exists_mixedGraphPackedWord_candidateRawLoads_lt
    {L n D : ℕ} (hL : 0 < L) (hmult : G.PairMultiplicityAtMost L)
    (hn : 0 < n)
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
    (hdegree : ∀ v, Fintype.card (G.StarEdge v) ≤ D * n) :
    let scale := (L : ℝ) * mixedCandidateOrientedScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
    let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
    let columnBound := mixedCandidatePerColorColumnBound (Label := Label)
      (β := β) (qstep := qstep) (r := r) D n
    let deviation := FinitePartialResamplingNumerics.packingDeviation
      meanBound (Fintype.card Color * columnBound)
    ∃ choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R,
      (∀ v, 0 < G.paddedMixedGraphWordProbability
        proposal edgeLabel qLaw R omega v (choice v)) ∧
      ∀ c (row : G.MixedCandidateRowAt proposal edgeLabel qLaw R c),
        G.selectedMixedCandidateCapacityLoad proposal edgeLabel qLaw R
          rho omega choice c row <
            rho / (1 - omega) + scale / (n : ℝ) * deviation := by
  classical
  let scale := (L : ℝ) * mixedCandidateOrientedScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let meanBound := (n : ℝ) * (rho / (1 - omega)) / scale
  let columnBound := mixedCandidatePerColorColumnBound (Label := Label)
    (β := β) (qstep := qstep) (r := r) D n
  let deviation := FinitePartialResamplingNumerics.packingDeviation
    meanBound (Fintype.card Color * columnBound)
  obtain ⟨choice, hpos, hrows⟩ :=
    G.exists_mixedGraphPackedWord_candidateRows_lt
      proposal edgeLabel qLaw R hL hmult hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal hdegree
  refine ⟨choice, hpos, ?_⟩
  intro c row
  have hscale : 0 < scale := by
    have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
    exact mul_pos hLreal
      (mixedCandidateOrientedScale_pos hrho hs homega0 hC0)
  have hrow := hrows ⟨c, row⟩
  exact G.selectedMixedCandidateCapacityLoad_lt
    proposal edgeLabel qLaw R hn scale rho omega deviation hscale
    choice c row hrow

end WeightedMultigraph

end

end WeightedEdgeColoring
