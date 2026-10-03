import WeightedEdgeColoring.SubtwoMixedGraphSelectedOptionLoads
import WeightedEdgeColoring.OptionNormalization

/-!
# A probability distribution on each selected physical edge

All selected mixed large and tiny options for an edge are clipped by the
same denominator.  A private residual then makes the edge distribution
sum exactly to one.  Clipping preserves positive option support and never
increases slot or reservoir load.
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

def selectedMixedAllOptionMass
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) : ℝ :=
  ∑ c : Color,
    ((∑ i, ∑ j, G.selectedMixedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j) +
      G.selectedMixedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e c)

def selectedMixedNormalizationDenominator
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) : ℝ :=
  max 1 (G.selectedMixedAllOptionMass
    proposal edgeLabel qLaw R rho omega choice e)

def selectedMixedNormalizedLargeOptionMass
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  G.selectedMixedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice e c i j /
    G.selectedMixedNormalizationDenominator
      proposal edgeLabel qLaw R rho omega choice e

def selectedMixedNormalizedTinyOptionMass
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) : ℝ :=
  G.selectedMixedTinyOptionMass
    proposal edgeLabel qLaw R rho omega choice e c /
    G.selectedMixedNormalizationDenominator
      proposal edgeLabel qLaw R rho omega choice e

def selectedMixedResidualOptionMass
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) : ℝ :=
  1 - min 1 (G.selectedMixedAllOptionMass
    proposal edgeLabel qLaw R rho omega choice e)

theorem selectedMixedLargeOptionMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r)) :
    0 ≤ G.selectedMixedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j := by
  exact G.mixedGraphLargeProductMass_nonneg
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 e c _ _ i j

theorem selectedMixedTinyOptionMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) :
    0 ≤ G.selectedMixedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c := by
  exact G.mixedGraphTinyProductMass_nonneg
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 e c _ _

theorem selectedMixedAllOptionMass_nonneg
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) :
    0 ≤ G.selectedMixedAllOptionMass
      proposal edgeLabel qLaw R rho omega choice e := by
  unfold selectedMixedAllOptionMass
  exact Finset.sum_nonneg fun c _ ↦ add_nonneg
    (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      G.selectedMixedLargeOptionMass_nonneg
        proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
        homega0 homega1 hrho hproposal0 choice e c i j)
    (G.selectedMixedTinyOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
      homega0 homega1 hrho hproposal0 choice e c)

theorem selectedMixedNormalizationDenominator_pos
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) :
    0 < G.selectedMixedNormalizationDenominator
      proposal edgeLabel qLaw R rho omega choice e :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem selectedMixedNormalizedLargeOptionMass_pos_iff
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r)) :
    0 < G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j ↔
      0 < G.selectedMixedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j := by
  unfold selectedMixedNormalizedLargeOptionMass
  have hd := G.selectedMixedNormalizationDenominator_pos
    proposal edgeLabel qLaw R rho omega choice e
  exact div_pos_iff_of_pos_right hd

theorem selectedMixedNormalizedTinyOptionMass_pos_iff
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) :
    0 < G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e c ↔
      0 < G.selectedMixedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e c := by
  unfold selectedMixedNormalizedTinyOptionMass
  have hd := G.selectedMixedNormalizationDenominator_pos
    proposal edgeLabel qLaw R rho omega choice e
  exact div_pos_iff_of_pos_right hd

theorem positive_selectedMixedNormalizedLargeOptionMass_endpointLabels
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r))
    (hpos : 0 < G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.fst e) (choice (G.fst e)) c =
        some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.snd e) (choice (G.snd e)) c =
        some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  exact G.positive_selectedMixedLargeOptionMass_endpointLabels
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 choice e c i j
    ((G.selectedMixedNormalizedLargeOptionMass_pos_iff
      proposal edgeLabel qLaw R rho omega choice e c i j).mp hpos)

theorem positive_selectedMixedNormalizedTinyOptionMass_endpointLabels
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (hpos : 0 < G.selectedMixedNormalizedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c) :
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.fst e) (choice (G.fst e)) c =
        some (edgeLabel (G.fst e) (G.fstStarEdge e)) ∧
    G.decodeMixedGraphLabel proposal edgeLabel qLaw R
      (G.snd e) (choice (G.snd e)) c =
        some (edgeLabel (G.snd e) (G.sndStarEdge e)) := by
  exact G.positive_selectedMixedTinyOptionMass_endpointLabels
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 choice e c
    ((G.selectedMixedNormalizedTinyOptionMass_pos_iff
      proposal edgeLabel qLaw R rho omega choice e c).mp hpos)

theorem selectedMixedNormalizedLargeOptionMass_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r)) :
    G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j ≤
      G.selectedMixedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j := by
  let x := G.selectedMixedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice e c i j
  let d := G.selectedMixedNormalizationDenominator
    proposal edgeLabel qLaw R rho omega choice e
  have hx : 0 ≤ x := G.selectedMixedLargeOptionMass_nonneg
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 choice e c i j
  have hd : 0 < d := G.selectedMixedNormalizationDenominator_pos
    proposal edgeLabel qLaw R rho omega choice e
  have hd1 : 1 ≤ d := le_max_left _ _
  change x / d ≤ x
  apply (div_le_iff₀ hd).2
  simpa using mul_le_mul_of_nonneg_left hd1 hx

theorem selectedMixedNormalizedTinyOptionMass_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) :
    G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e c ≤
      G.selectedMixedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e c := by
  let x := G.selectedMixedTinyOptionMass
    proposal edgeLabel qLaw R rho omega choice e c
  let d := G.selectedMixedNormalizationDenominator
    proposal edgeLabel qLaw R rho omega choice e
  have hx : 0 ≤ x := G.selectedMixedTinyOptionMass_nonneg
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
    homega0 homega1 hrho hproposal0 choice e c
  have hd : 0 < d := G.selectedMixedNormalizationDenominator_pos
    proposal edgeLabel qLaw R rho omega choice e
  have hd1 : 1 ≤ d := le_max_left _ _
  change x / d ≤ x
  apply (div_le_iff₀ hd).2
  simpa using mul_le_mul_of_nonneg_left hd1 hx

theorem selectedMixedResidualOptionMass_nonneg
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) :
    0 ≤ G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice e :=
  sub_nonneg.mpr (min_le_left _ _)

theorem selectedMixedTinyOptionMass_eq_zero_of_large
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) (hlarge : β ≤ G.weight e) :
    G.selectedMixedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c = 0 := by
  unfold selectedMixedTinyOptionMass mixedGraphTinyProductMass pairedOption
    mixedGraphTinyEdgeMass
  simp [not_lt_of_ge hlarge]

theorem selectedMixedNormalizedTinyOptionMass_eq_zero_of_large
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (c : Color) (hlarge : β ≤ G.weight e) :
    G.selectedMixedNormalizedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c = 0 := by
  unfold selectedMixedNormalizedTinyOptionMass
  rw [G.selectedMixedTinyOptionMass_eq_zero_of_large
    proposal edgeLabel qLaw R rho omega choice e c hlarge]
  exact zero_div _

theorem sum_selectedMixedNormalizedOptionMass_add_residual
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) :
    (∑ c : Color,
      ((∑ i, ∑ j,
        G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c i j) +
        G.selectedMixedNormalizedTinyOptionMass
          proposal edgeLabel qLaw R rho omega choice e c)) +
      G.selectedMixedResidualOptionMass
        proposal edgeLabel qLaw R rho omega choice e = 1 := by
  let S := G.selectedMixedAllOptionMass
    proposal edgeLabel qLaw R rho omega choice e
  let d := G.selectedMixedNormalizationDenominator
    proposal edgeLabel qLaw R rho omega choice e
  have hS0 : 0 ≤ S := G.selectedMixedAllOptionMass_nonneg
    proposal edgeLabel qLaw R hq0 hqsum hqsingle
    hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 choice e
  have hfactor :
      (∑ c : Color,
        ((∑ i, ∑ j,
          G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice e c i j) +
          G.selectedMixedNormalizedTinyOptionMass
            proposal edgeLabel qLaw R rho omega choice e c)) = S / d := by
    unfold selectedMixedNormalizedLargeOptionMass
      selectedMixedNormalizedTinyOptionMass
    unfold S selectedMixedAllOptionMass
    change
      (∑ c : Color,
        ((∑ i, ∑ j,
          G.selectedMixedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice e c i j / d) +
          G.selectedMixedTinyOptionMass
            proposal edgeLabel qLaw R rho omega choice e c / d)) =
        (∑ c : Color,
          ((∑ i, ∑ j,
            G.selectedMixedLargeOptionMass
              proposal edgeLabel qLaw R rho omega choice e c i j) +
            G.selectedMixedTinyOptionMass
              proposal edgeLabel qLaw R rho omega choice e c)) / d
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    have hj (i : Fin (explicitLargeSlotBound β qstep r)) :
        (∑ j, G.selectedMixedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c i j / d) =
          (∑ j, G.selectedMixedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice e c i j) / d := by
      exact (Finset.sum_div Finset.univ
        (fun j ↦ G.selectedMixedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c i j) d).symm
    calc
      (∑ i, ∑ j, G.selectedMixedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c i j / d) +
        G.selectedMixedTinyOptionMass
          proposal edgeLabel qLaw R rho omega choice e c / d =
          (∑ i, (∑ j, G.selectedMixedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice e c i j) / d) +
            G.selectedMixedTinyOptionMass
              proposal edgeLabel qLaw R rho omega choice e c / d := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact hj i
      _ = ((∑ i, ∑ j, G.selectedMixedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice e c i j) / d) +
            G.selectedMixedTinyOptionMass
              proposal edgeLabel qLaw R rho omega choice e c / d := by
        congr 1
        exact (Finset.sum_div Finset.univ
          (fun i ↦ ∑ j, G.selectedMixedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice e c i j) d).symm
      _ = _ := (add_div _ _ _).symm
  rw [hfactor]
  change S / max 1 S + (1 - min 1 S) = 1
  rw [OptionNormalization.div_max_one_eq_min_one S hS0]
  ring

def selectedMixedNormalizedLargeSlotLoad
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (slot : Fin (explicitLargeSlotBound β qstep r)) : ℝ :=
  ∑ e : G.E,
    ((if v = G.fst e then
        ∑ j, G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c slot j else 0) +
      (if v = G.snd e then
        ∑ i, G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice e c i slot else 0))

def selectedMixedNormalizedTinyReservoirLoad
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) : ℝ :=
  ∑ e : G.E, if G.Inc v e then
    G.weight e * G.selectedMixedNormalizedTinyOptionMass
      proposal edgeLabel qLaw R rho omega choice e c else 0

theorem selectedMixedNormalizedLargeSlotLoad_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color)
    (slot : Fin (explicitLargeSlotBound β qstep r)) :
    G.selectedMixedNormalizedLargeSlotLoad
        proposal edgeLabel qLaw R rho omega choice v c slot ≤
      G.selectedMixedLargeSlotLoad
        proposal edgeLabel qLaw R rho omega choice v c slot := by
  unfold selectedMixedNormalizedLargeSlotLoad selectedMixedLargeSlotLoad
  apply Finset.sum_le_sum
  intro e _
  apply add_le_add
  · by_cases hv : v = G.fst e
    · simp only [hv, if_true]
      exact Finset.sum_le_sum fun j _ ↦
        G.selectedMixedNormalizedLargeOptionMass_le
          proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
          homega0 homega1 hrho hproposal0 choice e c slot j
    · simp [hv]
  · by_cases hv : v = G.snd e
    · simp only [hv, if_true]
      exact Finset.sum_le_sum fun i _ ↦
        G.selectedMixedNormalizedLargeOptionMass_le
          proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
          homega0 homega1 hrho hproposal0 choice e c i slot
    · simp [hv]

theorem selectedMixedNormalizedTinyReservoirLoad_le
    (hq0 : ∀ v c S, 0 ≤ qLaw v c S)
    (hqsum : ∀ v c, ∑ S, qLaw v c S = 1)
    (hqsingle : ∀ v c S, qLaw v c S ≠ 0 → S ≠ ∅ →
      ∃ label : Label, ∀ f ∈ S, edgeLabel v f = label)
    (hs : 0 ≤ s) (hqstep : 0 ≤ qstep) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + qstep + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (v : G.V) (c : Color) :
    G.selectedMixedNormalizedTinyReservoirLoad
        proposal edgeLabel qLaw R rho omega choice v c ≤
      G.selectedMixedTinyReservoirLoad
        proposal edgeLabel qLaw R rho omega choice v c := by
  unfold selectedMixedNormalizedTinyReservoirLoad
    selectedMixedTinyReservoirLoad
  apply Finset.sum_le_sum
  intro e _
  by_cases hv : G.Inc v e
  · simp only [hv, if_true]
    exact mul_le_mul_of_nonneg_left
      (G.selectedMixedNormalizedTinyOptionMass_le
        proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0 hleft
        homega0 homega1 hrho hproposal0 choice e c)
      (G.weight_nonneg e)
  · simp [hv]

end WeightedMultigraph

end

end WeightedEdgeColoring
