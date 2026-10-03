import WeightedEdgeColoring.SubtwoMixedGraphQuantizedBridge
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeRestriction
import WeightedEdgeColoring.BoundedMultiplicityOriginalTypeIsolatedClosedIteration

/-!
# Initial copied-job degree for the selected mixed graph

The edgewise normalization makes the ordinary selected mass and its private
residual add to one on every large edge. This is the full-degree input for the
retained matching iteration, without a loss depending on the number of jobs.
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

theorem selectedMixedNormalizedLarge_fiber_add_residual_eq_one
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
    (e : G.E) (hlarge : β ≤ G.weight e) :
    (∑ c : Color, ∑ i, ∑ j,
      G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j) +
      G.selectedMixedResidualOptionMass
        proposal edgeLabel qLaw R rho omega choice e = 1 := by
  have htotal := G.sum_selectedMixedNormalizedOptionMass_add_residual
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice e
  have htiny : ∀ c : Color,
      G.selectedMixedNormalizedTinyOptionMass
        proposal edgeLabel qLaw R rho omega choice e c = 0 := by
    intro c
    exact G.selectedMixedNormalizedTinyOptionMass_eq_zero_of_large
      proposal edgeLabel qLaw R rho omega choice e c hlarge
  simpa [htiny] using htotal

theorem selectedMixed_quantizedLargeJobDegree_lower
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
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (e : G.E) (hlarge : β ≤ G.weight e) :
    (N : ℝ) -
        ((Fintype.card Color * explicitLargeSlotBound β qstep r *
          explicitLargeSlotBound β qstep r : ℕ) +
          DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket
              (G.selectedMixedResidualOptionMass
                proposal edgeLabel qLaw R rho omega choice) gamma reserve) e) ≤
      ((G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)).quantizedJobDegree N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice)) e : ℝ) := by
  have hbase := G.dyadicLargeEdge_quantizedJobDegree_lower
    (Color := Color) (explicitLargeSlotBound β qstep r) bucket gamma reserve
    (G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice)
    (G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice) N e
  have htotal := G.selectedMixedNormalizedLarge_fiber_add_residual_eq_one
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice e hlarge
  rw [htotal, mul_one] at hbase
  exact hbase

theorem selectedMixed_quantizedLargeJobDegree_ge
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
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N C : ℕ)
    (hCN : C ≤ N)
    (hchoices : ∀ e,
      Fintype.card Color * explicitLargeSlotBound β qstep r *
          explicitLargeSlotBound β qstep r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket
            (G.selectedMixedResidualOptionMass
              proposal edgeLabel qLaw R rho omega choice) gamma reserve) e ≤ C)
    (e : G.E) (hlarge : β ≤ G.weight e) :
    N - C ≤
      (G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)).quantizedJobDegree N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice)) e := by
  have hbase := G.selectedMixed_quantizedLargeJobDegree_lower
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice bucket gamma reserve N
    e hlarge
  have hchoice := hchoices e
  have hnat : (N - C : ℝ) ≤
      (G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)).quantizedJobDegree N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice)) e := by
    have hchoiceR :
        ((Fintype.card Color * explicitLargeSlotBound β qstep r *
          explicitLargeSlotBound β qstep r : ℕ) +
          DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket
              (G.selectedMixedResidualOptionMass
                proposal edgeLabel qLaw R rho omega choice) gamma reserve) e : ℝ) ≤ C := by
      exact_mod_cast hchoice
    push_cast at hchoiceR
    push_cast at hbase
    linarith
  exact_mod_cast hnat

theorem selectedMixedLarge_activeJobs_all
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
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N C : ℕ)
    (hCN : C ≤ N) (hNC : 0 < N - C)
    (hchoices : ∀ e,
      Fintype.card Color * explicitLargeSlotBound β qstep r *
          explicitLargeSlotBound β qstep r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket
            (G.selectedMixedResidualOptionMass
              proposal edgeLabel qLaw R rho omega choice) gamma reserve) e ≤ C) :
    let Hbase :=
      (G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedResidualOptionMass
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice))
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∀ j, j ∈ Hlarge.activeJobs := by
  dsimp only
  intro j
  rw [RankThreeOptionSystem.mem_activeJobs]
  apply Finset.card_pos.mp
  have hdeg := G.selectedMixed_quantizedLargeJobDegree_ge
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice bucket gamma reserve N C
    hCN hchoices j.1 (G.mem_largeEdgeJobs.mp j.2)
  rw [G.largeEdgeJobSystem_fiber_card]
  have hfiber := hNC.trans_le hdeg
  simpa only [← RankThreeOptionSystem.quantized_fiber_card] using hfiber

theorem selectedMixedResidualOptionMass_le_one
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
    G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice e ≤ 1 := by
  have hmass := G.selectedMixedAllOptionMass_nonneg
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice e
  unfold selectedMixedResidualOptionMass
  exact sub_le_self _ (le_min (by norm_num) hmass)

theorem selectedMixedNormalizedLargeOptionMass_le_inv_reserve
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
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (reserve : ℕ)
    (hpair : mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 / n ≤
        1 / (reserve : ℝ))
    (e : G.E) (c : Color)
    (i j : Fin (explicitLargeSlotBound β qstep r)) :
    G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j ≤
        1 / (reserve : ℝ) := by
  have hx0 : ∀ j', 0 ≤ G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j' := by
    intro j'
    exact G.selectedMixedNormalizedLargeOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e c i j'
  have hsingle : G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j ≤
      ∑ j', G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j' := by
    exact Finset.single_le_sum (fun b _hb ↦ hx0 b) (Finset.mem_univ j)
  have hbound := G.n_mul_sum_selectedMixedNormalizedLarge_le_scale
    proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
    hs hqstep hr0 hleft homega0 homega1 hrho hC0
    hproposal0 hproposal choice e c i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ j', G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j') ≤
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 / n := by
    exact (le_div_iff₀ hnR).2 (by simpa [mul_comm] using hbound)
  exact (hsingle.trans hsum).trans hpair

theorem selectedMixed_quantizedSlotPairCodegree_le
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
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve N mult : ℕ)
    (hmult : G.PairMultiplicityAtMost mult)
    (hreserve : 0 < reserve)
    (hpair : mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 / n ≤
        1 / (reserve : ℝ))
    {left right : G.DyadicLargeEdgeSlot
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket gamma reserve
      (G.selectedMixedResidualOptionMass
        proposal edgeLabel qLaw R rho omega choice)}
    (hne : left ≠ right) :
    ((((G.dyadicLargeEdgeOptionSystem
        (Color := Color) (explicitLargeSlotBound β qstep r)
        bucket gamma reserve
        (G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega choice)).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve
        (G.selectedMixedResidualOptionMass
          proposal edgeLabel qLaw R rho omega choice)
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice))).slotPairCodegree
        left right : ℕ) : ℝ) ≤ (mult : ℝ) * N / reserve := by
  have hx0 : ∀ e c i j, 0 ≤ G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice e c i j := by
    intro e c i j
    exact G.selectedMixedNormalizedLargeOptionMass_nonneg
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e c i j
  have hx : ∀ e c i j,
      G.selectedMixedNormalizedLargeOptionMass
        proposal edgeLabel qLaw R rho omega choice e c i j ≤
          1 / (reserve : ℝ) := by
    intro e c i j
    exact G.selectedMixedNormalizedLargeOptionMass_le_inv_reserve
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal choice reserve hpair e c i j
  have hres0 : ∀ e, 0 ≤ G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice e := by
    intro e
    exact G.selectedMixedResidualOptionMass_nonneg
      proposal edgeLabel qLaw R rho omega choice e
  have hres1 : ∀ e, G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice e ≤ 1 := by
    intro e
    exact G.selectedMixedResidualOptionMass_le_one
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e
  exact G.dyadicLargeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β qstep r) bucket gamma reserve
    (G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice) hmult
    (G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice)
    hx0 hx hres0 hres1 hreserve N hne

end WeightedMultigraph

end

end WeightedEdgeColoring
