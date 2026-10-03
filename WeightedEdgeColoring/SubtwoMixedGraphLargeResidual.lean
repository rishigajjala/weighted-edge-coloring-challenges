import WeightedEdgeColoring.SubtwoMixedGraphMatchingInitialBounds

/-!
# Large-edge private residual for selected mixed matching

Tiny edges must not contribute to the dyadic extra-slot support. This mask
agrees with the selected normalized residual on every large job.
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

def selectedMixedLargeResidual (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) : ℝ :=
  if β ≤ G.weight e then
    G.selectedMixedResidualOptionMass
      proposal edgeLabel qLaw R rho omega choice e else 0

theorem selectedMixedLargeResidual_eq_of_large
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) (hlarge : β ≤ G.weight e) :
    G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice e =
      G.selectedMixedResidualOptionMass
        proposal edgeLabel qLaw R rho omega choice e := by
  simp [selectedMixedLargeResidual, hlarge]

theorem selectedMixedLargeResidual_nonneg
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (e : G.E) :
    0 ≤ G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice e := by
  by_cases hlarge : β ≤ G.weight e
  · rw [G.selectedMixedLargeResidual_eq_of_large
      proposal edgeLabel qLaw R rho omega choice e hlarge]
    exact G.selectedMixedResidualOptionMass_nonneg
      proposal edgeLabel qLaw R rho omega choice e
  · simp [selectedMixedLargeResidual, hlarge]

theorem selectedMixedLargeResidual_le_one
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
    G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice e ≤ 1 := by
  by_cases hlarge : β ≤ G.weight e
  · rw [G.selectedMixedLargeResidual_eq_of_large
      proposal edgeLabel qLaw R rho omega choice e hlarge]
    exact G.selectedMixedResidualOptionMass_le_one
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e
  · simp [selectedMixedLargeResidual, hlarge]

theorem selectedMixedLargeResidual_mul_beta_le_weight
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
    G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice e * β ≤ G.weight e := by
  by_cases hlarge : β ≤ G.weight e
  · have hres := G.selectedMixedLargeResidual_le_one
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e
    have hβbound : G.selectedMixedLargeResidual
        proposal edgeLabel qLaw R rho omega choice e * β ≤ β := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hres hβ.le
    exact hβbound.trans hlarge
  · simp [selectedMixedLargeResidual, hlarge, G.weight_nonneg]

theorem boundedClassResidual_selectedMixedLargeResidual_mul_beta_le_starWeight
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
    (bucket : G.E → Class) (v : G.V) (h : Class) :
    G.boundedClassResidual bucket
      (G.selectedMixedLargeResidual
        proposal edgeLabel qLaw R rho omega choice) v h * β ≤
      G.starWeight v := by
  unfold boundedClassResidual
  rw [Finset.sum_mul]
  calc
    (∑ e,
      ((if (G.fst e, bucket e) = (v, h) then
          G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice e else 0) +
       (if (G.snd e, bucket e) = (v, h) then
          G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice e else 0)) * β) ≤
      ∑ e, if G.Inc v e then G.weight e else 0 := by
        apply Finset.sum_le_sum
        intro e _
        have hedge := G.selectedMixedLargeResidual_mul_beta_le_weight
          proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
          hleft homega0 homega1 hrho hproposal0 choice e
        by_cases hf : (G.fst e, bucket e) = (v, h)
        · have hfv : G.fst e = v := congrArg Prod.fst hf
          have hinc : G.Inc v e := Or.inl hfv
          have hsnd : (G.snd e, bucket e) ≠ (v, h) := by
            intro heq
            exact G.noLoop e (hfv.trans (congrArg Prod.fst heq).symm)
          rw [if_pos hf, if_neg hsnd, add_zero, if_pos hinc]
          exact hedge
        · by_cases hsnd : (G.snd e, bucket e) = (v, h)
          · have hsv : G.snd e = v := congrArg Prod.fst hsnd
            have hinc : G.Inc v e := Or.inr hsv
            rw [if_neg hf, if_pos hsnd, zero_add, if_pos hinc]
            exact hedge
          · by_cases hinc : G.Inc v e
            · simp [hf, hsnd, hinc, G.weight_nonneg]
            · simp [hf, hsnd, hinc]
    _ = G.starWeight v := by
      unfold starWeight
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter (G.Inc v))
        (by intro e; simp) G.weight

theorem selectedMixedLargeResidual_supportCount_le
    {n : ℕ}
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
    (hstar : ∀ v, G.starWeight v ≤ n)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (gamma : ℝ) (reserve E : ℕ)
    (hreserve : 0 < reserve) (hgamma1 : gamma < 1)
    (hE : 2 * ((n : ℝ) / β / (1 - gamma) +
      1 + reserve) ≤ E) (e : G.E) :
    DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
      (G.boundedDyadicExtraSlotCount bucket
        (G.selectedMixedLargeResidual
          proposal edgeLabel qLaw R rho omega choice)
        gamma reserve) e ≤ E := by
  let residual := G.selectedMixedLargeResidual
    proposal edgeLabel qLaw R rho omega choice
  have count_le (v : G.V) (h : Class) :
      G.boundedDyadicExtraSlotCount bucket residual
        gamma reserve v h ≤ E := by
    have hc := G.boundedDyadicExtraSlotCount_cast_le bucket
      residual (G.selectedMixedLargeResidual_nonneg
        proposal edgeLabel qLaw R rho omega choice)
      gamma hreserve hgamma1 v h
    have hmul :=
      G.boundedClassResidual_selectedMixedLargeResidual_mul_beta_le_starWeight
        proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
        hleft homega0 homega1 hrho hproposal0 choice bucket v h
    have hclass : G.boundedClassResidual bucket residual v h ≤
        (n : ℝ) / β := by
      apply (le_div_iff₀ hβ).2
      exact hmul.trans (hstar v)
    have hgap : 0 < 1 - gamma := sub_pos.mpr hgamma1
    have hdiv := div_le_div_of_nonneg_right hclass hgap.le
    have hinside :
        G.boundedClassResidual bucket residual v h / (1 - gamma) +
          1 + reserve ≤ (n : ℝ) / β / (1 - gamma) +
            1 + reserve := by
      nlinarith [hdiv]
    have hscaled :
        2 * (G.boundedClassResidual bucket residual v h / (1 - gamma) +
          1 + reserve) ≤
        2 * ((n : ℝ) / β / (1 - gamma) +
          1 + reserve) :=
      mul_le_mul_of_nonneg_left hinside (by norm_num)
    have hreal :
        (G.boundedDyadicExtraSlotCount bucket residual
          gamma reserve v h : ℝ) ≤ E :=
      hc.trans (hscaled.trans hE)
    exact_mod_cast hreal
  unfold DivisibleLocalExtraChoice.supportCount
  exact max_le (count_le _ _) (count_le _ _)

theorem selectedMixed_quantizedLargeMaskedJobDegree_lower
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
              (G.selectedMixedLargeResidual
                proposal edgeLabel qLaw R rho omega choice) gamma reserve) e) ≤
      ((G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)).quantizedJobDegree N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice)) e : ℝ) := by
  have hbase := G.dyadicLargeEdge_quantizedJobDegree_lower
    (Color := Color) (explicitLargeSlotBound β qstep r) bucket gamma reserve
    (G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice)
    (G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice) N e
  have htotal := G.selectedMixedNormalizedLarge_fiber_add_residual_eq_one
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice e hlarge
  rw [G.selectedMixedLargeResidual_eq_of_large
    proposal edgeLabel qLaw R rho omega choice e hlarge,
    htotal, mul_one] at hbase
  exact hbase

theorem selectedMixed_quantizedLargeMaskedJobDegree_ge
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
            (G.selectedMixedLargeResidual
              proposal edgeLabel qLaw R rho omega choice) gamma reserve) e ≤ C)
    (e : G.E) (hlarge : β ≤ G.weight e) :
    N - C ≤
      (G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)).quantizedJobDegree N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice)) e := by
  have hbase := G.selectedMixed_quantizedLargeMaskedJobDegree_lower
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice bucket gamma reserve N
    e hlarge
  have hchoice := hchoices e
  have hnat : (N - C : ℝ) ≤
      (G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)).quantizedJobDegree N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice)) e := by
    have hchoiceR :
        ((Fintype.card Color * explicitLargeSlotBound β qstep r *
          explicitLargeSlotBound β qstep r : ℕ) +
          DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
            (G.boundedDyadicExtraSlotCount bucket
              (G.selectedMixedLargeResidual
                proposal edgeLabel qLaw R rho omega choice) gamma reserve) e : ℝ) ≤ C := by
      exact_mod_cast hchoice
    push_cast at hchoiceR hbase
    linarith
  exact_mod_cast hnat

theorem selectedMixedLargeMasked_activeJobs_all
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
            (G.selectedMixedLargeResidual
              proposal edgeLabel qLaw R rho omega choice) gamma reserve) e ≤ C) :
    let Hbase :=
      (G.dyadicLargeEdgeOptionSystem
          (Color := Color) (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket gamma reserve
          (G.selectedMixedLargeResidual
            proposal edgeLabel qLaw R rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice))
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∀ j, j ∈ Hlarge.activeJobs := by
  dsimp only
  intro j
  rw [RankThreeOptionSystem.mem_activeJobs]
  apply Finset.card_pos.mp
  have hdeg := G.selectedMixed_quantizedLargeMaskedJobDegree_ge
    proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
    hleft homega0 homega1 hrho hproposal0 choice bucket gamma reserve N C
    hCN hchoices j.1 (G.mem_largeEdgeJobs.mp j.2)
  rw [G.largeEdgeJobSystem_fiber_card]
  have hfiber := hNC.trans_le hdeg
  simpa only [← RankThreeOptionSystem.quantized_fiber_card] using hfiber

theorem selectedMixedMasked_quantizedSlotPairCodegree_le
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
      (G.selectedMixedLargeResidual
        proposal edgeLabel qLaw R rho omega choice)}
    (hne : left ≠ right) :
    ((((G.dyadicLargeEdgeOptionSystem
        (Color := Color) (explicitLargeSlotBound β qstep r)
        bucket gamma reserve
        (G.selectedMixedLargeResidual
          proposal edgeLabel qLaw R rho omega choice)).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve
        (G.selectedMixedLargeResidual
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
  have hres0 : ∀ e, 0 ≤ G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice e := by
    intro e
    exact G.selectedMixedLargeResidual_nonneg
      proposal edgeLabel qLaw R rho omega choice e
  have hres1 : ∀ e, G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice e ≤ 1 := by
    intro e
    exact G.selectedMixedLargeResidual_le_one
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice e
  exact G.dyadicLargeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β qstep r) bucket gamma reserve
    (G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice) hmult
    (G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice)
    hx0 hx hres0 hres1 hreserve N hne

end WeightedMultigraph

end

end WeightedEdgeColoring
