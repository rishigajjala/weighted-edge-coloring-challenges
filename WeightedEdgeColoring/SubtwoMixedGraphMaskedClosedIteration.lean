import WeightedEdgeColoring.SubtwoMixedGraphMaskedInitialBounds
import WeightedEdgeColoring.BoundedMultiplicityLargeEdgeTraceLiftBridge

/-!
# Closed endpoint iteration for the actual selected mixed copied jobs
-/

namespace WeightedEdgeColoring

open scoped BigOperators
open RankThreeOptionSystem.OriginalIterationState
open RankThreeOptionSystem.OriginalIterationState.Multigraph

noncomputable section

structure MixedMaskedClosedScalars
    (β alpha gamma delta : ℝ)
    (N C S0 lambda L K steps : ℕ) : Prop where
  dyadicCover : 1 ≤ dyadicScale β L
  alphaPos : 0 < alpha
  alphaSmall : alpha ≤ 1 / 100000
  gammaPos : 0 < gamma
  gammaHalf : gamma ≤ 1 / 2
  deltaPos : 0 < delta
  deltaOne : delta ≤ 1
  KPos : 0 < K
  lambdaPos : 0 < lambda
  thetaOne : (1 - delta) * variableSlackA alpha gamma lambda / 8 ≤ 1
  jobRate : 0 ≤ fixedSlackJobRetention
    (variableSlackA alpha gamma lambda) gamma -
      variableSlackEta alpha gamma lambda
  slotRate : 0 ≤ fixedSlackSlotRetention
    (variableSlackA alpha gamma lambda) gamma * (1 - gamma) +
      3 * variableSlackEta alpha gamma lambda
  gap : (S0 : ℝ) ≤ (1 - gamma) * (N - C)
  margin : ∀ t < steps, 1 - gamma ≤
    (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
      ((1 - gamma) * variableSlackEta alpha gamma lambda +
        3 * variableSlackEta alpha gamma lambda)) *
      naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) t
  positive : ∀ t < steps, 5 ≤
    naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
  nextPositive : ∀ t < steps,
    0 < (fixedSlackJobRetention
        (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda) *
      naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) t
  Kdegree : ∀ t < steps, K ≤
    naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
  scale : ∀ t < steps,
    let d := naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
    1000 * ((lambda : ℝ) + 1) ≤ gamma * d
  groupScale : ∀ t < steps,
    let d := naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
    isolatedVariableZ d + 1 ≤
      delta ^ 2 * variableSlackA alpha gamma lambda * K / 64
  slotScale : ∀ t < steps,
    let d := naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
    isolatedVariableZ d + 1 ≤
      variableSlackEta alpha gamma lambda ^ 2 * d /
        (96 * variableSlackA alpha gamma lambda * lambda)
  jobScale : ∀ t < steps,
    let d := naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
    isolatedVariableZ d + Real.log 2 ≤
      variableSlackEta alpha gamma lambda ^ 2 * d /
        (16 * variableSlackA alpha gamma lambda * lambda)
  block : ∀ t < steps,
    let d := naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
    128 * lambda * (isolatedVariableMoment d : ℝ) ^ 2 ≤
      delta * alpha * gamma * K
  aSmall : variableSlackA alpha gamma lambda ≤ delta / 96
  square : ∀ t < steps,
    let d := naturalSharpJobScale (N - C)
      (variableSlackA alpha gamma lambda) gamma
      (variableSlackEta alpha gamma lambda) t
    lambda ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
      variableSlackBeta0 alpha gamma * d

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

theorem exists_selectedMixedMaskedClosedEndpointIteration
    {n N reserve C E S0 steps L K lambda mult : ℕ}
    {rho omega C0 extraGamma bound alpha gamma delta : ℝ}
    (hmult : G.PairMultiplicityAtMost mult)
    (hn : 0 < n) (hN : 0 < N)
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
    (bucket : G.E → Class)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcapacity : ∀ v c place,
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R rho omega choice c
          (Sum.inl (G.selectedMixedLargeCandidateRow
            proposal edgeLabel qLaw R choice v c place)) < bound)
    (hordinaryCap : (N : ℝ) * bound ≤ S0)
    (hreserve : 0 < reserve)
    (hextraGamma0 : 0 ≤ extraGamma)
    (hextraGamma1 : extraGamma < 1)
    (hextraCap : (1 - extraGamma) * N ≤ S0)
    (hordinaryCodegree : (N : ℝ) *
      ((explicitLargeSlotBound β qstep r : ℝ) *
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
          (n : ℝ)) ≤ lambda)
    (hordinaryPair : mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 / n ≤
        1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hpairCodegree : (mult : ℝ) * N / reserve ≤ lambda)
    (hCN : C ≤ N)
    (hE : 2 * ((n : ℝ) / β / (1 - extraGamma) +
      1 + reserve) ≤ E)
    (hchoiceCap : Fintype.card Color * explicitLargeSlotBound β qstep r *
      explicitLargeSlotBound β qstep r + E ≤ C)
    (numeric : MixedMaskedClosedScalars β alpha gamma delta
      N C S0 lambda L K steps) :
    let residual := G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let Hbase := (G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket extraGamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket extraGamma reserve residual x)
    letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
      inferInstance
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∃ final : RankThreeOptionSystem.OriginalIterationState Hlarge,
      EndpointSharpTrace (G.largeEdgeRestriction β) β
        (variableSlackA alpha gamma lambda) delta L K steps
        (RankThreeOptionSystem.OriginalIterationState.full Hlarge) final ∧
      (∀ j, (final.system.fiber j).Nonempty →
        naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) steps ≤
          (final.system.fiber j).card) ∧
      (∀ slot, final.system.slotDegree slot ≤
        naturalSharpSlotCap S0 (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda)
          (2 * variableSlackEta alpha gamma lambda)
          (variableSlackEta alpha gamma lambda) steps) ∧
      ∀ v, stateActiveStarWeight (G.largeEdgeRestriction β) final v ≤
        (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps *
          stateActiveStarWeight (G.largeEdgeRestriction β)
            (RankThreeOptionSystem.OriginalIterationState.full Hlarge) v +
          (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  dsimp only
  let residual := G.selectedMixedLargeResidual
    proposal edgeLabel qLaw R rho omega choice
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let Hbase := (G.dyadicLargeEdgeOptionSystem
    (Color := Color) (explicitLargeSlotBound β qstep r)
    bucket extraGamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket extraGamma reserve residual x)
  letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem Hbase β
  have hchoices : ∀ e,
      Fintype.card Color * explicitLargeSlotBound β qstep r *
          explicitLargeSlotBound β qstep r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket residual
            extraGamma reserve) e ≤ C := by
    intro e
    exact (Nat.add_le_add_left
      (G.selectedMixedLargeResidual_supportCount_le
        proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
        hleft homega0 homega1 hrho hproposal0 choice hstar
        bucket extraGamma reserve E hreserve hextraGamma1 hE e) _).trans
        hchoiceCap
  apply RankThreeOptionSystem.OriginalIterationState.Multigraph.exists_endpointVariableSlackClosedIteration
    (G.largeEdgeRestriction β)
    (RankThreeOptionSystem.OriginalIterationState.full Hlarge)
    steps (N - C) S0 lambda L K
  · exact hβ
  · exact numeric.dyadicCover
  · exact G.largeEdgeRestriction_weight_lower β
  · exact numeric.alphaPos
  · exact numeric.alphaSmall
  · exact numeric.gammaPos
  · exact numeric.gammaHalf
  · exact numeric.deltaPos
  · exact numeric.deltaOne
  · exact numeric.KPos
  · exact numeric.lambdaPos
  · exact numeric.thetaOne
  · exact numeric.jobRate
  · exact numeric.slotRate
  · simpa only [Nat.cast_sub hCN] using numeric.gap
  · exact numeric.margin
  · exact numeric.positive
  · exact numeric.nextPositive
  · intro o
    exact G.quantized_dyadicLargeEdgeOptionSystem_slots_card_eq_two
      (explicitLargeSlotBound β qstep r) bucket extraGamma reserve residual x
      N o.1
  · intro e slot
    have hdeg := G.selectedMixedMaskedLarge_jobSlotCodegree_le
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal choice bucket extraGamma reserve N hreserve
      lambda hordinaryCodegree hextraCodegree e slot
    exact_mod_cast hdeg
  · intro left right hne
    have hrestrict := G.largeEdgeJobSystem_slotPairCodegree_le
      Hbase β left right
    have hbase := G.selectedMixedMasked_quantizedSlotPairCodegree_le
      proposal edgeLabel qLaw R hn hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0
      hproposal0 hproposal choice bucket extraGamma reserve N mult
      hmult hreserve hordinaryPair hne
    have hrestrictR : (Hlarge.slotPairCodegree left right : ℝ) ≤
        (Hbase.slotPairCodegree left right : ℝ) := by
      exact_mod_cast hrestrict
    exact_mod_cast hrestrictR.trans (hbase.trans hpairCodegree)
  · intro j _hj
    change N - C ≤
      ((RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.fiber j).card
    have hfull :
        ((RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.fiber j).card =
          (Hlarge.fiber j).card :=
      RankThreeOptionSystem.OriginalIterationState.Multigraph.full_system_fiber_card
        (G := G.largeEdgeRestriction β) (H := Hlarge) j
    rw [hfull, G.largeEdgeJobSystem_fiber_card]
    have hdeg := G.selectedMixed_quantizedLargeMaskedJobDegree_ge
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice bucket extraGamma
      reserve N C hCN hchoices j.1 (G.mem_largeEdgeJobs.mp j.2)
    simpa only [← RankThreeOptionSystem.quantized_fiber_card] using hdeg
  · intro slot
    change (RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.slotDegree slot ≤ S0
    have hfull :
        (RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.slotDegree slot =
          Hlarge.slotDegree slot :=
      RankThreeOptionSystem.OriginalIterationState.Multigraph.full_system_slotDegree
        (G := G.largeEdgeRestriction β) (H := Hlarge) slot
    rw [hfull]
    exact G.selectedMixedMaskedLarge_slotDegree_le
      proposal edgeLabel qLaw R hq0 hqsum hqsingle
      hs hqstep hr0 hleft homega0 homega1 hrho hproposal0 choice
      bucket extraGamma reserve N S0 hN bound hcapacity hordinaryCap
      hreserve hextraGamma0 hextraGamma1 hextraCap slot
  · exact numeric.Kdegree
  · exact numeric.scale
  · exact numeric.groupScale
  · exact numeric.slotScale
  · exact numeric.jobScale
  · exact numeric.block
  · exact numeric.aSmall
  · exact numeric.square

/-- The copied-job matching in a closed trace is an actual partial matching
of the selected masked dyadic system, with the trace's uniform endpoint loss. -/
theorem selectedMixedMaskedTrace_to_matching
    (rho omega extraGamma : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    {Class : Type*} [Fintype Class] [DecidableEq Class]
    (bucket : G.E → Class) (reserve N L K steps : ℕ)
    (a delta traceLoss : ℝ) :
    let residual := G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let Hbase := (G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket extraGamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket extraGamma reserve residual x)
    letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
      inferInstance
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∀ (final : RankThreeOptionSystem.OriginalIterationState Hlarge)
      (T : EndpointSharpTrace (G.largeEdgeRestriction β) β a delta
        L K steps (RankThreeOptionSystem.OriginalIterationState.full Hlarge)
        final)
      (hactive : ∀ j, j ∈ Hlarge.activeJobs)
      (hstate : ∀ v,
        stateActiveStarWeight (G.largeEdgeRestriction β) final v ≤
          traceLoss),
    ∃ (M : Finset (QuantizedCopy N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket extraGamma reserve residual x))),
      Hbase.IsPartialMatching M ∧
      ∀ v, G.uncoveredLargeStarWeight Hbase β M v ≤ traceLoss := by
  dsimp only
  let residual := G.selectedMixedLargeResidual
    proposal edgeLabel qLaw R rho omega choice
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let Hbase := (G.dyadicLargeEdgeOptionSystem
    (Color := Color) (explicitLargeSlotBound β qstep r)
    bucket extraGamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket extraGamma reserve residual x)
  letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem Hbase β
  intro final T hactive hstate
  let M := G.liftLargeEdgeJobSet Hbase β final.matching
  refine ⟨M, G.liftLargeEdgeJobSet_isPartialMatching Hbase β
    final.matching_isPartial, ?_⟩
  intro v
  rw [G.endpointSharpTrace_uncoveredLargeStarWeight_lift_eq_state
    Hbase T hactive v]
  exact hstate v

/-- A closed large-job trace has a graph-independent uncovered-star bound.
The statement applies directly to the selected masked copied-job system. -/
theorem exists_largePartialMatching_of_closedTrace_uniform
    {Slot Option : Type*} [Fintype Slot] [DecidableEq Slot]
    [Fintype Option] [DecidableEq Option]
    (H : RankThreeOptionSystem G.E Slot Option)
    {L K steps : ℕ} {β a delta n : ℝ}
    (hstar : ∀ v, G.starWeight v ≤ n)
    (htheta0 : 0 ≤ 1 - (1 - delta) * a / 8) :
    letI : DecidableEq (H.ActiveJobOption (G.largeEdgeJobs β)) :=
      inferInstance
    let Hlarge := G.largeEdgeJobSystem H β
    ∀ (final : RankThreeOptionSystem.OriginalIterationState Hlarge)
      (T : EndpointSharpTrace (G.largeEdgeRestriction β) β a delta
        L K steps (RankThreeOptionSystem.OriginalIterationState.full Hlarge)
        final)
      (hactive : ∀ j, j ∈ Hlarge.activeJobs)
      (htrace : ∀ v,
        stateActiveStarWeight (G.largeEdgeRestriction β) final v ≤
          (1 - (1 - delta) * a / 8) ^ steps *
            stateActiveStarWeight (G.largeEdgeRestriction β)
              (RankThreeOptionSystem.OriginalIterationState.full Hlarge) v +
            (((L + 1) * (K - 1) : ℕ) : ℝ)),
    ∃ (M : Finset Option), H.IsPartialMatching M ∧
      ∀ v, G.uncoveredLargeStarWeight H β M v ≤
        (1 - (1 - delta) * a / 8) ^ steps * n +
          (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  dsimp only
  letI : DecidableEq (H.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem H β
  intro final T hactive htrace
  let M := G.liftLargeEdgeJobSet H β final.matching
  refine ⟨M, G.liftLargeEdgeJobSet_isPartialMatching H β
    final.matching_isPartial, ?_⟩
  intro v
  have hinitial :=
    RankThreeOptionSystem.OriginalIterationState.Multigraph.stateActiveStarWeight_full_eq_total
      (G.largeEdgeRestriction β) hactive v
  have hrestricted :
      (∑ e ∈ G.largeEdgeJobs β,
        if G.Inc v e then G.weight e else 0) ≤ G.starWeight v := by
    simpa using G.restrictedStarWeight_le_starWeight
      (G.largeEdgeJobs β) v
  have hlarge :
      (∑ e ∈ Finset.univ,
        if (G.largeEdgeRestriction β).Inc v e then
          (G.largeEdgeRestriction β).weight e else 0) ≤ n := by
    have hsub :
        (∑ e ∈ Finset.univ,
          if (G.largeEdgeRestriction β).Inc v e then
            (G.largeEdgeRestriction β).weight e else 0) ≤
          G.starWeight v := by
      change (∑ e : {e // e ∈ G.largeEdgeJobs β},
        if G.Inc v e.1 then G.weight e.1 else 0) ≤ G.starWeight v
      calc
        (∑ e : {e // e ∈ G.largeEdgeJobs β},
            if G.Inc v e.1 then G.weight e.1 else 0) =
            ∑ e ∈ G.largeEdgeJobs β,
              if G.Inc v e then G.weight e else 0 := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach (G.largeEdgeJobs β)
            (fun e ↦ if G.Inc v e then G.weight e else 0)
        _ ≤ G.starWeight v := hrestricted
    exact hsub.trans (hstar v)
  rw [G.endpointSharpTrace_uncoveredLargeStarWeight_lift_eq_state
    H T hactive v]
  have hraw := htrace v
  rw [hinitial] at hraw
  have hpow0 : 0 ≤ (1 - (1 - delta) * a / 8) ^ steps :=
    pow_nonneg htheta0 _
  exact hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlarge hpow0) le_rfl)

/-- An actual partial matching of selected copied large jobs exists with the
closed iteration's uniform endpoint loss. -/
theorem exists_selectedMixedMaskedLargePartialMatching
    {n N reserve C E S0 steps L K lambda mult : ℕ}
    {rho omega C0 extraGamma bound alpha gamma delta : ℝ}
    (hmult : G.PairMultiplicityAtMost mult)
    (hn : 0 < n) (hN : 0 < N)
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
    (bucket : G.E → Class)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hcapacity : ∀ v c place,
      G.selectedMixedCandidateCapacityLoad
        proposal edgeLabel qLaw R rho omega choice c
          (Sum.inl (G.selectedMixedLargeCandidateRow
            proposal edgeLabel qLaw R choice v c place)) < bound)
    (hordinaryCap : (N : ℝ) * bound ≤ S0)
    (hreserve : 0 < reserve)
    (hextraGamma0 : 0 ≤ extraGamma)
    (hextraGamma1 : extraGamma < 1)
    (hextraCap : (1 - extraGamma) * N ≤ S0)
    (hordinaryCodegree : (N : ℝ) *
      ((explicitLargeSlotBound β qstep r : ℝ) *
        mixedGraphCandidateCapacityScale (Label := Label)
          (β := β) (qstep := qstep) (r := r) rho s omega C0 /
          (n : ℝ)) ≤ lambda)
    (hordinaryPair : mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 / n ≤
        1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hpairCodegree : (mult : ℝ) * N / reserve ≤ lambda)
    (hCN : C ≤ N) (hNC : 0 < N - C)
    (hE : 2 * ((n : ℝ) / β / (1 - extraGamma) +
      1 + reserve) ≤ E)
    (hchoiceCap : Fintype.card Color * explicitLargeSlotBound β qstep r *
      explicitLargeSlotBound β qstep r + E ≤ C)
    (numeric : MixedMaskedClosedScalars β alpha gamma delta
      N C S0 lambda L K steps) :
    let residual := G.selectedMixedLargeResidual
      proposal edgeLabel qLaw R rho omega choice
    let x := G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice
    let Hbase := (G.dyadicLargeEdgeOptionSystem
      (Color := Color) (explicitLargeSlotBound β qstep r)
      bucket extraGamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket extraGamma reserve residual x)
    ∃ (M : Finset (QuantizedCopy N
        (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
          bucket extraGamma reserve residual x))),
      Hbase.IsPartialMatching M ∧
      ∀ v, G.uncoveredLargeStarWeight Hbase β M v ≤
        (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps * n +
          (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  dsimp only
  let residual := G.selectedMixedLargeResidual
    proposal edgeLabel qLaw R rho omega choice
  let x := G.selectedMixedNormalizedLargeOptionMass
    proposal edgeLabel qLaw R rho omega choice
  let Hbase := (G.dyadicLargeEdgeOptionSystem
    (Color := Color) (explicitLargeSlotBound β qstep r)
    bucket extraGamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket extraGamma reserve residual x)
  letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem Hbase β
  obtain ⟨final, T, _hdegree, _hslot, htrace⟩ :=
    G.exists_selectedMixedMaskedClosedEndpointIteration
      proposal edgeLabel qLaw R hmult hn hN hq0 hqmarg hqsingle hqsum
      hs hqstep hr0 hleft homega0 homega1 hrho hC0 hproposal0 hproposal
      choice bucket hstar hcapacity hordinaryCap hreserve
      hextraGamma0 hextraGamma1 hextraCap hordinaryCodegree hordinaryPair
      hextraCodegree hpairCodegree hCN hE hchoiceCap numeric
  have hchoices : ∀ e,
      Fintype.card Color * explicitLargeSlotBound β qstep r *
          explicitLargeSlotBound β qstep r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.boundedDyadicExtraSlotCount bucket residual
            extraGamma reserve) e ≤ C := by
    intro e
    exact (Nat.add_le_add_left
      (G.selectedMixedLargeResidual_supportCount_le
        proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
        hleft homega0 homega1 hrho hproposal0 choice hstar
        bucket extraGamma reserve E hreserve hextraGamma1 hE e) _).trans
        hchoiceCap
  have hactive : ∀ j, j ∈ Hlarge.activeJobs :=
    G.selectedMixedLargeMasked_activeJobs_all
      proposal edgeLabel qLaw R hq0 hqsum hqsingle hs hqstep hr0
      hleft homega0 homega1 hrho hproposal0 choice bucket extraGamma
      reserve N C hCN hNC hchoices
  have htheta0 : 0 ≤
      1 - (1 - delta) * variableSlackA alpha gamma lambda / 8 := by
    linarith [numeric.thetaOne]
  exact G.exists_largePartialMatching_of_closedTrace_uniform Hbase
    hstar htheta0 final T hactive htrace

end WeightedMultigraph

end

end WeightedEdgeColoring
