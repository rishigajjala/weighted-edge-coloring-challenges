import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileLargeClosedMatching

/-!
# One-call large matching from color-dependent selected profiles

This theorem runs the closed endpoint iteration and immediately decodes its
ordinary options.  The endpoint trace, private-extra reserve, and filtered
retained residual are combined into one caller-supplied large-loss budget.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

open RankThreeOptionSystem.OriginalIterationState
open RankThreeOptionSystem.OriginalIterationState.Multigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n N reserve C E S0 steps L K lambda mult : ℕ}
variable {s β q r proposalGamma extraGamma rho omega C0 scale deviation
    ordinaryRate alpha delta iterationGamma residualBudget largeLoss : ℝ}
variable {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

set_option maxHeartbeats 1000000 in
theorem exists_colorDependentLargeMatchingData_of_closedIteration
    (hmult : G.PairMultiplicityAtMost mult)
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hN : 0 < N) (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 ≤ rho) (hscale : 0 < scale)
    (hC0 : 0 ≤ C0) (hproposal0 : ∀ e c, 0 ≤ proposal e c)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (selected : G.ColorDependentSelectedStates proposal R)
    (hstar : ∀ v, G.starWeight v ≤ n)
    (hrow : ∀ v c slot,
      FiniteCategoricalSelection.rowLoad
        (G.colorDependentBlockCandidateUse proposal R n scale rho omega)
        (G.selectedColorDependentLargeCapacityRow proposal R selected v c slot)
        (G.encodedColorDependentSelectedBlock proposal R selected) <
      (n : ℝ) * (rho / (1 - omega)) / scale + deviation)
    (hordinaryRate : rho / (1 - omega) + scale / n * deviation ≤ ordinaryRate)
    (hordinarySlotCap : (N : ℝ) * ordinaryRate ≤ S0)
    (hreserve : 0 < reserve)
    (hextraGamma0 : 0 ≤ extraGamma) (hextraGamma1 : extraGamma < 1)
    (hextraGammaHalf : extraGamma ≤ 1 / 2)
    (hextraSlotCap : (1 - extraGamma) * N ≤ S0)
    (hordinaryJobCodegree : (N : ℝ) *
      (2 * colorDependentCandidateCapacityScale
        rho s omega β q r C0 / n) ≤ lambda)
    (hordinaryPair : 2 * colorDependentCandidateCapacityScale
      rho s omega β q r C0 / n ≤ 1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hpairCodegree : (mult : ℝ) * (N : ℝ) / reserve ≤ lambda)
    (hCN : C ≤ N)
    (hE : 2 * (((n : ℕ) : ℝ) / β / (1 - extraGamma) +
      1 + reserve) ≤ E)
    (hchoiceCap : (B * k) * explicitLargeSlotBound β q r *
        explicitLargeSlotBound β q r + E ≤ C)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hiterationGamma0 : 0 < iterationGamma)
    (hiterationGammaHalf : iterationGamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hK : 0 < K) (hlambda : 0 < lambda)
    (htheta1 : (1 - delta) * variableSlackA alpha iterationGamma lambda / 8 ≤ 1)
    (hjobRate0 : 0 ≤ fixedSlackJobRetention
      (variableSlackA alpha iterationGamma lambda) iterationGamma -
        variableSlackEta alpha iterationGamma lambda)
    (hslotRate0 : 0 ≤ fixedSlackSlotRetention
      (variableSlackA alpha iterationGamma lambda) iterationGamma *
        (1 - iterationGamma) +
        3 * variableSlackEta alpha iterationGamma lambda)
    (hgap0 : (S0 : ℝ) ≤
      (1 - iterationGamma) * (((N - C : ℕ) : ℝ)))
    (hmargin : ∀ t < steps, 1 - iterationGamma ≤
      (variableSlackA alpha iterationGamma lambda * iterationGamma *
          (1 - iterationGamma) -
        ((1 - iterationGamma) * variableSlackEta alpha iterationGamma lambda +
          3 * variableSlackEta alpha iterationGamma lambda)) *
        naturalSharpJobScale (N - C)
          (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) t)
    (hpositive : ∀ t < steps, 5 ≤
      naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t)
    (hnextPositive : ∀ t < steps,
      0 < (fixedSlackJobRetention
          (variableSlackA alpha iterationGamma lambda) iterationGamma -
          variableSlackEta alpha iterationGamma lambda) *
        naturalSharpJobScale (N - C)
          (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) t)
    (hKdegree : ∀ t < steps, K ≤
      naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t)
    (hscaleIteration : ∀ t < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t
      1000 * (lambda + 1) ≤ iterationGamma * d)
    (hgroupScale : ∀ t < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t
      isolatedVariableZ d + 1 ≤
        delta ^ 2 * variableSlackA alpha iterationGamma lambda * K / 64)
    (hslotScale : ∀ t < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t
      isolatedVariableZ d + 1 ≤
        variableSlackEta alpha iterationGamma lambda ^ 2 * d /
          (96 * variableSlackA alpha iterationGamma lambda * lambda))
    (hjobScale : ∀ t < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t
      isolatedVariableZ d + Real.log 2 ≤
        variableSlackEta alpha iterationGamma lambda ^ 2 * d /
          (16 * variableSlackA alpha iterationGamma lambda * lambda))
    (hblock : ∀ t < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t
      128 * lambda * (isolatedVariableMoment d : ℝ) ^ 2 ≤
        delta * alpha * iterationGamma * K)
    (haSmall : variableSlackA alpha iterationGamma lambda ≤ delta / 96)
    (hsquare : ∀ t < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) t
      lambda ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
        variableSlackBeta0 alpha iterationGamma * d)
    (hB : 0 < B) (hk : 0 < k) (hNC : 0 < N - C)
    (hdyadicTop : dyadicScale β L ≤ 2)
    (hresidual : ∀ v,
      G.weightedResidualStar
        (G.selectedColorDependentRetainedMacroscopicResidual
          proposal R proposalGamma β rho omega
          (G.encodedColorDependentSelectedBlock proposal R selected)) v ≤
        residualBudget)
    (hresidualBudget0 : 0 ≤ residualBudget)
    (hlargeBudget :
      (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^ steps * n +
        (((L + 1) * (K - 1) : ℕ) : ℝ) +
        8 * residualBudget +
        8 * (1 + (reserve : ℝ)) ≤ largeLoss) :
    ∃ (M : Finset (OrdinarySlotChoice G.E (Fin (B * k))
          (explicitLargeSlotBound β q r)))
      (hM : (OrdinarySlotChoice.system G.fst G.snd
          (explicitLargeSlotBound β q r)).IsPartialMatching M),
      G.ordinarySelectedEdges M ⊆ G.largeEdgeJobs β ∧
      (∀ e ∈ G.ordinarySelectedEdges M,
        0 < proposal e (finProdFinEquiv.symm
          (G.extendSelectedOrdinaryColor (Nat.mul_pos hB hk) M hM e))) ∧
      (∀ v c,
        G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
          ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
            (selected v c.1 c.2) i) ∧
      ∀ v,
        (∑ e ∈ G.retainedMacroscopicEdges proposal proposalGamma β \
            G.ordinarySelectedEdges M,
          if G.Inc v e then G.weight e else 0) ≤ largeLoss := by
  let Hbase := G.colorDependentSelectedDyadicSystem
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R proposalGamma extraGamma rho omega selected
  letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem Hbase β
  classical
  have hextraGammaGap : 0 < 1 - extraGamma := sub_pos.mpr hextraGamma1
  have hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r * explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd
          (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
          (G.boundedDyadicExtraSlotCount
            (G.colorDependentRetainedDyadicBucket proposal proposalGamma β L)
            (G.selectedColorDependentLargeResidual proposal R rho omega selected)
            extraGamma reserve) e ≤ C := by
    intro e
    exact (Nat.add_le_add_left
      (G.colorDependent_graphDyadicLargeResidual_supportCount_le proposal R
        hs hq hr0 hleft homega0 homega1 hrho selected hstar hreserve
        hextraGamma1 E hE e) _).trans hchoiceCap
  obtain ⟨final, T, _hdegree, _hslot, htraceRaw⟩ :=
    G.exists_colorDependentSelectedDyadicClosedEndpointIteration
      (proposalGamma := proposalGamma) proposal R
      hmult hn hs hq hr0 hN hleft homega0 homega1 hrho hscale hC0 hproposal0
      hproposal selected hstar hrow hordinaryRate hordinarySlotCap hreserve
      hextraGamma0 hextraGamma1 hextraSlotCap hordinaryJobCodegree
      hordinaryPair hextraCodegree hpairCodegree hCN hE hchoiceCap hdyadicCover halpha
      halphaSmall hiterationGamma0 hiterationGammaHalf hdelta0 hdelta1 hK
      hlambda htheta1 hjobRate0 hslotRate0 hgap0 hmargin hpositive
      hnextPositive hKdegree hscaleIteration hgroupScale hslotScale hjobScale
      hblock haSmall hsquare
  have hactive0 : ∀ j, j ∈ Hlarge.activeJobs := by
    intro j
    rw [RankThreeOptionSystem.mem_activeJobs]
    apply Finset.card_pos.mp
    exact hNC.trans_le
      (G.colorDependentSelectedDyadicLarge_jobDegree_lower proposal R
        hs hq hr0 hleft homega0 homega1 hrho selected hCN hchoices j)
  let traceLoss : ℝ :=
    (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^ steps * n +
      (((L + 1) * (K - 1) : ℕ) : ℝ)
  have hstate : ∀ v,
      RankThreeOptionSystem.OriginalIterationState.Multigraph.stateActiveStarWeight
        (G.largeEdgeRestriction β) final v ≤ traceLoss := by
    intro v
    have hraw := htraceRaw v
    have hinitial :=
      RankThreeOptionSystem.OriginalIterationState.Multigraph.stateActiveStarWeight_full_eq_total
        (G.largeEdgeRestriction β) hactive0 v
    have htotal :
        (∑ e ∈ Finset.univ,
          if (G.largeEdgeRestriction β).Inc v e then
            (G.largeEdgeRestriction β).weight e else 0) ≤ n := by
      have hrestricted :
          (∑ e ∈ G.largeEdgeJobs β,
            if G.Inc v e then G.weight e else 0) ≤ G.starWeight v := by
        simpa using
          (G.restrictedStarWeight_le_starWeight
            (G.largeEdgeJobs β) v)
      have hlarge :
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
      exact hlarge.trans (hstar v)
    have htheta0 : 0 ≤
        1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8 := by
      have ha0 := (variableSlackA_pos halpha hiterationGamma0 hlambda).le
      have hdeltaFactor : 0 ≤ 1 - delta := by linarith
      nlinarith
    have hpow0 : 0 ≤
        (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^ steps :=
      pow_nonneg htheta0 _
    rw [hinitial] at hraw
    have hscaled := mul_le_mul_of_nonneg_left htotal hpow0
    exact hraw.trans (by
      dsimp [traceLoss]
      exact add_le_add hscaled le_rfl)
  obtain ⟨M, hM, hsubset, hsupport, hload, hloss⟩ :=
    G.exists_colorDependentLargeMatchingData_of_closedTrace proposal R
      hs hq hr0 hleft homega0 homega1 hrho hproposal0 hB hk selected hCN hNC
      hchoices hdyadicCover hdyadicTop hreserve hextraGamma1
      (variableSlackA alpha iterationGamma lambda) delta final T hstate
  refine ⟨M, hM, hsubset, hsupport, hload, ?_⟩
  intro v
  have hscaled :
      4 * G.weightedResidualStar
          (G.selectedColorDependentRetainedMacroscopicResidual
            proposal R proposalGamma β rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)) v /
          (1 - extraGamma) ≤
        4 * residualBudget / (1 - extraGamma) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hresidual v)
        (show (0 : ℝ) ≤ 4 by norm_num))
      hextraGammaGap.le
  have hbudgetScaled :
      4 * residualBudget / (1 - extraGamma) ≤ 8 * residualBudget := by
    apply (div_le_iff₀ hextraGammaGap).2
    nlinarith
  have hresTerm :
      4 * G.weightedResidualStar
          (G.selectedColorDependentRetainedMacroscopicResidual
            proposal R proposalGamma β rho omega
            (G.encodedColorDependentSelectedBlock proposal R selected)) v /
          (1 - extraGamma) ≤
        8 * residualBudget :=
    hscaled.trans hbudgetScaled
  have hcombined :
      traceLoss +
          4 * G.weightedResidualStar
            (G.selectedColorDependentRetainedMacroscopicResidual
              proposal R proposalGamma β rho omega
              (G.encodedColorDependentSelectedBlock proposal R selected)) v /
            (1 - extraGamma) +
          8 * (1 + (reserve : ℝ)) ≤
        traceLoss + 8 * residualBudget + 8 * (1 + (reserve : ℝ)) :=
    add_le_add (add_le_add le_rfl hresTerm) le_rfl
  have hbudget :
      traceLoss + 8 * residualBudget + 8 * (1 + (reserve : ℝ)) ≤
        largeLoss := by
    simpa [traceLoss] using hlargeBudget
  exact (hloss v).trans (hcombined.trans hbudget)

end WeightedMultigraph

end

end WeightedEdgeColoring
