import WeightedEdgeColoring.ExtendedProfileSelectedCanonicalData
import WeightedEdgeColoring.ExtendedProfileSelectedDyadicClosedEndpointIteration
import WeightedEdgeColoring.ExtendedProfileSelectedSmallLossDecoder

/-!
# Closed selected-profile partial rounding

This is the deterministic outer composition used by the simple-graph
application.  It chooses the block profiles, runs the isolated endpoint
iteration, and decodes the accumulated matching.  The statement exposes
only scalar inequalities; in particular neither the selected profiles nor
an intermediate matching occur among its hypotheses.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k N reserve C S0 lambda steps L K E : ℕ}
variable {s beta q r extraGamma rho omega ordinaryRate : ℝ}
variable {alpha gamma delta epsilon : ℝ}
variable {hbeta : 0 < beta} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s beta q r hbeta hr)

include R0

/- Canonical selection, the closed isolated iteration, and the decoder in
one theorem.  `E` is a uniform bound for the number of cyclic extra choices
incident with one edge. -/
set_option maxHeartbeats 800000 in
theorem exists_partialColoring_of_selectedBlockDyadicClosedIteration
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s) (hs1 : s ≤ 1)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hrs : rho * s ≤ 1)
    (hrhoKappa : rho ≤ extendedProfileSmoothingKappa omega beta q r)
    (hpack : G.LocallyPacksInto (B * k))
    (hjointError :
      extendedProfileCandidateCapacityScale rho s omega beta q r /
            ((B * k : ℕ) : ℝ) *
          extendedProfileBlockCombinedDeviation rho s omega beta q r B k +
          2 * beta ≤
        (1 - rho / extendedProfileSmoothingKappa omega beta q r) * r)
    (hordinaryRate :
      rho / extendedProfileSmoothingKappa omega beta q r +
          extendedProfileCandidateCapacityScale rho s omega beta q r /
            ((B * k : ℕ) : ℝ) *
              extendedProfileBlockCombinedDeviation
                rho s omega beta q r B k ≤ ordinaryRate)
    (hordinarySlotCap : (N : ℝ) * ordinaryRate ≤ S0)
    (hreserve : 0 < reserve)
    (hextraGamma0 : 0 ≤ extraGamma) (hextraGammaHalf : extraGamma ≤ 1 / 2)
    (hextraSlotCap : (1 - extraGamma) * N ≤ S0)
    (hsupportE :
      2 * (((B * k : ℕ) : ℝ) / beta / (1 - extraGamma) +
        1 + reserve) ≤ E)
    (hchoiceCap :
      (B * k) * explicitLargeSlotBound beta q r *
          explicitLargeSlotBound beta q r + E ≤ C)
    (hordinaryJobCodegree : (N : ℝ) *
      ((explicitLargeSlotBound beta q r : ℝ) *
        extendedProfileCandidateCapacityScale rho s omega beta q r /
          (B * k : ℕ)) ≤ lambda)
    (hordinaryPair :
      extendedProfileCandidateCapacityScale rho s omega beta q r /
          (B * k : ℕ) ≤ 1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hCN : C ≤ N) (hNC : 0 < N - C)
    (hdyadicCover : 1 ≤ dyadicScale beta L)
    (hdyadicTop : dyadicScale beta L ≤ 2)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hK : 0 < K) (hlambda : 0 < lambda)
    (htheta1 :
      (1 - delta) * variableSlackA alpha gamma lambda / 8 ≤ 1)
    (hjobRate0 : 0 ≤ fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)
    (hslotRate0 : 0 ≤ fixedSlackSlotRetention
      (variableSlackA alpha gamma lambda) gamma * (1 - gamma) +
        3 * variableSlackEta alpha gamma lambda)
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * (N - C))
    (hmargin : ∀ n < steps, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          (N - C) (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
    (hpositive : ∀ n < steps, 5 ≤
      RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n)
    (hnextPositive : ∀ n < steps,
      0 < (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
          variableSlackEta alpha gamma lambda) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          (N - C) (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
    (hKdegree : ∀ n < steps, K ≤
      RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n)
    (hscale : ∀ n < steps,
      let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      1000 * ((lambda : ℝ) + 1) ≤ gamma * d)
    (hgroupScale : ∀ n < steps,
      let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      isolatedVariableZ d + 1 ≤
        delta ^ 2 * variableSlackA alpha gamma lambda * K / 64)
    (hslotScale : ∀ n < steps,
      let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      isolatedVariableZ d + 1 ≤
        variableSlackEta alpha gamma lambda ^ 2 * d /
          (96 * variableSlackA alpha gamma lambda * lambda))
    (hjobScale : ∀ n < steps,
      let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      isolatedVariableZ d + Real.log 2 ≤
        variableSlackEta alpha gamma lambda ^ 2 * d /
          (16 * variableSlackA alpha gamma lambda * lambda))
    (hblock : ∀ n < steps,
      let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      128 * (lambda : ℝ) * (isolatedVariableMoment d : ℝ) ^ 2 ≤
        delta * alpha * gamma * K)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hsquare : ∀ n < steps,
      let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
        (N - C) (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
        variableSlackBeta0 alpha gamma * d)
    (htraceBudget :
      (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps *
            (B * k : ℕ) +
          (((L + 1) * (K - 1) : ℕ) : ℝ) ≤ epsilon * (B * k : ℕ))
    (hepsilon : 0 ≤ epsilon)
    (hsigma0 : 0 ≤
      extendedProfileBlockQuadraticBound rho s omega beta q r B k)
    (hsigma :
      extendedProfileBlockQuadraticBound rho s omega beta q r B k ≤
        epsilon ^ 2 * (B * k : ℕ))
    (hrhoLoss : 1 - rho * s ≤ epsilon)
    (hone : 1 ≤ epsilon * (B * k : ℕ))
    (hreserveSmall : (reserve : ℝ) ≤ epsilon * (B * k : ℕ))
    (hbetaSmall : beta ≤ epsilon * (B * k : ℕ)) :
    ∃ (P : Finset G.E) (color : G.E → Fin (B * k)),
      G.asMultigraph.IsFeasibleOn P color ∧
      ∀ v,
        (∑ e ∈ Finset.univ \ P,
          if G.Inc v e then G.weight e else 0) ≤
            37 * epsilon * (B * k : ℕ) := by
  obtain ⟨choice, hchoicePos, hcapacity, hquad, hcapacityTiny⟩ :=
    G.exists_selectedBlockData_for_dyadicIteration_canonical R0
      hB hk hn hs hspos hq hr0 hleft omega homega0 homega1 rho hrho hpack
  let bucket : G.E → Fin (L + 1) := dyadicBucket beta L G.weight
  have hextraGamma1 : extraGamma < 1 :=
    hextraGammaHalf.trans_lt (by norm_num)
  have hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound beta q r *
          explicitLargeSlotBound beta q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.graphDyadicExtraSlotCount bucket
            (G.selectedBlockLargeResidual R0 omega rho choice)
            extraGamma reserve) e ≤ C := by
    intro e
    have hsupport := G.graphDyadicLargeResidual_supportCount_le R0
      hn hs hq hr0 hleft omega homega0 homega1 rho hrho.le choice bucket
      hpack hreserve hextraGamma1 E hsupportE e
    exact (Nat.add_le_add_left hsupport _).trans hchoiceCap
  obtain ⟨final, T, hdegree, hslot, htraceRaw⟩ :=
    G.exists_selectedBlockDyadicClosedEndpointIteration R0 hn hs hspos hq
      hr0 (by omega) hleft omega homega0 homega1 rho hrho choice bucket
      (extendedProfileBlockCombinedDeviation rho s omega beta q r B k)
      ordinaryRate hcapacity hordinaryRate hordinarySlotCap hreserve
      hextraGamma0 hextraGamma1 hgamma0 hgammaHalf hextraSlotCap
      hordinaryJobCodegree hordinaryPair hextraCodegree hCN hchoices
      hdyadicCover halpha halphaSmall hdelta0 hdelta1 hK hlambda htheta1
      hjobRate0 hslotRate0 hgap0 hmargin hpositive hnextPositive hKdegree
      hscale hgroupScale hslotScale hjobScale hblock haSmall hsquare
  have hactive0 : ∀ j, j ∈
      (G.largeEdgeJobSystem
        (G.selectedBlockDyadicQuantizedSystem
          (N := N) (reserve := reserve) (gamma := extraGamma)
          R0 omega rho choice bucket) beta).activeJobs := by
    intro j
    exact G.selectedBlockDyadicLarge_mem_activeJobs R0 hn hs hq hr0 hleft
      omega homega0 homega1 rho hrho.le choice bucket hCN hNC hchoices j
  have htrace : ∀ v,
      RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight
        (G.largeEdgeRestriction beta) final v ≤ epsilon * (B * k : ℕ) := by
    intro v
    have hraw := htraceRaw v
    have hinitial :=
      RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight_full_eq_total
        (G.largeEdgeRestriction beta) hactive0 v
    have htotal :
        (∑ e ∈ Finset.univ,
          if (G.largeEdgeRestriction beta).Inc v e then
            (G.largeEdgeRestriction beta).weight e else 0) ≤
          (B * k : ℕ) := by
      have hstar := G.starWeight_le_of_locallyPacksInto hpack v
      have hrestricted :
          (∑ e ∈ G.largeEdgeJobs beta,
            if G.Inc v e then G.weight e else 0) ≤ G.starWeight v := by
        simpa using
          (G.toMultigraph.restrictedStarWeight_le_starWeight
            (G.largeEdgeJobs beta) v)
      have hlarge :
          (∑ e ∈ Finset.univ,
            if (G.largeEdgeRestriction beta).Inc v e then
              (G.largeEdgeRestriction beta).weight e else 0) ≤
            G.starWeight v := by
        change (∑ e : {e // e ∈ G.largeEdgeJobs beta},
          if G.Inc v e.1 then G.weight e.1 else 0) ≤ G.starWeight v
        calc
          (∑ e : {e // e ∈ G.largeEdgeJobs beta},
              if G.Inc v e.1 then G.weight e.1 else 0) =
              ∑ e ∈ G.largeEdgeJobs beta,
                if G.Inc v e then G.weight e else 0 := by
            rw [Finset.univ_eq_attach]
            exact Finset.sum_attach (G.largeEdgeJobs beta)
              (fun e ↦ if G.Inc v e then G.weight e else 0)
          _ ≤ G.starWeight v := hrestricted
      exact hlarge.trans hstar
    rw [hinitial] at hraw
    have htheta0 : 0 ≤
        1 - (1 - delta) * variableSlackA alpha gamma lambda / 8 := by
      have ha0 := variableSlackA_pos halpha hgamma0 hlambda
      have hdeltaFactor : 0 ≤ 1 - delta := by linarith
      nlinarith
    have hpow0 : 0 ≤
        (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps :=
      pow_nonneg htheta0 _
    have hscaled :
        (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps *
              (∑ e ∈ Finset.univ,
                if (G.largeEdgeRestriction beta).Inc v e then
                  (G.largeEdgeRestriction beta).weight e else 0) +
            (((L + 1) * (K - 1) : ℕ) : ℝ) ≤
          (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps *
              (B * k : ℕ) +
            (((L + 1) * (K - 1) : ℕ) : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left htotal hpow0) le_rfl
    exact hraw.trans (hscaled.trans htraceBudget)
  exact G.exists_partialColoring_of_selectedBlockDyadicTrace_smallLoss R0
    hn hs hq hr0 hr1 hleft homega0 homega1 hrho.le hrs hrhoKappa choice
    hcapacityTiny hjointError hreserve hextraGamma0 hextraGammaHalf
    hdyadicCover hdyadicTop final T hactive0 htrace hquad hpack hepsilon
    hsigma0 hsigma hrhoLoss hone hreserveSmall hbetaSmall

end WeightedSimpleGraph

end

end WeightedEdgeColoring
