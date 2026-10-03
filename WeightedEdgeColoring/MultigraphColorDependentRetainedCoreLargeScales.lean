import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileLargeClosedMatchingOneCall
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileRetainedResidual
import WeightedEdgeColoring.MultigraphColorDependentRetainedCoreScalars
import WeightedEdgeColoring.MultigraphColorDependentRetainedCoreRoundingProof
import WeightedEdgeColoring.BoundedMultiplicityDyadicOuterStructuralScales

import WeightedEdgeColoring.VariableSlackGeometricSteps
import WeightedEdgeColoring.VariableSlackIterationScalars


/-!
# Closed large matching at the retained-core scale

This file makes the polynomial choices for the colour-dependent large-edge
iteration.  The proposal cutoff and the iteration slack are deliberately
different: the former is `gamma`, while the latter is `tau / 8`.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

private def retainedNibbleAlpha : ℝ := 1 / 200000

private theorem retainedNibbleAlpha_pos : 0 < retainedNibbleAlpha := by
  norm_num [retainedNibbleAlpha]

/-- Exact capacity rows imply the common large-slot row bound consumed by
the quantized option system. -/
theorem selectedLargeCapacityRow_lt_common
    (G : WeightedMultigraph.{u})
    {mult B k n : ℕ} {s β q r rho omega C0 D : ℝ}
    (hmult : 0 < mult)
    {hβ : 0 < β} {hr : 0 < r}
    (proposal : G.E → (Fin B × Fin k) → ℝ)
    (R : ∀ v c, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)
    (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega < 1)
    (hspos : 0 < s) (hrhopos : 0 < rho) (hC0 : 0 < C0)
    (selected : G.ColorDependentSelectedStates proposal R)
    (hcapacity : ∀ row : G.ColorDependentExtendedProfileCapacityRow
        (G.ColorDependentCandidateRowAt R),
      FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse proposal R n
            ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
            rho omega) row
          (G.encodedColorDependentSelectedBlock proposal R selected) <
        FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
          (G.colorDependentBlockCandidateUse proposal R n
            ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
            rho omega) row + D) :
    ∀ v c slot,
      FiniteCategoricalSelection.rowLoad
          (G.colorDependentBlockCandidateUse proposal R n
            ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
            rho omega)
          (G.selectedColorDependentLargeCapacityRow proposal R selected v c slot)
          (G.encodedColorDependentSelectedBlock proposal R selected) <
        (n : ℝ) * (rho / (1 - omega)) /
            ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0) + D := by
  intro v c slot
  let row := G.selectedColorDependentLargeCapacityRow proposal R selected v c slot
  have hrow := hcapacity row
  have hmean :
      FiniteCategoricalSelection.rowMean
          (G.paddedColorDependentExtendedProfileBlockProbability proposal R omega)
          (G.colorDependentBlockCandidateUse proposal R n
            ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
            rho omega) row ≤
        (n : ℝ) * (rho / (1 - omega)) /
          ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0) := by
    rw [G.colorDependentBlockCandidate_rowMean_eq]
    exact G.scaledColorDependentCandidateAtomMean_le_one_sub_omega
      proposal R n
      ((mult : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
      hs hq hr0 hleft homega0 homega1 hrhopos.le
      (mul_pos (by exact_mod_cast hmult)
        (colorDependentCandidateCapacityScale_pos
          (C0 := C0) hrhopos hspos hC0 homega0))
      row.1 row.2
  exact hrow.trans_le (by
    simpa [add_comm] using add_le_add_right hmean D)

set_option maxHeartbeats 400000 in
/-- For fixed retained-core accuracy, every sufficiently large ambient
star scale admits the large matching required by the final decoder. -/
theorem exists_retainedCoreLargeMatching_eventually
    {mult : ℕ} {C0 gamma eta : ℝ}
    (hmultPos : 0 < mult)
    (hC0 : 0 < C0) (hgamma0 : 0 < gamma) (hgammaEta : 64 * gamma < eta)
    (heta1 : eta < 1) :
    ∃ N0 : ℕ, ∀ (G : WeightedMultigraph.{u}) (n B k : ℕ)
      (x : G.E → Fin (B * k) → ℝ),
      N0 ≤ n → G.PairMultiplicityAtMost mult →
      (hB : 0 < B) → (hk4 : 4 ≤ k) → B * k ≤ 4 * n →
      (∀ v, G.starWeight v ≤ n) →
      (∀ e c, 0 ≤ x e c ∧ x e c ≤ C0 / n) →
      (∀ e, ∑ c, x e c ≤ 1) →
      let tau := retainedCoreTau C0 gamma eta
      let proposal := G.retainedCoreProductProposal x
      let scale := (mult : ℝ) * colorDependentCandidateCapacityScale
        (jointProfileRho tau) (jointProfileS tau) (jointProfileOmega tau)
        (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau) C0
      let D := FinitePartialResamplingNumerics.packingDeviation n
        (colorDependentBlockCombinedColumnBound n k
          (jointProfileBeta tau) (jointProfileQ tau) (jointProfileR tau))
      ∀ (hβ : 0 < jointProfileBeta tau) (hr : 0 < jointProfileR tau)
        (R : ∀ v c, G.BoundedProfileRealization
          (fun e : G.StarEdge v ↦ proposal e.1 c)
          (jointProfileS tau) (jointProfileBeta tau)
          (jointProfileQ tau) (jointProfileR tau) hβ hr)
        (selected : G.ColorDependentSelectedStates proposal R),
        (∀ row : G.ColorDependentExtendedProfileCapacityRow
            (G.ColorDependentCandidateRowAt R),
          FiniteCategoricalSelection.rowLoad
              (G.colorDependentBlockCandidateUse proposal R n scale
                (jointProfileRho tau) (jointProfileOmega tau)) row
              (G.encodedColorDependentSelectedBlock proposal R selected) <
            FiniteCategoricalSelection.rowMean
              (G.paddedColorDependentExtendedProfileBlockProbability proposal R
                (jointProfileOmega tau))
              (G.colorDependentBlockCandidateUse proposal R n scale
                (jointProfileRho tau) (jointProfileOmega tau)) row + D) →
        scale / n * D ≤ tau ^ 2 / 4 →
        (∀ v,
          G.weightedResidualStar
              (G.selectedColorDependentRetainedMacroscopicResidual
                proposal R gamma (jointProfileBeta tau)
                (jointProfileRho tau) (jointProfileOmega tau)
                (G.encodedColorDependentSelectedBlock proposal R selected)) v ≤
            (gamma + 4 * tau + (eta - gamma) / 1024) * n) →
        ∃ (M : Finset (OrdinarySlotChoice G.E (Fin (B * k))
              (explicitLargeSlotBound (jointProfileBeta tau)
                (jointProfileQ tau) (jointProfileR tau))))
          (hM : (OrdinarySlotChoice.system G.fst G.snd
              (explicitLargeSlotBound (jointProfileBeta tau)
                (jointProfileQ tau) (jointProfileR tau))).IsPartialMatching M),
          G.ordinarySelectedEdges M ⊆ G.largeEdgeJobs (jointProfileBeta tau) ∧
          (∀ e ∈ G.ordinarySelectedEdges M,
            0 < proposal e (finProdFinEquiv.symm
              (G.extendSelectedOrdinaryColor (Nat.mul_pos hB
                (lt_of_lt_of_le (by norm_num) hk4)) M hM e))) ∧
          (∀ v c,
            G.selectedOrdinaryIntegralColorLoad M hM v (finProdFinEquiv c) ≤
              ∑ i, G.colorDependentExtendedProfileConcreteSlotSize R v c
                (selected v c.1 c.2) i) ∧
          ∀ v,
            (∑ e ∈ G.retainedMacroscopicEdges proposal gamma
                (jointProfileBeta tau) \ G.ordinarySelectedEdges M,
              if G.Inc v e then G.weight e else 0) ≤
              (eta - gamma) / 4 * n := by
  let tau := retainedCoreTau C0 gamma eta
  let iterationGamma := tau / 8
  let extraGamma := tau / 4
  let alpha := retainedNibbleAlpha
  let delta : ℝ := 1 / 2
  have hgammaEta' : gamma < eta := by nlinarith
  have hgap0 : 0 < eta - gamma := sub_pos.mpr hgammaEta'
  have htau0 : 0 < tau := retainedCoreTau_pos hC0 hgammaEta'
  have htau1 : tau ≤ 1 / 4 := retainedCoreTau_le_quarter C0 gamma eta
  have hiterationGamma0 : 0 < iterationGamma := by
    dsimp [iterationGamma]; positivity
  have hiterationGammaHalf : iterationGamma ≤ 1 / 2 := by
    dsimp [iterationGamma]; linarith
  have hextraGamma0 : 0 ≤ extraGamma := by
    dsimp [extraGamma]; positivity
  have hextraGammaHalf : extraGamma ≤ 1 / 2 := by
    dsimp [extraGamma]; linarith
  have hextraEq : extraGamma = 2 * iterationGamma := by
    dsimp [extraGamma, iterationGamma]; ring
  have halpha : 0 < alpha := by simpa [alpha] using retainedNibbleAlpha_pos
  have halphaSmall : alpha ≤ 1 / 100000 := by
    norm_num [alpha, retainedNibbleAlpha]
  have halphaOne : alpha ≤ 1 := halphaSmall.trans (by norm_num)
  have halphaSixth : alpha ≤ 1 / 6 := by
    norm_num [alpha, retainedNibbleAlpha]
  have hdelta0 : 0 < delta := by norm_num [delta]
  have hdelta1 : delta ≤ 1 := by norm_num [delta]
  rcases jointProfile_parameters htau0 htau1 with
    ⟨hspos, hbeta, hqpos, hrpos, homega0, homega1, hleft, _hr1,
      hrhopos, _hrhoKappa, _hfraction⟩
  let s := jointProfileS tau
  let beta := jointProfileBeta tau
  let q := jointProfileQ tau
  let r := jointProfileR tau
  let omega := jointProfileOmega tau
  let rho := jointProfileRho tau
  let scale := (mult : ℝ) * colorDependentCandidateCapacityScale rho s omega beta q r C0
  have hs : 0 ≤ s := by simpa [s] using hspos.le
  have hq : 0 ≤ q := by simpa [q] using hqpos.le
  have hr0 : 0 ≤ r := by simpa [r] using hrpos.le
  have hbeta0 : 0 < beta := by simpa [beta] using hbeta
  have hbeta1 : beta ≤ 1 := by
    dsimp [beta, jointProfileBeta]
    nlinarith [sq_nonneg tau]
  have hrho : 0 < rho := by simpa [rho] using hrhopos
  have homegaLt : omega < 1 := by
    dsimp [omega, jointProfileOmega]
    exact htau1.trans_lt (by norm_num)
  have hscale0 : 0 < scale := by
    exact mul_pos (by exact_mod_cast hmultPos)
      (colorDependentCandidateCapacityScale_pos
        (β := beta) (q := q) (r := r) hrho hspos hC0 homega0)
  obtain ⟨L, hdyadicCover, hdyadicTopLt⟩ :=
    exists_dyadic_scale_mem_Ico_one_two beta hbeta0 hbeta1
  have hdyadicTop : dyadicScale beta L ≤ 2 := hdyadicTopLt.le
  let placeCount := explicitLargeSlotBound beta q r
  let A := boundedMultiplicityDyadicFixedCodegreeCoefficient mult 2 scale
  let Ecoef := boundedMultiplicityDyadicSupportCoefficient beta extraGamma
  let Ccoef := 4 * boundedMultiplicityDyadicChoiceCoefficient placeCount beta extraGamma
  have hA : 0 < A := by
    dsimp [A, boundedMultiplicityDyadicFixedCodegreeCoefficient,
      boundedMultiplicityDyadicCodegreeCoefficient]
    omega
  have hCcoef : 0 < Ccoef := by
    dsimp [Ccoef, boundedMultiplicityDyadicChoiceCoefficient, Ecoef,
      boundedMultiplicityDyadicSupportCoefficient]
    omega
  let traceEps : ℝ := (eta - gamma) / 256
  have htraceEps0 : 0 < traceEps := by dsimp [traceEps]; positivity
  have htraceEps1 : traceEps ≤ 1 := by
    dsimp [traceEps]
    have : eta - gamma < 1 := by nlinarith
    linarith
  let T := variableSlackStepMultiplier alpha iterationGamma traceEps
  let decayBudget : ℝ := 3 * alpha * iterationGamma * T
  let cfrac : ℝ := Real.exp (-2 * decayBudget) / 4
  have hcfrac : 0 < cfrac := by dsimp [cfrac]; positivity
  have hclosedEventually := eventually_dyadicSimple_closedRoundScales
    A 1 alpha iterationGamma delta cfrac hA (by norm_num) halpha
      hiterationGamma0 hdelta0 hcfrac
  have hboundaryEventually :=
    eventually_dyadicSimple_fixedEndpointBlock_sublinear
      (L + 1) traceEps htraceEps0
  have hlossEventually := eventually_const_le_pos_mul_nat
    ((Ccoef : ℝ) + 1) iterationGamma hiterationGamma0
  have hpairEventually := eventually_const_le_pos_mul_nat scale 1 (by norm_num)
  have hmarginEventually := eventually_const_le_pos_mul_nat
    (4 * (1 - iterationGamma) * A)
      (alpha * iterationGamma ^ 2 * cfrac) (by positivity)
  have hfloorEventually := eventually_const_le_pos_mul_nat
    (T * A) (Real.exp (-2 * decayBudget) / 4) (by positivity)
  let reserveEps : ℝ := (eta - gamma) / 2048
  have hreserveEps0 : 0 < reserveEps := by dsimp [reserveEps]; positivity
  have hreserveEventually := eventually_const_le_pos_mul_nat
    1 reserveEps hreserveEps0
  have hrootEventually : ∀ᶠ m : ℕ in Filter.atTop, 2 ≤ m :=
    Filter.eventually_ge_atTop 2
  have hall : ∀ᶠ m : ℕ in Filter.atTop,
      (∀ d lambda : ℕ, 0 < d → 0 < lambda →
        cfrac * dyadicSimpleQuantizationScale m ≤ d →
        d ≤ (m + 1) ^ 30 →
        lambda ≤ dyadicSimpleCodegreeScale A m →
        DyadicSimpleClosedRoundScales 1 m d lambda alpha iterationGamma delta) ∧
      (dyadicSimpleEndpointBlockScale (L + 1) m : ℝ) ≤
        traceEps * dyadicSimplePaletteScale m ∧
      (Ccoef : ℝ) + 1 ≤ iterationGamma * m ∧
      scale ≤ (m : ℝ) ∧
      4 * (1 - iterationGamma) * A ≤
        alpha * iterationGamma ^ 2 * cfrac * m ∧
      T * A ≤ Real.exp (-2 * decayBudget) / 4 * m ∧
      1 ≤ reserveEps * m ∧ 2 ≤ m := by
    filter_upwards [hclosedEventually, hboundaryEventually, hlossEventually,
      hpairEventually, hmarginEventually, hfloorEventually,
      hreserveEventually, hrootEventually] with m hclosed hboundary hloss
        hpair hmargin hfloor hreserveGrow hm
    exact ⟨hclosed, hboundary, hloss, (by simpa using hpair), hmargin, hfloor,
      hreserveGrow, hm⟩
  rcases Filter.eventually_atTop.1 hall with ⟨M0, hM0⟩
  refine ⟨max 1 (M0 ^ 20), ?_⟩
  intro G n B k x hnLarge hmult hB hk4 hpalette hstar hx hmass
  dsimp only
  have hn1 : 1 ≤ n := (le_max_left 1 (M0 ^ 20)).trans hnLarge
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hMpow : M0 ^ 20 ≤ n := (le_max_right 1 (M0 ^ 20)).trans hnLarge
  let m := dyadicSimpleRoot n
  have hmM : M0 ≤ m := le_dyadicSimpleRoot_of_pow_le hMpow
  rcases hM0 m hmM with
    ⟨hclosed, hboundary, hloss, hpair, hmarginGrowth, hfloorGrowth,
      hreserveGrowth, hm⟩
  have hnLower : m ^ 20 ≤ n := dyadicSimpleRoot_pow_le n
  have hnUpper : n ≤ 2 ^ 20 * m ^ 20 :=
    boundedMultiplicityDyadic_palette_le_two_pow_mul (show 1 ≤ m by omega)
      (lt_succ_dyadicSimpleRoot_pow n)
  let N := dyadicSimpleQuantizationScale m
  let reserve := dyadicSimpleReserveScale m
  let lambda := dyadicSimpleCodegreeScale A m
  let E := Ecoef * m ^ 20
  let C := Ccoef * m ^ 20
  let d0 := N - C
  let S0 := RankThreeOptionSystem.OriginalIterationState.fixedSlackPaddedSlotTarget
    iterationGamma d0
  let K := dyadicSimpleEndpointBlockScale 1 m
  let steps := variableSlackSteps alpha iterationGamma traceEps lambda
  have hN : 0 < N := by
    dsimp [N]
    exact (dyadicSimple_scales_pos m (by omega)).2.1
  have hreserve : 0 < reserve := by
    dsimp [reserve]
    exact (dyadicSimple_scales_pos m (by omega)).2.2
  have hlambda : 0 < lambda := by
    dsimp [lambda, dyadicSimpleCodegreeScale]
    exact Nat.mul_pos hA (pow_pos (by omega) _)
  have hK : 0 < K := by
    dsimp [K, dyadicSimpleEndpointBlockScale]
    positivity
  have hlossReal : (C : ℝ) + 1 ≤ iterationGamma * N := by
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hm20 : (1 : ℝ) ≤ (m : ℝ) ^ 20 := one_le_pow₀ hmR
    have hm10 : (m : ℝ) ≤ (m : ℝ) ^ 10 := by
      calc
        (m : ℝ) = (m : ℝ) ^ 1 := by ring
        _ ≤ (m : ℝ) ^ 10 := pow_le_pow_right₀ hmR (by omega)
    have hgrowth : (Ccoef : ℝ) + 1 ≤
        iterationGamma * (m : ℝ) ^ 10 :=
      hloss.trans (mul_le_mul_of_nonneg_left hm10 hiterationGamma0.le)
    dsimp [C, N, dyadicSimpleQuantizationScale]
    push_cast
    calc
      (Ccoef : ℝ) * (m : ℝ) ^ 20 + 1 ≤
          (Ccoef : ℝ) * (m : ℝ) ^ 20 + 1 * (m : ℝ) ^ 20 := by
        simpa [add_comm] using
          (add_le_add_left hm20 ((Ccoef : ℝ) * (m : ℝ) ^ 20))
      _ = ((Ccoef : ℝ) + 1) * (m : ℝ) ^ 20 := by ring
      _ ≤ (iterationGamma * (m : ℝ) ^ 10) * (m : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ = iterationGamma * (m : ℝ) ^ 30 := by ring
  have hCN : C ≤ N := by
    have hiterOne : iterationGamma ≤ 1 :=
      hiterationGammaHalf.trans (by norm_num)
    have hreal : (C : ℝ) ≤ N := by
      calc
        (C : ℝ) ≤ (C : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ iterationGamma * N := hlossReal
        _ ≤ 1 * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hiterOne (Nat.cast_nonneg N)
        _ = N := one_mul _
    exact_mod_cast hreal
  have hNC : 0 < N - C := by
    have hiterStrict : iterationGamma < 1 :=
      hiterationGammaHalf.trans_lt (by norm_num)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    apply Nat.sub_pos_of_lt
    exact_mod_cast (show (C : ℝ) < N by
      calc
        (C : ℝ) < (C : ℝ) + 1 := lt_add_one _
        _ ≤ iterationGamma * N := hlossReal
        _ < 1 * (N : ℝ) := mul_lt_mul_of_pos_right hiterStrict hN0
        _ = N := one_mul _)
  have hordinaryRateBound :
      jointProfileColorDependentRate tau + tau ^ 2 / 4 ≤
        1 - 4 * iterationGamma := by
    have hrate := jointProfileColorDependentRate_add_quarter_square_le htau0 htau1
    calc
      jointProfileColorDependentRate tau + tau ^ 2 / 4 ≤ 1 - tau / 2 := hrate
      _ = 1 - 4 * iterationGamma := by
        dsimp [iterationGamma]
        ring
  have hslotCaps := boundedMultiplicityDyadic_initial_slot_caps
    hiterationGamma0.le hiterationGammaHalf hCN hlossReal hordinaryRateBound
  have hordinarySlotCap : (N : ℝ) *
      (jointProfileColorDependentRate tau + tau ^ 2 / 4) ≤ S0 := by
    simpa [S0, d0] using hslotCaps.1
  have hextraSlotCap : (1 - extraGamma) * N ≤ S0 := by
    rw [hextraEq]
    simpa [S0, d0] using hslotCaps.2.1
  have hgapInitial : (S0 : ℝ) ≤ (1 - iterationGamma) * d0 := by
    dsimp [S0, d0]
    rw [Nat.cast_sub hCN]
    exact hslotCaps.2.2
  have hsupportE :
      2 * (((n : ℝ) / beta / (1 - extraGamma)) + 1 + reserve) ≤ E := by
    simpa [E, reserve, Ecoef] using
      (boundedMultiplicityDyadic_support_budget (show 1 ≤ m by omega) hbeta0
        (hextraGammaHalf.trans_lt (by norm_num)) hnUpper)
  have hchoiceCap : B * k * placeCount * placeCount + E ≤ C := by
    have hpaletteEnvelope : B * k ≤ 4 * (2 ^ 20 * m ^ 20) :=
      hpalette.trans (Nat.mul_le_mul_left 4 hnUpper)
    dsimp [C, Ccoef, E, Ecoef, boundedMultiplicityDyadicChoiceCoefficient]
    calc
      B * k * placeCount * placeCount +
          boundedMultiplicityDyadicSupportCoefficient beta extraGamma * m ^ 20 ≤
        (4 * (2 ^ 20 * m ^ 20)) * placeCount * placeCount +
          4 * boundedMultiplicityDyadicSupportCoefficient beta extraGamma * m ^ 20 := by
            gcongr
            omega
      _ = (4 * (2 ^ 20 * placeCount ^ 2 +
          boundedMultiplicityDyadicSupportCoefficient beta extraGamma)) * m ^ 20 := by
        ring
  have hordinaryJobCodegree : (N : ℝ) * (2 * scale / n) ≤ lambda := by
    simpa [N, lambda, A] using boundedMultiplicityDyadic_ordinaryJobCodegree_fixed
      (mult := mult) (m := m) (palette := n) (placeCount := 2)
      (show 1 ≤ m by omega) hscale0.le hnLower
  have hextraCodegree : (N : ℝ) / reserve ≤ lambda := by
    simpa [N, reserve, lambda] using
      boundedMultiplicityDyadic_extraCodegree_for_coefficient (show 1 ≤ m by omega)
        (show 1 ≤ A by omega)
  have hextraPairCodegree : (mult : ℝ) * (N : ℝ) / reserve ≤ lambda := by
    simpa [N, reserve, lambda, A] using
      boundedMultiplicityDyadic_extraPairCodegree_fixed
        (mult := mult) (m := m) (placeCount := 2) (scale := scale)
        (show 1 ≤ m by omega)
  have hordinaryPair : 2 * scale / (n : ℝ) ≤ 1 / (reserve : ℝ) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hreserveR : (0 : ℝ) < reserve := by exact_mod_cast hreserve
    rw [div_le_div_iff₀ hnR hreserveR]
    simp only [one_mul]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hresCast : (reserve : ℝ) = (m : ℝ) ^ 16 := by
      simp [reserve, dyadicSimpleReserveScale]
    have hnCast : (m : ℝ) ^ 20 ≤ n := by exact_mod_cast hnLower
    rw [hresCast]
    calc
      2 * scale * (m : ℝ) ^ 16 ≤
          2 * (m : ℝ) * (m : ℝ) ^ 16 := by gcongr
      _ = 2 * (m : ℝ) ^ 17 := by ring
      _ ≤ (m : ℝ) ^ 20 := by
        have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
        have hm3 : (2 : ℝ) ≤ (m : ℝ) ^ 3 := by
          exact hm2.trans (by
            simpa using (pow_le_pow_right₀ hmR (show 1 ≤ 3 by omega)))
        calc
          2 * (m : ℝ) ^ 17 ≤ (m : ℝ) ^ 3 * (m : ℝ) ^ 17 :=
            mul_le_mul_of_nonneg_right hm3 (by positivity)
          _ = (m : ℝ) ^ 20 := by ring
      _ ≤ n := hnCast
  let baseScale := colorDependentCandidateCapacityScale rho s omega beta q r C0
  have hbaseScale0 : 0 < baseScale := by
    exact colorDependentCandidateCapacityScale_pos
      (β := beta) (q := q) (r := r) hrho hspos hC0 homega0
  have hbaseScale_le : baseScale ≤ scale := by
    dsimp [baseScale, scale]
    calc
      colorDependentCandidateCapacityScale rho s omega beta q r C0 =
          1 * colorDependentCandidateCapacityScale rho s omega beta q r C0 := by ring
      _ ≤ (mult : ℝ) * colorDependentCandidateCapacityScale rho s omega beta q r C0 := by
        gcongr
        exact_mod_cast (show 1 ≤ mult by omega)
  have hordinaryJobCodegreeBase :
      (N : ℝ) * (2 * baseScale / n) ≤ lambda := by
    apply (show (N : ℝ) * (2 * baseScale / n) ≤
        (N : ℝ) * (2 * scale / n) by
      gcongr).trans
    exact hordinaryJobCodegree
  have hordinaryPairBase :
      2 * baseScale / (n : ℝ) ≤ 1 / (reserve : ℝ) := by
    apply (show 2 * baseScale / (n : ℝ) ≤ 2 * scale / (n : ℝ) by
      gcongr).trans
    exact hordinaryPair
  have hret0 : 0 ≤ fixedSlackJobRetention
      (variableSlackA alpha iterationGamma lambda) iterationGamma -
        variableSlackEta alpha iterationGamma lambda :=
    (variableSlack_jobRetention_pos halpha hiterationGamma0
      hiterationGammaHalf hlambda halphaOne).le
  have hretHalf : 1 / 2 ≤ fixedSlackJobRetention
      (variableSlackA alpha iterationGamma lambda) iterationGamma -
        variableSlackEta alpha iterationGamma lambda :=
    variableSlack_half_le_jobRetention halpha.le halphaSixth
      hiterationGamma0.le (hiterationGammaHalf.trans (by norm_num)) hlambda
  have hret1 : fixedSlackJobRetention
      (variableSlackA alpha iterationGamma lambda) iterationGamma -
        variableSlackEta alpha iterationGamma lambda ≤ 1 :=
    variableSlack_jobRetention_le_one halpha.le hiterationGamma0.le
      (hiterationGammaHalf.trans (by norm_num)) hlambda
  have hstepsCast : (steps : ℝ) ≤ T * lambda := by
    simpa [steps, T] using variableSlackSteps_cast_le halpha hiterationGamma0
      htraceEps0 htraceEps1 hlambda
  have hdecay :
      (1 - (fixedSlackJobRetention
          (variableSlackA alpha iterationGamma lambda) iterationGamma -
        variableSlackEta alpha iterationGamma lambda)) * steps ≤ decayBudget := by
    simpa [decayBudget, T] using variableSlack_jobDecay_mul_steps_le
      halpha.le hiterationGamma0.le
      (hiterationGammaHalf.trans (by norm_num)) hlambda hstepsCast
  have hfloorSteps : (steps : ℝ) ≤
      Real.exp (-2 * decayBudget) * (1 / 2 : ℝ) * N / 2 := by
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hlambdaCast : (lambda : ℝ) = (A : ℝ) * (m : ℝ) ^ 14 := by
      simp [lambda, dyadicSimpleCodegreeScale]
    have hm16 : (m : ℝ) ≤ (m : ℝ) ^ 16 := by
      calc
        (m : ℝ) = (m : ℝ) ^ 1 := by ring
        _ ≤ (m : ℝ) ^ 16 := pow_le_pow_right₀ hmR (by omega)
    have hTA : T * A ≤ Real.exp (-2 * decayBudget) / 4 * (m : ℝ) ^ 16 :=
      hfloorGrowth.trans (mul_le_mul_of_nonneg_left
        hm16 (by positivity))
    calc
      (steps : ℝ) ≤ T * lambda := hstepsCast
      _ = (T * A) * (m : ℝ) ^ 14 := by rw [hlambdaCast]; ring
      _ ≤ (Real.exp (-2 * decayBudget) / 4 * (m : ℝ) ^ 16) *
          (m : ℝ) ^ 14 := by gcongr
      _ = Real.exp (-2 * decayBudget) * (1 / 2 : ℝ) * N / 2 := by
        simp [N, dyadicSimpleQuantizationScale]
        ring
  have hd0Half : (1 / 2 : ℝ) * N ≤ d0 := by
    have hCHalf : (C : ℝ) ≤ (1 / 2 : ℝ) * N := by
      calc
        (C : ℝ) ≤ (C : ℝ) + 1 := le_add_of_nonneg_right zero_le_one
        _ ≤ iterationGamma * N := hlossReal
        _ ≤ (1 / 2 : ℝ) * N :=
          mul_le_mul_of_nonneg_right hiterationGammaHalf (Nat.cast_nonneg N)
    dsimp [d0]
    rw [Nat.cast_sub hCN]
    apply (le_sub_iff_add_le).2
    calc
      (1 / 2 : ℝ) * N + C ≤
          (1 / 2 : ℝ) * N + (1 / 2 : ℝ) * N :=
        by
          simpa [add_comm] using
            (add_le_add_left hCHalf ((1 / 2 : ℝ) * N))
      _ = N := by ring
  have hdegreeFraction : ∀ t ≤ steps,
      cfrac * N ≤
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) t := by
    have hfrac :=
      RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale_uniform_fraction
        d0 N steps
          (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) (1 / 2) decayBudget
          hret0 hretHalf hret1 (by norm_num) hd0Half hdecay hfloorSteps
    intro t ht
    have h := hfrac t ht
    dsimp [cfrac]
    convert h using 1; ring
  have hdegreeUpper : ∀ t,
      RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) t ≤ (m + 1) ^ 30 := by
    intro t
    exact (RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale_le_initial
      d0 t
        (variableSlackA alpha iterationGamma lambda) iterationGamma
        (variableSlackEta alpha iterationGamma lambda) hret0 hret1).trans
      ((Nat.sub_le N C).trans (Nat.pow_le_pow_left (Nat.le_succ m) 30))
  have hroundScales : ∀ t < steps,
      DyadicSimpleClosedRoundScales 1 m
        (RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) t)
        lambda alpha iterationGamma delta := by
    intro t ht
    apply hclosed
    · have hd := hdegreeFraction t (Nat.le_of_lt ht)
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
      exact_mod_cast (mul_pos hcfrac hN0).trans_le hd
    · exact hlambda
    · exact hdegreeFraction t (Nat.le_of_lt ht)
    · exact hdegreeUpper t
    · exact le_rfl
  have hmarginDegree : ∀ t < steps,
      4 * (1 - iterationGamma) ≤
        variableSlackA alpha iterationGamma lambda * iterationGamma *
          RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
            d0 (variableSlackA alpha iterationGamma lambda) iterationGamma
            (variableSlackEta alpha iterationGamma lambda) t := by
    intro t ht
    let d := RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
      d0 (variableSlackA alpha iterationGamma lambda) iterationGamma
      (variableSlackEta alpha iterationGamma lambda) t
    have hd := hdegreeFraction t (Nat.le_of_lt ht)
    have hlambdaCast : (lambda : ℝ) = (A : ℝ) * (m : ℝ) ^ 14 := by
      simp [lambda, dyadicSimpleCodegreeScale]
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hgrowth : 4 * (1 - iterationGamma) * (lambda : ℝ) ≤
        alpha * iterationGamma ^ 2 * (cfrac * N) := by
      rw [hlambdaCast]
      calc
        4 * (1 - iterationGamma) * ((A : ℝ) * (m : ℝ) ^ 14) =
            (4 * (1 - iterationGamma) * A) * (m : ℝ) ^ 14 := by ring
        _ ≤ (alpha * iterationGamma ^ 2 * cfrac * m) *
            (m : ℝ) ^ 14 := by gcongr
        _ = alpha * iterationGamma ^ 2 * cfrac * (m : ℝ) ^ 15 := by ring
        _ ≤ alpha * iterationGamma ^ 2 * cfrac * (m : ℝ) ^ 30 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hmR (by omega : 15 ≤ 30)) (by positivity)
        _ = alpha * iterationGamma ^ 2 * (cfrac * N) := by
          simp [N, dyadicSimpleQuantizationScale]
          ring
    have hright := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ alpha * iterationGamma ^ 2 by positivity)
    change 4 * (1 - iterationGamma) ≤
      variableSlackA alpha iterationGamma lambda * iterationGamma * (d : ℝ)
    unfold variableSlackA
    rw [show (alpha * iterationGamma / (lambda : ℝ)) * iterationGamma *
        (d : ℝ) = (alpha * iterationGamma ^ 2 * d) / lambda by ring]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < lambda)).2
      (hgrowth.trans hright)
  have hmargin : ∀ t < steps, 1 - iterationGamma ≤
      (variableSlackA alpha iterationGamma lambda * iterationGamma *
          (1 - iterationGamma) -
        ((1 - iterationGamma) * variableSlackEta alpha iterationGamma lambda +
          3 * variableSlackEta alpha iterationGamma lambda)) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) t := by
    intro t ht
    exact variableSlack_iterationMargin_of_degree halpha.le
      hiterationGamma0.le hiterationGammaHalf hlambda (hmarginDegree t ht)
  have hnextPositive : ∀ t < steps,
      0 < (fixedSlackJobRetention
          (variableSlackA alpha iterationGamma lambda) iterationGamma -
        variableSlackEta alpha iterationGamma lambda) *
        RankThreeOptionSystem.OriginalIterationState.naturalSharpJobScale
          d0 (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda) t := by
    intro t ht
    exact mul_pos (lt_of_lt_of_le (by norm_num) hretHalf)
      (by exact_mod_cast (hroundScales t ht).degree_five.trans' (by omega))
  have htheta1 :
      (1 - delta) * variableSlackA alpha iterationGamma lambda / 8 ≤ 1 := by
    have haLe : variableSlackA alpha iterationGamma lambda ≤ alpha := by
      unfold variableSlackA
      have hlambdaOne : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2
      exact (mul_le_mul_of_nonneg_left
        (hiterationGammaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
          halpha.le).trans (mul_le_mul_of_nonneg_left hlambdaOne halpha.le)
    dsimp [delta]
    calc
      (1 - (1 / 2 : ℝ)) *
          variableSlackA alpha iterationGamma lambda / 8 ≤
          (1 - (1 / 2 : ℝ)) * alpha / 8 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left haLe (by norm_num)) (by norm_num)
      _ ≤ 1 := by norm_num [alpha, retainedNibbleAlpha]
  have haSmall : variableSlackA alpha iterationGamma lambda ≤ delta / 96 := by
    have haLe : variableSlackA alpha iterationGamma lambda ≤ alpha := by
      unfold variableSlackA
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < lambda)).2
      have hlambdaOne : (1 : ℝ) ≤ lambda := by exact_mod_cast hlambda
      exact (mul_le_mul_of_nonneg_left
        (hiterationGammaHalf.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
          halpha.le).trans (mul_le_mul_of_nonneg_left hlambdaOne halpha.le)
    norm_num [delta, alpha, retainedNibbleAlpha] at haLe ⊢
    linarith
  have hslotRate0 : 0 ≤ fixedSlackSlotRetention
      (variableSlackA alpha iterationGamma lambda) iterationGamma *
        (1 - iterationGamma) +
      3 * variableSlackEta alpha iterationGamma lambda := by
    have h := variableSlack_slotRetention_pos halpha hiterationGamma0
      hiterationGammaHalf hlambda halphaOne
    calc
      0 ≤ fixedSlackSlotRetention
          (variableSlackA alpha iterationGamma lambda) iterationGamma *
            (1 - iterationGamma) +
          2 * variableSlackEta alpha iterationGamma lambda +
          variableSlackEta alpha iterationGamma lambda := h.le
      _ = _ := by ring
  have htraceGeom :
      (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^
          steps ≤ traceEps := by
    simpa [delta, steps] using variableSlack_geometric_pow_steps_le
      halpha halphaOne hiterationGamma0
      (hiterationGammaHalf.trans (by norm_num)) htraceEps0 htraceEps1 hlambda
  have hboundaryN : (((L + 1) * (K - 1) : ℕ) : ℝ) ≤ traceEps * n := by
    have hnat : (L + 1) * (K - 1) ≤
        dyadicSimpleEndpointBlockScale (L + 1) m := by
      dsimp [K, dyadicSimpleEndpointBlockScale]
      simp only [one_mul]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hnatReal : (((L + 1) * (K - 1) : ℕ) : ℝ) ≤
        dyadicSimpleEndpointBlockScale (L + 1) m := by
      exact_mod_cast hnat
    have hnLowerReal : (dyadicSimplePaletteScale m : ℝ) ≤ n := by
      simpa [dyadicSimplePaletteScale] using
        (show ((m ^ 20 : ℕ) : ℝ) ≤ (n : ℝ) by exact_mod_cast hnLower)
    exact hnatReal.trans (hboundary.trans
      (mul_le_mul_of_nonneg_left hnLowerReal htraceEps0.le))
  have hreserveSmall : (reserve : ℝ) ≤ reserveEps * n := by
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    rw [show (reserve : ℝ) = (m : ℝ) ^ 16 by
      simp [reserve, dyadicSimpleReserveScale]]
    calc
      (m : ℝ) ^ 16 ≤ (reserveEps * m) * (m : ℝ) ^ 16 := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hreserveGrowth
            (show 0 ≤ (m : ℝ) ^ 16 by positivity))
      _ = reserveEps * (m : ℝ) ^ 17 := by ring
      _ ≤ reserveEps * (m : ℝ) ^ 20 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hmR (by omega : 17 ≤ 20)) hreserveEps0.le
      _ ≤ reserveEps * n :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hnLower) hreserveEps0.le
  have honeSmall : (1 : ℝ) ≤ reserveEps * n := by
    have hm20Nat : m ≤ m ^ 20 := by
      simpa using
        (show m ^ 1 ≤ m ^ 20 from
          Nat.pow_le_pow_right (by omega) (by omega))
    have hmnReal : (m : ℝ) ≤ n := by
      exact_mod_cast hm20Nat.trans hnLower
    exact hreserveGrowth.trans (mul_le_mul_of_nonneg_left
      hmnReal hreserveEps0.le)
  intro hβ hr R selected hcapacity hdev hresidual
  let proposal := G.retainedCoreProductProposal x
  let D := FinitePartialResamplingNumerics.packingDeviation n
    (colorDependentBlockCombinedColumnBound n k beta q r)
  have hproposal0 : ∀ e c, 0 ≤ proposal e c := by
    intro e c
    exact (hx e (finProdFinEquiv c)).1
  have hproposal : ∀ e c, proposal e c ≤ C0 / n := by
    intro e c
    exact (hx e (finProdFinEquiv c)).2
  have hrow := G.selectedLargeCapacityRow_lt_common hmultPos proposal R
    hs hq hr0 hleft homega0 homegaLt hspos hrhopos hC0
    selected hcapacity
  have hordinaryRate : rho / (1 - omega) + scale / n * D ≤
      jointProfileColorDependentRate tau + tau ^ 2 / 4 := by
    simpa [rho, omega, scale, D, jointProfileColorDependentRate] using
      add_le_add_left hdev (rho / (1 - omega))
  let residualBudget : ℝ :=
    (gamma + 4 * tau + (eta - gamma) / 1024) * n
  let largeLoss : ℝ := (eta - gamma) / 4 * n
  have hresidualBudget0 : 0 ≤ residualBudget := by
    dsimp [residualBudget]
    positivity
  have htraceSmall :
      traceEps * n + traceEps * n + 8 * (1 + (reserve : ℝ)) ≤
        (eta - gamma) / 64 * n := by
    dsimp [traceEps, reserveEps] at hreserveSmall honeSmall ⊢
    linarith only [hreserveSmall, honeSmall]
  have hlargeScalar := retainedCoreTau_largeCapture_with_trace_le
    (C0 := C0) hgamma0.le hgammaEta (le_rfl :
      (eta - gamma) / 64 ≤ (eta - gamma) / 64)
  have hlargeBudget :
          (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^
            steps * n +
          (((L + 1) * (K - 1) : ℕ) : ℝ) +
          8 * residualBudget +
          8 * (1 + (reserve : ℝ)) ≤ largeLoss := by
    have hgeom := mul_le_mul_of_nonneg_right htraceGeom
      (Nat.cast_nonneg n)
    have htrace :
        (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^
              steps * n +
            (((L + 1) * (K - 1) : ℕ) : ℝ) +
            8 * (1 + (reserve : ℝ)) ≤
          (eta - gamma) / 64 * n := by
      simpa [add_assoc] using
        ((add_le_add_left (add_le_add hgeom hboundaryN)
          (8 * (1 + (reserve : ℝ)))).trans htraceSmall)
    have hscalarMul := mul_le_mul_of_nonneg_right hlargeScalar
      (Nat.cast_nonneg n)
    calc
      (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^
              steps * n +
            (((L + 1) * (K - 1) : ℕ) : ℝ) +
            8 * residualBudget +
            8 * (1 + (reserve : ℝ)) =
          ((1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^
              steps * n +
            (((L + 1) * (K - 1) : ℕ) : ℝ) +
            8 * (1 + (reserve : ℝ))) + 8 * residualBudget := by ring
      _ ≤ (eta - gamma) / 64 * n + 8 * residualBudget :=
        add_le_add_left htrace (8 * residualBudget)
      _ = ((eta - gamma) / 64 +
          8 * (gamma + 4 * tau + (eta - gamma) / 1024)) * n := by
        dsimp [residualBudget]
        ring
      _ ≤ largeLoss := by
        simpa [largeLoss] using hscalarMul
  exact G.exists_colorDependentLargeMatchingData_of_closedIteration
    proposal R hmult hn hs hq hr0 hN hleft homega0 homega1 hrhopos.le hscale0
    hC0.le hproposal0 hproposal selected hstar hrow hordinaryRate
    hordinarySlotCap hreserve hextraGamma0
    (hextraGammaHalf.trans_lt (by norm_num)) hextraGammaHalf hextraSlotCap
    (by simpa [baseScale] using hordinaryJobCodegreeBase)
    (by simpa [baseScale] using hordinaryPairBase)
    hextraCodegree hextraPairCodegree
    hCN hsupportE hchoiceCap
    hdyadicCover halpha halphaSmall hiterationGamma0 hiterationGammaHalf
    hdelta0 hdelta1 hK hlambda htheta1 hret0 hslotRate0 hgapInitial hmargin
    (fun t ht ↦ (hroundScales t ht).degree_five) hnextPositive
    (fun t ht ↦ (hroundScales t ht).endpointBlock_le_degree)
    (fun t ht ↦ (hroundScales t ht).localScale)
    (fun t ht ↦ (hroundScales t ht).groupScale)
    (fun t ht ↦ (hroundScales t ht).slotScale)
    (fun t ht ↦ (hroundScales t ht).jobScale)
    (fun t ht ↦ (hroundScales t ht).blockScale)
    haSmall (fun t ht ↦ (hroundScales t ht).squareScale)
    hB (lt_of_lt_of_le (by norm_num) hk4) hNC hdyadicTop
    hresidual hresidualBudget0 hlargeBudget

end WeightedMultigraph

end

end WeightedEdgeColoring
