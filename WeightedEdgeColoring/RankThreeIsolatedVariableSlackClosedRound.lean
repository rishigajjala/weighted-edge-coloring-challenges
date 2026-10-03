import WeightedEdgeColoring.RankThreeIsolatedVariableSlackScalarClosure

/-!
# A numerically closed isolated variable-slack round

This wrapper uses the corrected inverse-eighth-power event weight and its
matching base-two moment.  Graph bookkeeping, collision tails, and Harris
products are all discharged.  The remaining rate assumptions are plain
scale inequalities with no exponential event terms hidden in them.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

open scoped BigOperators
open WeightedEdgeColoring
open WeightedEdgeColoring.SharpFixedSlackNumeric

universe u v w x

variable {Job : Type u} {Slot : Type v} {Option : Type w} {Group : Type x}
  [Fintype Job] [Fintype Slot] [Fintype Option] [Fintype Group]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option] [DecidableEq Group]
  (H : RankThreeOptionSystem Job Slot Option)

/-- One corrected isolated round.  In applications `S` is
`floor ((1-gamma)d)` and `K` is the endpoint-block width. -/
theorem exists_isolatedVariableSlackRound_closed
    (members : Group → Finset Job)
    (alpha gamma delta : ℝ) (lambda d S K : ℕ)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hd : 5 ≤ d) (hlambda : 0 < lambda) (hK : 0 < K) (hKd : K ≤ d)
    (hSgap : (S : ℝ) ≤ (1 - gamma) * d)
    (hSlower : (1 - gamma) * d - 1 ≤ (S : ℝ))
    (hscale : 1000 * ((lambda : ℝ) + 1) ≤ gamma * d)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjob : ∀ j, (H.fiber j).card = d)
    (hslot : ∀ s, H.slotDegree s = S)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s t, s ≠ t → H.slotPairCodegree s t ≤ lambda)
    (hmembers : ∀ g, (members g).card ≤ 2 * K)
    (hgroupSupportLower : ∀ g,
      K * d ≤ (linearRowSupport (H.jobGroupCoverageWeight members) g).card)
    (hgroupIncidence : ∀ j,
      ((Finset.univ : Finset Group).filter (fun g ↦ j ∈ members g)).card ≤ 2)
    (hgroupScale : isolatedVariableZ d + 1 ≤
        delta ^ 2 * variableSlackA alpha gamma lambda * K / 64)
    (hslotScale : isolatedVariableZ d + 1 ≤
        variableSlackEta alpha gamma lambda ^ 2 * d /
          (96 * variableSlackA alpha gamma lambda * lambda))
    (hjobScale : isolatedVariableZ d + Real.log 2 ≤
      variableSlackEta alpha gamma lambda ^ 2 * d /
        (16 * variableSlackA alpha gamma lambda * lambda))
    (hblock : 128 * (lambda : ℝ) *
        (isolatedVariableMoment d : ℝ) ^ 2 ≤
      delta * alpha * gamma * K)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hsquare : (lambda : ℝ) ^ 2 *
        isolatedVariableMomentUpper d ^ 2 ≤
      variableSlackBeta0 alpha gamma * d) :
    ∃ A : Finset Option,
      H.IsPartialMatching A ∧
      (∀ g, (1 - delta) * variableSlackRho alpha gamma d lambda * (K * d) <
        ∑ o ∈ A, H.jobGroupCoverageWeight members g o) ∧
      (∀ j, ¬ H.Covers A j →
        (WeightedEdgeColoring.fixedSlackJobRetention
            (variableSlackA alpha gamma lambda) gamma -
          variableSlackEta alpha gamma lambda) * d ≤
            H.residualJobDegree A j) ∧
      ∀ s, (∀ p ∈ A, s ∉ H.slots p) →
        (H.residualSlotDegree A s : ℝ) ≤
          (WeightedEdgeColoring.fixedSlackSlotRetention
              (variableSlackA alpha gamma lambda) gamma * (1 - gamma) +
            3 * variableSlackEta alpha gamma lambda) * d := by
  have hd0 : 0 < d := by omega
  have hd1 : 1 ≤ d := by omega
  have hSle : S ≤ d := by
    have hreal : (S : ℝ) ≤ d := by
      have : 0 ≤ gamma := hgamma0.le
      nlinarith
    exact_mod_cast hreal
  rcases variableSlack_padded_mean_and_gap_shape halpha hgamma0 hgammaHalf
      hlambda hSgap hSlower hscale with
    ⟨hslotMean, hslotGap2, hjobMean, hjobGap2⟩
  have hslotGap := variableSlackSlotGap_lower halpha hgamma0 hgammaHalf
    hd0 hlambda hSlower hscale
  have hjobGap := variableSlackJobGap_lower halpha hgamma0 hd0 hlambda hSgap
  rcases isolatedVariable_lower_corrections_le_one d K hd hKd with
    ⟨hgroupCorrection, hslotCorrection⟩
  have hslotGap0 : 0 ≤ variableSlackSlotGap alpha gamma d S lambda :=
    (div_nonneg
      (mul_nonneg (variableSlackEta_pos halpha hgamma0 hlambda).le
        (by positivity)) (by positivity)).trans hslotGap
  have hjobGap0 : 0 ≤ variableSlackJobGap alpha gamma d S lambda :=
    (div_nonneg
      (mul_nonneg (variableSlackEta_pos halpha hgamma0 hlambda).le
        (by positivity)) (by positivity)).trans hjobGap
  have hgroupRateToScale :
      isolatedVariableZ d + 2 * exponentialRowWeight (isolatedVariableZ d) *
          (isolatedLowerNeighborBudget
            (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤
        delta ^ 2 * variableSlackA alpha gamma lambda * K / 64 := by
    linarith [hgroupScale, hgroupCorrection]
  have hgroupRate :
      isolatedVariableZ d + 2 * exponentialRowWeight (isolatedVariableZ d) *
          (isolatedLowerNeighborBudget
            (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤
        -(((delta / 2) * (1 - delta / 2) +
            (Real.exp (-(delta / 2)) - 1)) *
          (variableSlackRho alpha gamma d lambda * (K * d : ℕ))) :=
    hgroupRateToScale.trans
      (variableSlack_groupRate_lower (m := K) halpha.le hgamma0.le
        hd0 hlambda hdelta0.le hdelta1)
  have hslotRate := (show
      isolatedVariableZ d + 2 * exponentialRowWeight (isolatedVariableZ d) *
          (isolatedLowerNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤
        variableSlackEta alpha gamma lambda ^ 2 * d /
          (96 * variableSlackA alpha gamma lambda * lambda) by
      linarith).trans
    (variableSlack_slotQuadraticRate_lower halpha hgamma0 hd0 hlambda hSle
      hslotMean hslotGap)
  have hupperRate := hjobScale.trans
    (variableSlack_jobQuadraticRate_lower halpha hgamma0 hd0 hlambda hSle
      hjobMean hjobGap)
  rcases isolatedVariable_all_product_bounds d K hd hKd with
    ⟨hupperProduct, hgroupLossProduct, hslotLossProduct,
      hcollisionProduct⟩
  have hgroupLoss := variableSlack_groupLossEnvelope_of_blockScale
    alpha gamma delta d lambda K (isolatedVariableMoment d) hd0 hlambda
      (isolatedVariableMoment_pos d hd0) halpha hgamma0 hdelta0 hdelta1
      haSmall hblock
  have hIsolation := variableSlack_isolationBudget_of_corrected_square_ratio
    alpha gamma (variableSlackBeta0 alpha gamma) d lambda hd0 hlambda
      halpha.le hgamma0.le (by unfold variableSlackBeta0; positivity)
      hsquare (variableSlack_fixed_isolation_budget halpha halphaSmall
        hgamma0 (hgammaHalf.trans (by norm_num)))
  have hround := H.exists_isolatedVariableSlackRound members alpha gamma delta
    (isolatedVariableZ d) lambda d S 2 (2 * K) (K * d)
    (isolatedVariableMoment d) halpha halphaSmall hgamma0 hgammaHalf
    hdelta0 hdelta1 hd0 hlambda (Nat.mul_pos hK hd0) hSgap htwo hjob
    hslot hjobSlot hslotPair hmembers hgroupSupportLower hgroupIncidence
    hslotMean hslotGap0 hslotGap2 hjobMean hjobGap0 hjobGap2
    (isolatedVariable_rowWeight_le_half d hd1)
    (isolatedVariable_collisionWeight_le d) hgroupRate hslotRate hupperRate
    hupperProduct hgroupLoss hgroupLossProduct hslotLossProduct
    hcollisionProduct hIsolation
  rcases hround with ⟨A, hmatching, hgroup, hjobResidual, hslotResidual⟩
  refine ⟨A, hmatching, ?_, hjobResidual, ?_⟩
  · simpa only [Nat.cast_mul] using hgroup
  · intro s hs
    have h := hslotResidual s hs
    convert h using 1 <;> ring

end WeightedEdgeColoring.RankThreeOptionSystem
