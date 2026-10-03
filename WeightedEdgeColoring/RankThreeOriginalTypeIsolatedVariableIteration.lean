import WeightedEdgeColoring.RankThreeOriginalTypeIsolatedEndpointIteration

/-!
# Variable-slack endpoint iteration

This wrapper removes the remaining abstract step-data argument from the
endpoint iteration.  Each round is built directly by
`EndpointNaturalIsolatedSharpStepData.ofVariableSlack`; the hypotheses below
are the explicit scalar inequalities used by that constructor.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

open SharpFixedSlackNumeric

universe u v w

variable (G : WeightedSimpleGraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  {H : RankThreeOptionSystem G.E Slot Option}

namespace OriginalIterationState

theorem exists_endpointVariableSlackIsolatedIteration
    {beta alpha gamma delta : ℝ}
    (initial : OriginalIterationState H)
    (steps d0 S0 lambda L K : ℕ)
    (z : ℕ → ℝ) (moment : ℕ → ℕ)
    (hbeta : 0 < beta) (hdyadicCover : 1 ≤ dyadicScale beta L)
    (hweightLower : ∀ e, beta ≤ G.weight e)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hK : 0 < K) (hlambda : 0 < lambda)
    (htheta1 : (1 - delta) * variableSlackA alpha gamma lambda / 8 ≤ 1)
    (hjobRate0 : 0 ≤
      fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)
    (hslotRate0 : 0 ≤
      fixedSlackSlotRetention (variableSlackA alpha gamma lambda) gamma *
          (1 - gamma) +
        3 * variableSlackEta alpha gamma lambda)
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0)
    (hmargin : ∀ n, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) *
        naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
    (hpositive : ∀ n < steps,
      0 < naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n)
    (hnextPositive : ∀ n < steps,
      0 < (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
          variableSlackEta alpha gamma lambda) *
        naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
    (htwo : ∀ o, (H.slots o).card = 2)
    (hjobSlot : ∀ j s, H.jobSlotCodegree j s ≤ lambda)
    (hslotPair : ∀ s r, s ≠ r → H.slotPairCodegree s r ≤ lambda)
    (hdegree0 : ∀ j, (initial.system.fiber j).Nonempty →
      d0 ≤ (initial.system.fiber j).card)
    (hslot0 : ∀ s, initial.system.slotDegree s ≤ S0)
    (hmoment : ∀ n < steps, 0 < moment n)
    (hmomentEq : ∀ n < steps, moment n =
      sharpConcreteMomentOrder
        (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n))
    (hslotMean : ∀ n < steps,
      0 < variableSlackSlotMean alpha gamma
        (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hslotGap0 : ∀ n < steps,
      0 ≤ variableSlackSlotGap alpha gamma
        (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hslotGap2 : ∀ n < steps,
      variableSlackSlotGap alpha gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda ≤
        2 * variableSlackSlotMean alpha gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda)
    (hjobMean : ∀ n < steps,
      0 < variableSlackJobMean alpha gamma
        (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hjobGap0 : ∀ n < steps,
      0 ≤ variableSlackJobGap alpha gamma
        (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hjobGap2 : ∀ n < steps,
      variableSlackJobGap alpha gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda ≤
        2 * variableSlackJobMean alpha gamma
          (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda)
    (hrowHalf : ∀ n < steps, exponentialRowWeight (z n) ≤ 1 / 2)
    (hcollisionRow : ∀ n < steps,
      collisionWeight (moment n) ≤ exponentialRowWeight (z n))
    (hgroupRate : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      z n + 2 * exponentialRowWeight (z n) *
          (isolatedLowerNeighborBudget
            (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤
        -(((delta / 2) * (1 - delta / 2) +
            (Real.exp (-(delta / 2)) - 1)) *
          (variableSlackRho alpha gamma d lambda * (K * d : ℕ))))
    (hslotRate : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      let S := fixedSlackPaddedSlotTarget gamma d
      z n + 2 * exponentialRowWeight (z n) *
          (isolatedLowerNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤
        variableSlackSlotGap alpha gamma d S lambda ^ 2 /
          (4 * variableSlackSlotMean alpha gamma d S lambda))
    (hupperRate : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      let S := fixedSlackPaddedSlotTarget gamma d
      z n + Real.log 2 ≤
        variableSlackJobGap alpha gamma d S lambda ^ 2 /
          (4 * variableSlackJobMean alpha gamma d S lambda))
    (hupperProduct : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      exponentialRowWeight (z n) *
        (increasingNeighborBudget (upperSupportBudget d) 2 d : ℝ) ≤ 1 / 2)
    (hgroupLossProduct : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      exponentialRowWeight (z n) *
        (increasingNeighborBudget
          (isolatedConflictSupportBudget (groupSupportBudget (2 * K) d) d)
            2 d : ℝ) ≤ 1 / 2)
    (hslotLossProduct : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      exponentialRowWeight (z n) *
        (increasingNeighborBudget
          (isolatedConflictSupportBudget (slotSupportBudget d) d) 2 d : ℝ) ≤ 1 / 2)
    (hcollisionProduct : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      exponentialRowWeight (z n) *
        (increasingNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤ 1 / 2)
    (hblock : ∀ n < steps,
      128 * (lambda : ℝ) * (moment n : ℝ) ^ 2 ≤
        delta * alpha * gamma * K)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hsquare : ∀ n < steps,
      (lambda : ℝ) ^ 2 *
          sharpConcreteMomentUpper
            (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n) ^ 2 ≤
        variableSlackBeta0 alpha gamma *
          naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n) :
    ∃ final : OriginalIterationState H,
      EndpointSharpTrace G beta (variableSlackA alpha gamma lambda) delta
        L K steps initial final ∧
      (∀ j, (final.system.fiber j).Nonempty →
        naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) steps ≤
          (final.system.fiber j).card) ∧
      (∀ s, final.system.slotDegree s ≤
        naturalSharpSlotCap S0 d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda)
          (2 * variableSlackEta alpha gamma lambda)
      (variableSlackEta alpha gamma lambda) steps) ∧
      ∀ vtx,
        stateActiveStarWeight G final vtx ≤
          (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps *
              stateActiveStarWeight G initial vtx +
            (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  apply exists_endpointNaturalIsolatedSharpIteration G initial
    steps d0 S0 lambda L K (variableSlackA alpha gamma lambda) gamma
    (variableSlackEta alpha gamma lambda)
    (2 * variableSlackEta alpha gamma lambda)
    (variableSlackEta alpha gamma lambda) delta
    hbeta hdyadicCover hweightLower hK hlambda hgamma0.le
    (hgammaHalf.trans (by norm_num)) hdelta1
    (variableSlackA_pos halpha hgamma0 hlambda).le htheta1
    hjobRate0 (by convert hslotRate0 using 1 <;> ring)
    (variableSlack_error_fits halpha hgamma0
      (hgammaHalf.trans (by norm_num)) hlambda)
    hgap0 (fun n hn ↦ by convert hmargin n using 1 <;> ring)
    hpositive hnextPositive htwo hjobSlot hslotPair
    hdegree0 hslot0
  intro n hn X D
  exact EndpointNaturalIsolatedSharpStepData.ofVariableSlack G X D
    halpha halphaSmall hgamma0 hgammaHalf hdelta0 hdelta1
    (hpositive n hn)
    (fixedSlackPaddedSlotTarget_le gamma
      (naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n)
      hgamma0.le (hgammaHalf.trans (by norm_num)))
    hK hlambda (hmoment n hn) (hmomentEq n hn) rfl
    (hslotMean n hn) (hslotGap0 n hn) (hslotGap2 n hn)
    (hjobMean n hn) (hjobGap0 n hn) (hjobGap2 n hn)
    (hrowHalf n hn) (hcollisionRow n hn)
    (hgroupRate n hn) (hslotRate n hn) (hupperRate n hn)
    (hupperProduct n hn) (hgroupLossProduct n hn)
    (hslotLossProduct n hn) (hcollisionProduct n hn)
    (hblock n hn) haSmall (hsquare n hn)

end OriginalIterationState
end RankThreeOptionSystem
end WeightedEdgeColoring
