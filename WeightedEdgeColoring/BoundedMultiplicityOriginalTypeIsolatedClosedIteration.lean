import WeightedEdgeColoring.BoundedMultiplicityOriginalTypeIsolatedClosedStep

/-!
# Endpoint iteration with the corrected isolated scalar package

This theorem removes the event-weight, collision-moment, and Harris-product
hypotheses from the older variable-slack iterator.  Every round uses the
canonical corrected choices `isolatedVariableZ d` and
`isolatedVariableMoment d`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace RankThreeOptionSystem

open SharpFixedSlackNumeric

universe u v w

variable (G : WeightedMultigraph.{u})
  {Slot : Type v} {Option : Type w}
  [Fintype Slot] [Fintype Option]
  [DecidableEq Slot] [DecidableEq Option]
  {H : RankThreeOptionSystem G.E Slot Option}

namespace OriginalIterationState

namespace Multigraph

theorem exists_endpointVariableSlackClosedIteration
    {beta alpha gamma delta : ℝ}
    (initial : OriginalIterationState H)
    (steps d0 S0 lambda L K : ℕ)
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
          (1 - gamma) + 3 * variableSlackEta alpha gamma lambda)
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * d0)
    (hmargin : ∀ n < steps, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) *
        naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
    (hpositive : ∀ n < steps,
      5 ≤ naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
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
    (hKdegree : ∀ n < steps, K ≤
      naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n)
    (hscale : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      1000 * ((lambda : ℝ) + 1) ≤ gamma * d)
    (hgroupScale : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      isolatedVariableZ d + 1 ≤
        delta ^ 2 * variableSlackA alpha gamma lambda * K / 64)
    (hslotScale : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      isolatedVariableZ d + 1 ≤
        variableSlackEta alpha gamma lambda ^ 2 * d /
          (96 * variableSlackA alpha gamma lambda * lambda))
    (hjobScale : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      isolatedVariableZ d + Real.log 2 ≤
        variableSlackEta alpha gamma lambda ^ 2 * d /
          (16 * variableSlackA alpha gamma lambda * lambda))
    (hblock : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      128 * (lambda : ℝ) * (isolatedVariableMoment d : ℝ) ^ 2 ≤
        delta * alpha * gamma * K)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hsquare : ∀ n < steps,
      let d := naturalSharpJobScale d0
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      (lambda : ℝ) ^ 2 * isolatedVariableMomentUpper d ^ 2 ≤
        variableSlackBeta0 alpha gamma * d) :
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
  have hslotRate0' : 0 ≤
      fixedSlackSlotRetention (variableSlackA alpha gamma lambda) gamma *
          (1 - gamma) +
        2 * variableSlackEta alpha gamma lambda +
        variableSlackEta alpha gamma lambda := by
    convert hslotRate0 using 1 <;> ring
  have hmargin' : ∀ n < steps, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          2 * variableSlackEta alpha gamma lambda +
          variableSlackEta alpha gamma lambda)) *
        naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n := by
    intro n hn
    convert hmargin n hn using 1 <;> ring
  apply exists_endpointNaturalIsolatedSharpIteration G initial
    steps d0 S0 lambda L K (variableSlackA alpha gamma lambda) gamma
    (variableSlackEta alpha gamma lambda)
    (2 * variableSlackEta alpha gamma lambda)
    (variableSlackEta alpha gamma lambda) delta
    hbeta hdyadicCover hweightLower hK hlambda hgamma0.le
    (hgammaHalf.trans (by norm_num)) hdelta1
    (variableSlackA_pos halpha hgamma0 hlambda).le htheta1
    hjobRate0 hslotRate0'
    (variableSlack_error_fits halpha hgamma0
      (hgammaHalf.trans (by norm_num)) hlambda)
    hgap0 hmargin' (fun n hn ↦ by
      have := hpositive n hn
      omega) hnextPositive htwo hjobSlot hslotPair
    hdegree0 hslot0
  intro n hn X Dg
  let d := naturalSharpJobScale d0 (variableSlackA alpha gamma lambda) gamma
    (variableSlackEta alpha gamma lambda) n
  let S := fixedSlackPaddedSlotTarget gamma d
  exact EndpointNaturalIsolatedSharpStepData.ofVariableSlackClosed G X Dg
    halpha halphaSmall hgamma0 hgammaHalf hdelta0 hdelta1
    (hpositive n hn)
    (fixedSlackPaddedSlotTarget_le gamma d hgamma0.le
      (hgammaHalf.trans (by norm_num)))
    hK (hKdegree n hn) hlambda rfl (hscale n hn)
    (hgroupScale n hn) (hslotScale n hn) (hjobScale n hn)
    (hblock n hn) haSmall (hsquare n hn)

end Multigraph

end OriginalIterationState
end RankThreeOptionSystem
end WeightedEdgeColoring
