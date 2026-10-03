import WeightedEdgeColoring.SubtwoMixedGraphMaskedClosedIteration
import WeightedEdgeColoring.DyadicSimpleClosedIterationScales

/-!
# Scalar schedule bridge for the masked selected matching

The graph-dependent matching theorem uses the same corrected isolated-round
scale certificate as the existing large-edge construction. This bridge
packages those eight per-round inequalities without changing their meaning.
-/

namespace WeightedEdgeColoring

open RankThreeOptionSystem.OriginalIterationState

theorem mixedMaskedClosedScalars_of_dyadicRounds
    (β alpha gamma delta : ℝ)
    (N C S0 lambda L steps B m : ℕ)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hgamma0 : 0 < gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hK : 0 < dyadicSimpleEndpointBlockScale B m)
    (hlambda : 0 < lambda)
    (htheta1 : (1 - delta) * variableSlackA alpha gamma lambda / 8 ≤ 1)
    (hjobRate : 0 ≤ fixedSlackJobRetention
      (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)
    (hslotRate : 0 ≤ fixedSlackSlotRetention
      (variableSlackA alpha gamma lambda) gamma * (1 - gamma) +
        3 * variableSlackEta alpha gamma lambda)
    (hgap : (S0 : ℝ) ≤ (1 - gamma) * (N - C))
    (hmargin : ∀ t < steps, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) *
      naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) t)
    (hnextPositive : ∀ t < steps,
      0 < (fixedSlackJobRetention
          (variableSlackA alpha gamma lambda) gamma -
          variableSlackEta alpha gamma lambda) *
        naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) t)
    (haSmall : variableSlackA alpha gamma lambda ≤ delta / 96)
    (hround : ∀ t < steps,
      DyadicSimpleClosedRoundScales B m
        (naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) t)
        lambda alpha gamma delta) :
    MixedMaskedClosedScalars β alpha gamma delta N C S0 lambda L
      (dyadicSimpleEndpointBlockScale B m) steps :=
  { dyadicCover := hdyadicCover
    alphaPos := halpha
    alphaSmall := halphaSmall
    gammaPos := hgamma0
    gammaHalf := hgammaHalf
    deltaPos := hdelta0
    deltaOne := hdelta1
    KPos := hK
    lambdaPos := hlambda
    thetaOne := htheta1
    jobRate := hjobRate
    slotRate := hslotRate
    gap := hgap
    margin := hmargin
    positive := fun t ht ↦ (hround t ht).degree_five
    nextPositive := hnextPositive
    Kdegree := fun t ht ↦ (hround t ht).endpointBlock_le_degree
    scale := fun t ht ↦ (hround t ht).localScale
    groupScale := fun t ht ↦ (hround t ht).groupScale
    slotScale := fun t ht ↦ (hround t ht).slotScale
    jobScale := fun t ht ↦ (hround t ht).jobScale
    block := fun t ht ↦ (hround t ht).blockScale
    aSmall := haSmall
    square := fun t ht ↦ (hround t ht).squareScale }

end WeightedEdgeColoring
