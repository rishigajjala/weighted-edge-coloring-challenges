import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileLargeInitialBounds
import WeightedEdgeColoring.BoundedMultiplicityOriginalTypeIsolatedClosedIteration

/-!
# Closed endpoint iteration for color-dependent selected profiles

All combinatorial hypotheses of the rank-three iteration are discharged by
the concrete selected-option estimates.  The remaining assumptions are
explicit scalar inequalities, so this theorem can be fed by an eventual
parameter constructor without any graph-dependent interface.
-/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

open RankThreeOptionSystem.OriginalIterationState
open RankThreeOptionSystem.OriginalIterationState.Multigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n N reserve C E S0 steps L K lambda mult : ℕ}
variable {s β q r proposalGamma extraGamma rho omega C0 scale deviation
    ordinaryRate alpha delta iterationGamma : ℝ}
variable {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

theorem exists_colorDependentSelectedDyadicClosedEndpointIteration
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
        variableSlackBeta0 alpha iterationGamma * d) :
    let Hbase := G.colorDependentSelectedDyadicSystem
      (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
      proposal R proposalGamma extraGamma rho omega selected
    letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
      inferInstance
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∃ final : RankThreeOptionSystem.OriginalIterationState Hlarge,
      RankThreeOptionSystem.OriginalIterationState.Multigraph.EndpointSharpTrace
        (G.largeEdgeRestriction β) β
        (variableSlackA alpha iterationGamma lambda) delta L K steps
        (RankThreeOptionSystem.OriginalIterationState.full Hlarge) final ∧
      (∀ j, (final.system.fiber j).Nonempty →
        naturalSharpJobScale (N - C)
            (variableSlackA alpha iterationGamma lambda) iterationGamma
            (variableSlackEta alpha iterationGamma lambda) steps ≤
          (final.system.fiber j).card) ∧
      (∀ slot, final.system.slotDegree slot ≤
        naturalSharpSlotCap S0 (N - C)
          (variableSlackA alpha iterationGamma lambda) iterationGamma
          (variableSlackEta alpha iterationGamma lambda)
          (2 * variableSlackEta alpha iterationGamma lambda)
          (variableSlackEta alpha iterationGamma lambda) steps) ∧
      ∀ v,
        RankThreeOptionSystem.OriginalIterationState.Multigraph.stateActiveStarWeight
          (G.largeEdgeRestriction β) final v ≤
          (1 - (1 - delta) * variableSlackA alpha iterationGamma lambda / 8) ^ steps *
              RankThreeOptionSystem.OriginalIterationState.Multigraph.stateActiveStarWeight
                (G.largeEdgeRestriction β)
                (RankThreeOptionSystem.OriginalIterationState.full Hlarge) v +
            (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  dsimp only
  let Hbase := G.colorDependentSelectedDyadicSystem
    (B := B) (k := k) (N := N) (reserve := reserve) (L := L)
    proposal R proposalGamma extraGamma rho omega selected
  letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem Hbase β
  classical
  let initial := RankThreeOptionSystem.OriginalIterationState.full Hlarge
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
  apply RankThreeOptionSystem.OriginalIterationState.Multigraph.exists_endpointVariableSlackClosedIteration
      (G.largeEdgeRestriction β) initial steps (N - C) S0 lambda L K
  · exact hβ
  · exact hdyadicCover
  · exact G.largeEdgeRestriction_weight_lower β
  · exact halpha
  · exact halphaSmall
  · exact hiterationGamma0
  · exact hiterationGammaHalf
  · exact hdelta0
  · exact hdelta1
  · exact hK
  · exact hlambda
  · exact htheta1
  · exact hjobRate0
  · exact hslotRate0
  · exact hgap0
  · exact hmargin
  · exact hpositive
  · exact hnextPositive
  · intro o
    exact G.colorDependentSelectedDyadicLarge_slots_card_eq_two proposal R selected o
  · intro j slot
    exact_mod_cast G.colorDependentSelectedDyadicLarge_jobSlotCodegree_le proposal R
      hn hs hq hr0 hleft homega0 homega1 hrho hC0 hproposal0 hproposal
      hreserve hordinaryJobCodegree hextraCodegree selected j slot
  · intro leftSlot rightSlot hne
    exact_mod_cast G.colorDependentSelectedDyadicLarge_slotPairCodegree_le proposal R
      hmult hn hs hq hr0 hleft homega0 homega1 hrho hC0 hproposal0 hproposal
      hreserve hordinaryPair hpairCodegree selected leftSlot rightSlot hne
  · intro j _hj
    change N - C ≤ (((RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.fiber j).card)
    have hfull :
        (((RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.fiber j).card) =
          (Hlarge.fiber j).card :=
      RankThreeOptionSystem.OriginalIterationState.Multigraph.full_system_fiber_card
        (G := G.largeEdgeRestriction β) (H := Hlarge) j
    rw [hfull]
    exact G.colorDependentSelectedDyadicLarge_jobDegree_lower proposal R
      hs hq hr0 hleft homega0 homega1 hrho selected hCN hchoices j
  · intro slot
    change (RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.slotDegree slot ≤ S0
    have hfull :
        (RankThreeOptionSystem.OriginalIterationState.full Hlarge).system.slotDegree slot =
          Hlarge.slotDegree slot :=
      RankThreeOptionSystem.OriginalIterationState.Multigraph.full_system_slotDegree
        (G := G.largeEdgeRestriction β) (H := Hlarge) slot
    rw [hfull]
    exact G.colorDependentSelectedDyadicLarge_slotDegree_le proposal R
      hn hN hs hq hr0 hleft homega0 homega1 hrho hscale selected hrow
      hordinaryRate hordinarySlotCap hreserve hextraGamma0 hextraGamma1
      hextraSlotCap slot
  · exact hKdegree
  · exact hscaleIteration
  · exact hgroupScale
  · exact hslotScale
  · exact hjobScale
  · exact hblock
  · exact haSmall
  · exact hsquare

end WeightedMultigraph

end

end WeightedEdgeColoring
