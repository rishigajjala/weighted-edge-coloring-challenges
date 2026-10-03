import WeightedEdgeColoring.ExtendedProfileSelectedDyadicInitialBounds
import WeightedEdgeColoring.RankThreeOriginalTypeIsolatedVariableIteration

/-!
# Endpoint iteration for the selected local-dyadic option system

This theorem is the first full composition point.  It constructs the
canonical full state on the large-edge job restriction, discharges all
structural degree and codegree assumptions from the selected-profile dyadic
bounds, and invokes the variable-slack isolated iteration.  Only scalar
inequalities remain as hypotheses.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

open RankThreeOptionSystem
open RankThreeOptionSystem.OriginalIterationState
open SharpFixedSlackNumeric

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N reserve C S0 lambda steps L K : ℕ}
variable {s β q r gamma extraGamma alpha delta : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

theorem exists_selectedBlockDyadicEndpointIteration
    (hn : 0 < B * k) (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hN : 0 < N)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (D ordinaryRate : ℝ)
    (hcapacity : ∀ row : G.ExtendedProfileLargeRow
        (n := B * k) (β := β) (q := q) (r := r),
      G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl row) /
          extendedProfileCandidateCapacityScale rho s omega β q r <
        ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) + D)
    (hordinaryRate :
      rho / extendedProfileSmoothingKappa omega β q r +
          extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) * D ≤ ordinaryRate)
    (hordinarySlotCap : (N : ℝ) * ordinaryRate ≤ S0)
    (hreserve : 0 < reserve)
    (hextraGamma0 : 0 ≤ extraGamma) (hextraGamma1 : extraGamma < 1)
    (hgamma0 : 0 < gamma)
    (hgammaHalf : gamma ≤ 1 / 2)
    (hextraSlotCap : (1 - extraGamma) * N ≤ S0)
    (hordinaryJobCodegree : (N : ℝ) *
      ((explicitLargeSlotBound β q r : ℝ) *
        extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ)) ≤ lambda)
    (hordinaryPair :
      extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ) ≤ 1 / (reserve : ℝ))
    (hextraCodegree : (N : ℝ) / reserve ≤ lambda)
    (hCN : C ≤ N)
    (hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.graphDyadicExtraSlotCount bucket
            (G.selectedBlockLargeResidual R0 omega rho choice)
            extraGamma reserve) e ≤ C)
    (hdyadicCover : 1 ≤ dyadicScale β L)
    (halpha : 0 < alpha) (halphaSmall : alpha ≤ 1 / 100000)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hK : 0 < K) (hlambda : 0 < lambda)
    (z : ℕ → ℝ) (moment : ℕ → ℕ)
    (htheta1 : (1 - delta) * variableSlackA alpha gamma lambda / 8 ≤ 1)
    (hjobRate0 : 0 ≤
      fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
        variableSlackEta alpha gamma lambda)
    (hslotRate0 : 0 ≤
      fixedSlackSlotRetention (variableSlackA alpha gamma lambda) gamma *
          (1 - gamma) +
        3 * variableSlackEta alpha gamma lambda)
    (hgap0 : (S0 : ℝ) ≤ (1 - gamma) * (N - C))
    (hmargin : ∀ n, 1 - gamma ≤
      (variableSlackA alpha gamma lambda * gamma * (1 - gamma) -
        ((1 - gamma) * variableSlackEta alpha gamma lambda +
          3 * variableSlackEta alpha gamma lambda)) *
        naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
    (hpositive : ∀ n < steps,
      0 < naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n)
    (hnextPositive : ∀ n < steps,
      0 < (fixedSlackJobRetention (variableSlackA alpha gamma lambda) gamma -
          variableSlackEta alpha gamma lambda) *
        naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
    (hmoment : ∀ n < steps, 0 < moment n)
    (hmomentEq : ∀ n < steps, moment n =
      sharpConcreteMomentOrder
        (naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n))
    (hslotMean : ∀ n < steps,
      0 < variableSlackSlotMean alpha gamma
        (naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hslotGap0 : ∀ n < steps,
      0 ≤ variableSlackSlotGap alpha gamma
        (naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hslotGap2 : ∀ n < steps,
      variableSlackSlotGap alpha gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale (N - C)
              (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda ≤
        2 * variableSlackSlotMean alpha gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale (N - C)
              (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda)
    (hjobMean : ∀ n < steps,
      0 < variableSlackJobMean alpha gamma
        (naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hjobGap0 : ∀ n < steps,
      0 ≤ variableSlackJobGap alpha gamma
        (naturalSharpJobScale (N - C)
          (variableSlackA alpha gamma lambda) gamma
          (variableSlackEta alpha gamma lambda) n)
        (fixedSlackPaddedSlotTarget gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)) lambda)
    (hjobGap2 : ∀ n < steps,
      variableSlackJobGap alpha gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale (N - C)
              (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda ≤
        2 * variableSlackJobMean alpha gamma
          (naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n)
          (fixedSlackPaddedSlotTarget gamma
            (naturalSharpJobScale (N - C)
              (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n)) lambda)
    (hrowHalf : ∀ n < steps, exponentialRowWeight (z n) ≤ 1 / 2)
    (hcollisionRow : ∀ n < steps,
      collisionWeight (moment n) ≤ exponentialRowWeight (z n))
    (hgroupRate : ∀ n < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      z n + 2 * exponentialRowWeight (z n) *
          (isolatedLowerNeighborBudget
            (groupSupportBudget (2 * K) d) 2 d : ℝ) ≤
        -(((delta / 2) * (1 - delta / 2) +
            (Real.exp (-(delta / 2)) - 1)) *
          (variableSlackRho alpha gamma d lambda * (K * d : ℕ))))
    (hslotRate : ∀ n < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      let S := fixedSlackPaddedSlotTarget gamma d
      z n + 2 * exponentialRowWeight (z n) *
          (isolatedLowerNeighborBudget (slotSupportBudget d) 2 d : ℝ) ≤
        variableSlackSlotGap alpha gamma d S lambda ^ 2 /
          (4 * variableSlackSlotMean alpha gamma d S lambda))
    (hupperRate : ∀ n < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      let S := fixedSlackPaddedSlotTarget gamma d
      z n + Real.log 2 ≤
        variableSlackJobGap alpha gamma d S lambda ^ 2 /
          (4 * variableSlackJobMean alpha gamma d S lambda))
    (hupperProduct : ∀ n < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      exponentialRowWeight (z n) *
        (increasingNeighborBudget (upperSupportBudget d) 2 d : ℝ) ≤ 1 / 2)
    (hgroupLossProduct : ∀ n < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      exponentialRowWeight (z n) *
        (increasingNeighborBudget
          (isolatedConflictSupportBudget (groupSupportBudget (2 * K) d) d)
            2 d : ℝ) ≤ 1 / 2)
    (hslotLossProduct : ∀ n < steps,
      let d := naturalSharpJobScale (N - C)
        (variableSlackA alpha gamma lambda) gamma
        (variableSlackEta alpha gamma lambda) n
      exponentialRowWeight (z n) *
        (increasingNeighborBudget
          (isolatedConflictSupportBudget (slotSupportBudget d) d) 2 d : ℝ) ≤
            1 / 2)
    (hcollisionProduct : ∀ n < steps,
      let d := naturalSharpJobScale (N - C)
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
            (naturalSharpJobScale (N - C)
              (variableSlackA alpha gamma lambda) gamma
              (variableSlackEta alpha gamma lambda) n) ^ 2 ≤
        variableSlackBeta0 alpha gamma *
          naturalSharpJobScale (N - C)
            (variableSlackA alpha gamma lambda) gamma
            (variableSlackEta alpha gamma lambda) n) :
    let Hbase := G.selectedBlockDyadicQuantizedSystem
      (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice bucket
    letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
      inferInstance
    let Hlarge := G.largeEdgeJobSystem Hbase β
    ∃ final : RankThreeOptionSystem.OriginalIterationState Hlarge,
      RankThreeOptionSystem.OriginalIterationState.EndpointSharpTrace
        (G.largeEdgeRestriction β) β
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
      ∀ vtx,
        RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight
          (G.largeEdgeRestriction β) final vtx ≤
          (1 - (1 - delta) * variableSlackA alpha gamma lambda / 8) ^ steps *
              RankThreeOptionSystem.OriginalIterationState.stateActiveStarWeight
                (G.largeEdgeRestriction β)
                (RankThreeOptionSystem.OriginalIterationState.full Hlarge) vtx +
            (((L + 1) * (K - 1) : ℕ) : ℝ) := by
  classical
  dsimp only
  let Hbase := G.selectedBlockDyadicQuantizedSystem
    (N := N) (reserve := reserve) (gamma := extraGamma) R0 omega rho choice bucket
  letI : DecidableEq (Hbase.ActiveJobOption (G.largeEdgeJobs β)) :=
    inferInstance
  let Hlarge := G.largeEdgeJobSystem Hbase β
  let initial := RankThreeOptionSystem.OriginalIterationState.full Hlarge
  apply RankThreeOptionSystem.OriginalIterationState.exists_endpointVariableSlackIsolatedIteration
      (G.largeEdgeRestriction β) initial steps (N - C) S0 lambda L K z moment
  · exact hβ
  · exact hdyadicCover
  · exact G.largeEdgeRestriction_weight_lower β
  · exact halpha
  · exact halphaSmall
  · exact hgamma0
  · exact hgammaHalf
  · exact hdelta0
  · exact hdelta1
  · exact hK
  · exact hlambda
  · exact htheta1
  · exact hjobRate0
  · exact hslotRate0
  · rw [Nat.cast_sub hCN]
    exact hgap0
  · exact hmargin
  · exact hpositive
  · exact hnextPositive
  · intro o
    exact G.selectedBlockDyadicLarge_slots_card_eq_two (gamma := extraGamma) R0 omega rho choice
      bucket o
  · intro j slot
    exact G.selectedBlockDyadicLarge_jobSlotCodegree_le (gamma := extraGamma) R0
      hn hs hq hr0 hleft omega homega0 homega1 rho hrho.le choice bucket
      hreserve hordinaryJobCodegree hextraCodegree j slot
  · intro leftSlot rightSlot hne
    exact G.selectedBlockDyadicLarge_slotPairCodegree_le (gamma := extraGamma) R0
      hn hs hq hr0 hleft omega homega0 homega1 rho hrho.le choice bucket
      hreserve hordinaryPair hextraCodegree leftSlot rightSlot hne
  · intro j _hj
    change N - C ≤ (((full Hlarge).system.fiber j).card)
    have hfull : (((full Hlarge).system.fiber j).card) =
        (Hlarge.fiber j).card :=
      full_system_fiber_card (G := G.largeEdgeRestriction β)
        (H := Hlarge) j
    rw [hfull]
    exact G.selectedBlockDyadicLarge_jobDegree_lower (gamma := extraGamma) R0
      hn hs hq hr0 hleft omega homega0 homega1 rho hrho.le choice bucket
      hCN hchoices j
  · intro slot
    change (full Hlarge).system.slotDegree slot ≤ S0
    have hfull : (full Hlarge).system.slotDegree slot =
        Hlarge.slotDegree slot :=
      full_system_slotDegree (G := G.largeEdgeRestriction β)
        (H := Hlarge) slot
    rw [hfull]
    exact G.selectedBlockDyadicLarge_slotDegree_le (gamma := extraGamma) R0
      hn hs hspos hq hr0 hN hleft omega homega0 homega1 rho hrho choice
      bucket D ordinaryRate hcapacity hordinaryRate hordinarySlotCap hreserve
      hextraGamma0 hextraGamma1 hextraSlotCap slot
  · exact hmoment
  · exact hmomentEq
  · exact hslotMean
  · exact hslotGap0
  · exact hslotGap2
  · exact hjobMean
  · exact hjobGap0
  · exact hjobGap2
  · exact hrowHalf
  · exact hcollisionRow
  · exact hgroupRate
  · exact hslotRate
  · exact hupperRate
  · exact hupperProduct
  · exact hgroupLossProduct
  · exact hslotLossProduct
  · exact hcollisionProduct
  · exact hblock
  · exact haSmall
  · exact hsquare

end WeightedSimpleGraph

end

end WeightedEdgeColoring
