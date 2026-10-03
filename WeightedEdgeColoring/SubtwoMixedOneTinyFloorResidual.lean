import WeightedEdgeColoring.SubtwoOneTinyFloorRemainder
import WeightedEdgeColoring.SubtwoMixedGraphQuotientPairMultiplicity

/-! A coefficient-floor residual with bounded core types and at most one
exceptional tiny item per original endpoint pair. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

universe u
variable (G : WeightedMultigraph.{u})

private def oneTinyFloorBound (D S : ℕ) : ℕ :=
  (D + 1) * (((S + 1) ^ (D + 1) * S + S) + 1)

/-- This is the exact mixed per-bundle input. The left branch has no tiny
type; the right branch names its sole exceptional type. -/
def FloorBundleAtMostOneTiny (D S : ℕ) : Prop :=
  ∀ k : G.V × G.V,
    Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤ D + 1 ∧
      ((∀ x : G.EdgeSetWeightType (G.floorBundle k),
        Nat.floor (1 / x.1) ≤ S) ∨
       ∃ tiny : G.EdgeSetWeightType (G.floorBundle k),
         G.edgeSetWeightDemand (G.floorBundle k) tiny ≤ 1 ∧
         ∀ p : (G.edgeSetWeightBinPackingInstance (G.floorBundle k)).Pattern,
           ∀ x : G.EdgeSetWeightType (G.floorBundle k), x ≠ tiny →
             p.multiplicity x ≤ S)

private theorem oneTinyFloorBound_bundle
    (D S : ℕ) (h : G.FloorBundleAtMostOneTiny D S)
    (k : G.V × G.V) :
    (G.floorResidualEdges.filter fun e => e ∈ G.floorBundle k).card ≤
      oneTinyFloorBound D S := by
  obtain ⟨hcard, hcase⟩ := h k
  have hbase := G.card_floorResidual_bundle_le_sum k
  rcases hcase with hpure | ⟨tiny, hdemand, hcore⟩
  · have hcover := (G.floorBundleCover k).sum_floorResidualDemand_le_card_mul_succ_pow_card_mul S (by
        intro x
        simpa using hpure x)
    have hpow : (S + 1) ^
        Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤
        (S + 1) ^ (D + 1) :=
      Nat.pow_le_pow_right (by omega) hcard
    calc
      _ ≤ ∑ x : G.EdgeSetWeightType (G.floorBundle k),
            (G.floorBundleCover k).floorResidualDemand x := hbase
      _ ≤ Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) *
            ((S + 1) ^ Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) * S) :=
        hcover
      _ ≤ (D + 1) * ((S + 1) ^ (D + 1) * S) :=
        Nat.mul_le_mul hcard (Nat.mul_le_mul_right S hpow)
      _ ≤ oneTinyFloorBound D S := by
        unfold oneTinyFloorBound
        exact Nat.mul_le_mul_left (D + 1) (by omega)
  · have hcover := (G.floorBundleCover k).sum_floorResidualDemand_le_oneTiny
      tiny D S hcard hcore hdemand
    exact hbase.trans hcover

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Uniform bounded multiplicity of the actual floor residual after
contracting five-vertex blocks. -/
theorem floorResidualQuotient_pairMultiplicityAtMost_of_oneTiny
    (D S : ℕ) (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    (h : G.FloorBundleAtMostOneTiny D S) :
    ((G.edgeRestriction G.floorResidualEdges).subtwoQuotient block).PairMultiplicityAtMost
      (25 * oneTinyFloorBound D S) := by
  have hmult := G.floorResidualGraph_pairMultiplicityAtMost_of_bundleBound
    (oneTinyFloorBound D S) (G.oneTinyFloorBound_bundle D S h)
  exact G.edgeRestriction_subtwoQuotient_pairMultiplicityAtMost_five
    G.floorResidualEdges block hfiber hmult

end
end WeightedEdgeColoring.WeightedMultigraph
