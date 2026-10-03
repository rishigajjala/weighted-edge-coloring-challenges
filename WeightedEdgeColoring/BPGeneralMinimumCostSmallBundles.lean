import WeightedEdgeColoring.BPGeneralFloorPacketization
import WeightedEdgeColoring.BoundedMultiplicityPairCodegree

/-!
# Small minimum-cost parallel bundles

The coefficient-floor construction chooses a minimum exact-demand cover in
every unordered parallel bundle.  This file records the threshold fact used
by the large/small bundle split.  If all physical weights are at least
`1 / S` and the minimum cover of a bundle has cost below `B`, then that
bundle has at most `S * ceil B` physical edges.  Consequently the union of
all below-threshold bundles has fixed endpoint-pair multiplicity.

This statement is independent of how the above-threshold bundles are
linear-grouped and packed.
-/

open scoped BigOperators Sym2

namespace WeightedEdgeColoring

noncomputable section

universe u

namespace BinPackingInstance.ExactDemandPatternCover

variable {B : BinPackingInstance.{u}} {demand : B.Item → ℕ}

/-- Total physical weight prescribed by an exact demand vector. -/
def exactDemandWeight (B : BinPackingInstance.{u})
    (demand : B.Item → ℕ) : ℝ :=
  ∑ i : B.Item, (demand i : ℝ) * B.weight i

/-- Capacity of every pattern implies that exact-demand weight is a lower
bound on the cost of every exact-demand cover. -/
theorem exactDemandWeight_le_cost
    (C : B.ExactDemandPatternCover demand) :
    exactDemandWeight B demand ≤ C.cost := by
  calc
    exactDemandWeight B demand =
        ∑ i : B.Item,
          (∑ p : B.Pattern,
            C.coeff p * (p.multiplicity i : ℝ)) * B.weight i := by
      unfold exactDemandWeight
      apply Finset.sum_congr rfl
      intro i _hi
      rw [C.sum_coeff_mul_multiplicity_eq i]
    _ = ∑ p : B.Pattern,
          C.coeff p *
            (∑ i : B.Item, (p.multiplicity i : ℝ) * B.weight i) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤ ∑ p : B.Pattern, C.coeff p * 1 := by
      apply Finset.sum_le_sum
      intro p _hp
      exact mul_le_mul_of_nonneg_left p.capacity (C.coeff_nonneg p)
    _ = C.cost := by
      simpa using C.sum_coeff_eq_cost

end BinPackingInstance.ExactDemandPatternCover

namespace WeightedMultigraph

variable (G : WeightedMultigraph.{u})

/-- The exact-demand weight of a physical edge set is the sum of its
physical edge weights. -/
theorem edgeSet_exactDemandWeight_eq_sum (F : Finset G.E) :
    BinPackingInstance.ExactDemandPatternCover.exactDemandWeight
        (G.edgeSetWeightBinPackingInstance F) (G.edgeSetWeightDemand F) =
      ∑ e ∈ F, G.weight e := by
  classical
  unfold BinPackingInstance.ExactDemandPatternCover.exactDemandWeight
  calc
    (∑ x : G.EdgeSetWeightType F,
        (G.edgeSetWeightDemand F x : ℝ) *
          (G.edgeSetWeightBinPackingInstance F).weight x) =
        ∑ x : G.EdgeSetWeightType F,
          ∑ e ∈ F, if G.weight e = x.1 then G.weight e else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [edgeSetWeightBinPackingInstance_weight, edgeSetWeightDemand]
      calc
        (((F.filter fun e ↦ G.weight e = x.1).card : ℕ) : ℝ) * x.1 =
            ∑ _e ∈ F.filter (fun e ↦ G.weight e = x.1), x.1 := by
          simp
        _ = ∑ e ∈ F.filter (fun e ↦ G.weight e = x.1),
              G.weight e := by
          apply Finset.sum_congr rfl
          intro e he
          exact (Finset.mem_filter.mp he).2.symm
        _ = ∑ e ∈ F, if G.weight e = x.1 then G.weight e else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ e ∈ F,
          ∑ x : G.EdgeSetWeightType F,
            if G.weight e = x.1 then G.weight e else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ F, G.weight e := by
      apply Finset.sum_congr rfl
      intro e he
      let x : G.EdgeSetWeightType F :=
        ⟨G.weight e, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
      rw [Finset.sum_eq_single x]
      · simp [x]
      · intro y _hy hyx
        have hne : G.weight e ≠ y.1 := by
          intro h
          apply hyx
          exact Subtype.ext h.symm
        simp [hne]
      · intro hx
        exact (hx (Finset.mem_univ x)).elim

/-- With reciprocal lower cutoff `1 / S`, a bundle whose exact cover costs
less than `B` contains at most `S * ceil B` physical edges. -/
theorem card_le_mul_ceil_of_exactDemandCover_cost_lt
    (F : Finset G.E) (C : G.EdgeSetExactDemandCover F)
    (S : ℕ) (B : ℝ) (hS : 0 < S)
    (hweight : ∀ e ∈ F, (1 : ℝ) / S ≤ G.weight e)
    (hcost : C.cost < B) :
    F.card ≤ S * Nat.ceil B := by
  have hweightSum : (F.card : ℝ) * ((1 : ℝ) / S) ≤
      ∑ e ∈ F, G.weight e := by
    calc
      (F.card : ℝ) * ((1 : ℝ) / S) =
          ∑ _e ∈ F, ((1 : ℝ) / S) := by simp
      _ ≤ ∑ e ∈ F, G.weight e := by
        exact Finset.sum_le_sum fun e he ↦ hweight e he
  have hsumCost : (∑ e ∈ F, G.weight e) ≤ C.cost := by
    rw [← G.edgeSet_exactDemandWeight_eq_sum F]
    exact C.exactDemandWeight_le_cost
  have hB0 : 0 ≤ B := by
    exact (C.cost_nonneg.trans hcost.le)
  have hcardB : (F.card : ℝ) < (S : ℝ) * B := by
    have hSR : (0 : ℝ) < S := by exact_mod_cast hS
    have := hweightSum.trans_lt (hsumCost.trans_lt hcost)
    rw [one_div] at this
    have hSne : (S : ℝ) ≠ 0 := ne_of_gt hSR
    calc
      (F.card : ℝ) = (S : ℝ) * ((F.card : ℝ) * (S : ℝ)⁻¹) := by
        field_simp
      _ < (S : ℝ) * B := mul_lt_mul_of_pos_left this hSR
  have hceil : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
  have hcardCeil : (F.card : ℝ) ≤ (S * Nat.ceil B : ℕ) := by
    push_cast
    exact (hcardB.trans_le (mul_le_mul_of_nonneg_left hceil
      (Nat.cast_nonneg S))).le
  exact_mod_cast hcardCeil

/-- Edges belonging to a parallel bundle whose chosen minimum exact-demand
cost is below `B`. -/
def smallMinimumCostBundleEdges (B : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦
    (G.floorBundleCover (G.floorKey e)).cost < B

theorem floorPairKey_comm_minimumCostBundles (u v : G.V) :
    G.floorPairKey u v = G.floorPairKey v u := by
  unfold floorPairKey
  by_cases h : G.floorVertexCode u < G.floorVertexCode v
  · have hn : ¬ G.floorVertexCode v < G.floorVertexCode u := by omega
    simp [h, hn]
  · by_cases huv : u = v
    · subst v
      rfl
    · have hcode : G.floorVertexCode u ≠ G.floorVertexCode v := by
        intro hc
        exact huv (G.floorVertexCode.injective hc)
      have hr : G.floorVertexCode v < G.floorVertexCode u := by omega
      simp [h, hr]

theorem floorKey_eq_floorPairKey_of_mem_endpointPairCell_minimumCostBundles
    {u v : G.V} {e : G.E} (he : e ∈ G.endpointPairCell u v) :
    G.floorKey e = G.floorPairKey u v := by
  rw [G.floorKey_eq_floorPairKey]
  have hends := (G.mem_endpointPairCell_iff u v e).mp he
  rcases (Sym2.eq_iff).mp hends with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, G.floorPairKey_comm_minimumCostBundles]

/-- The below-threshold bundles form a bounded-multiplicity residual.  This
is the fixed-pair-multiplicity half of the large/small bundle split. -/
theorem smallMinimumCostBundleGraph_pairMultiplicityAtMost
    (S : ℕ) (B : ℝ) (hS : 0 < S)
    (hweight : ∀ e : G.E, (1 : ℝ) / S ≤ G.weight e) :
    (G.edgeRestriction (G.smallMinimumCostBundleEdges B)).PairMultiplicityAtMost
      (S * Nat.ceil B) := by
  intro u v
  let H := G.edgeRestriction (G.smallMinimumCostBundleEdges B)
  let cell : Finset H.E := H.endpointPairCell u v
  by_cases hcell : cell.Nonempty
  · obtain ⟨e, hecell⟩ := hcell
    have heEnds : e.1 ∈ G.endpointPairCell u v := by
      have h := (H.mem_endpointPairCell_iff u v e).mp hecell
      exact (G.mem_endpointPairCell_iff u v e.1).mpr (by
        simpa [H, WeightedMultigraph.endpoints] using h)
    have heSmall :
        (G.floorBundleCover (G.floorPairKey u v)).cost < B := by
      have hs := (Finset.mem_filter.mp e.2).2
      rw [G.floorKey_eq_floorPairKey_of_mem_endpointPairCell_minimumCostBundles
        heEnds] at hs
      exact hs
    have hcellSub : cell.card ≤
        (G.floorBundle (G.floorPairKey u v)).card := by
      let f : {e : H.E // e ∈ cell} →
          {e : G.E // e ∈ G.floorBundle (G.floorPairKey u v)} := fun e ↦
        ⟨e.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have h := (H.mem_endpointPairCell_iff u v e.1).mp e.2
          have h' : e.1.1 ∈ G.endpointPairCell u v :=
            (G.mem_endpointPairCell_iff u v e.1.1).mpr (by
              simpa [H, WeightedMultigraph.endpoints] using h)
          exact G.floorKey_eq_floorPairKey_of_mem_endpointPairCell_minimumCostBundles
            h'⟩⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : {e : G.E // e ∈ G.floorBundle (G.floorPairKey u v)} ↦
            z.1) hab
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
    exact hcellSub.trans
      (G.card_le_mul_ceil_of_exactDemandCover_cost_lt
        (G.floorBundle (G.floorPairKey u v))
        (G.floorBundleCover (G.floorPairKey u v)) S B hS
        (fun e _he ↦ hweight e) heSmall)
  · have hz : cell.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hcell)
    change cell.card ≤ S * Nat.ceil B
    rw [hz]
    exact Nat.zero_le _

end WeightedMultigraph

end

end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.BinPackingInstance.ExactDemandPatternCover.exactDemandWeight_le_cost
#print axioms WeightedEdgeColoring.WeightedMultigraph.card_le_mul_ceil_of_exactDemandCover_cost_lt
#print axioms WeightedEdgeColoring.WeightedMultigraph.smallMinimumCostBundleGraph_pairMultiplicityAtMost
