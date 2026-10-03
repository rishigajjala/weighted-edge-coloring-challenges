import WeightedEdgeColoring.BPGeneralMinimumCostSmallBundles
import WeightedEdgeColoring.BPGeneralLargeSmallTriangleLift
import WeightedEdgeColoring.BPGraphTwoBundlePacking
import WeightedEdgeColoring.FiniteUnitDemandExactPatternCover

/-!
# Minimum covers of physical indexed parallel bundles

Linear grouping must remember individual physical edges, so this file uses
`edgeSetBinPackingInstance` rather than first merging equal weights.  Every
physical edge coordinate has demand one.  We choose a minimum exact-demand
cover for each canonical unordered endpoint pair and record the same two
facts already available for the weight-merged cover:

* a below-threshold bundle has fixed cardinality; and
* the three minimum costs around a triangle sum to at most `2n`.

These are the threshold and triangle inputs for the physical linear-grouping
construction.
-/

open scoped BigOperators Sym2

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Exact unit-demand covers of the physically indexed edges in `F`. -/
abbrev PhysicalEdgeSetExactDemandCover (F : Finset G.E) :=
  (G.edgeSetBinPackingInstance F).ExactDemandPatternCover (fun _ ↦ 1)

/-- A canonical minimum exact unit-demand cover for one endpoint bundle. -/
noncomputable def physicalBundleCover (k : G.V × G.V) :
    G.PhysicalEdgeSetExactDemandCover (G.floorBundle k) :=
  Classical.choose
    (BinPackingInstance.ExactDemandPatternCover.exists_minimumCost
      (G.edgeSetBinPackingInstance (G.floorBundle k)) (fun _ ↦ 1))

theorem physicalBundleCover_minimum (k : G.V × G.V) :
    (G.physicalBundleCover k).IsMinimumCost :=
  Classical.choose_spec
    (BinPackingInstance.ExactDemandPatternCover.exists_minimumCost
      (G.edgeSetBinPackingInstance (G.floorBundle k)) (fun _ ↦ 1))

/-- For physical unit demand, exact-demand weight is the ordinary sum of
edge weights. -/
theorem physicalEdgeSet_exactDemandWeight_eq_sum (F : Finset G.E) :
    BinPackingInstance.ExactDemandPatternCover.exactDemandWeight
        (G.edgeSetBinPackingInstance F) (fun _ ↦ 1) =
      ∑ e ∈ F, G.weight e := by
  unfold BinPackingInstance.ExactDemandPatternCover.exactDemandWeight
    edgeSetBinPackingInstance
  simp only [Nat.cast_one, one_mul]
  change (∑ e : {e : G.E // e ∈ F}, G.weight e.1) =
    ∑ e ∈ F, G.weight e
  exact (Finset.sum_subtype (p := fun e : G.E ↦ e ∈ F) F
    (by intro e; simp) G.weight).symm

/-- If every edge in a physical bundle has weight at least `1/S`, then the
number of physical edges is at most `S` times the minimum unit-demand cover
cost.  This is the linear estimate used to turn a grouping remainder into a
multiplicative error. -/
theorem floorBundle_card_cast_le_mul_physicalBundleCover_cost
    (k : G.V × G.V) (S : ℕ) (hS : 0 < S)
    (hweight : ∀ e ∈ G.floorBundle k, (1 : ℝ) / S ≤ G.weight e) :
    ((G.floorBundle k).card : ℝ) ≤
      (S : ℝ) * (G.physicalBundleCover k).cost := by
  let F := G.floorBundle k
  let C := G.physicalBundleCover k
  have hweightSum : (F.card : ℝ) * ((1 : ℝ) / S) ≤
      ∑ e ∈ F, G.weight e := by
    calc
      (F.card : ℝ) * ((1 : ℝ) / S) =
          ∑ _e ∈ F, ((1 : ℝ) / S) := by simp
      _ ≤ ∑ e ∈ F, G.weight e :=
        Finset.sum_le_sum fun e he ↦ hweight e he
  have hsumCost : (∑ e ∈ F, G.weight e) ≤ C.cost := by
    rw [← G.physicalEdgeSet_exactDemandWeight_eq_sum F]
    exact C.exactDemandWeight_le_cost
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  calc
    (F.card : ℝ) =
        (S : ℝ) * ((F.card : ℝ) * ((1 : ℝ) / S)) := by
      field_simp
    _ ≤ (S : ℝ) * C.cost :=
      mul_le_mul_of_nonneg_left (hweightSum.trans hsumCost) hSR.le

/-- A physical bundle with reciprocal weight floor `1/S` and minimum cost
below `B` contains at most `S * ceil B` edges. -/
theorem floorBundle_card_le_mul_ceil_of_physicalBundleCover_cost_lt
    (k : G.V × G.V) (S : ℕ) (B : ℝ) (hS : 0 < S)
    (hweight : ∀ e ∈ G.floorBundle k, (1 : ℝ) / S ≤ G.weight e)
    (hcost : (G.physicalBundleCover k).cost < B) :
    (G.floorBundle k).card ≤ S * Nat.ceil B := by
  let F := G.floorBundle k
  let C := G.physicalBundleCover k
  have hweightSum : (F.card : ℝ) * ((1 : ℝ) / S) ≤
      ∑ e ∈ F, G.weight e := by
    calc
      (F.card : ℝ) * ((1 : ℝ) / S) =
          ∑ _e ∈ F, ((1 : ℝ) / S) := by simp
      _ ≤ ∑ e ∈ F, G.weight e :=
        Finset.sum_le_sum fun e he ↦ hweight e he
  have hsumCost : (∑ e ∈ F, G.weight e) ≤ C.cost := by
    rw [← G.physicalEdgeSet_exactDemandWeight_eq_sum F]
    exact C.exactDemandWeight_le_cost
  have hB0 : 0 ≤ B := C.cost_nonneg.trans hcost.le
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  have hcardB : (F.card : ℝ) < (S : ℝ) * B := by
    have h := hweightSum.trans_lt (hsumCost.trans_lt hcost)
    calc
      (F.card : ℝ) = (S : ℝ) * ((F.card : ℝ) * (S : ℝ)⁻¹) := by
        field_simp
      _ < (S : ℝ) * B := mul_lt_mul_of_pos_left (by
        simpa [one_div] using h) hSR
  have hceil : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
  have hcardCeil : (F.card : ℝ) ≤ (S * Nat.ceil B : ℕ) := by
    push_cast
    exact (hcardB.trans_le
      (mul_le_mul_of_nonneg_left hceil (Nat.cast_nonneg S))).le
  exact_mod_cast hcardCeil

/-- Physical edges whose endpoint bundle has minimum unit-demand cost below
the fixed threshold. -/
def smallPhysicalMinimumCostBundleEdges (B : ℝ) : Finset G.E :=
  Finset.univ.filter fun e ↦
    (G.physicalBundleCover (G.floorKey e)).cost < B

/-- The below-threshold physical bundles form a fixed-multiplicity
residual. -/
theorem smallPhysicalMinimumCostBundleGraph_pairMultiplicityAtMost
    (S : ℕ) (B : ℝ) (hS : 0 < S)
    (hweight : ∀ e : G.E, (1 : ℝ) / S ≤ G.weight e) :
    (G.edgeRestriction
      (G.smallPhysicalMinimumCostBundleEdges B)).PairMultiplicityAtMost
        (S * Nat.ceil B) := by
  intro u v
  let H := G.edgeRestriction (G.smallPhysicalMinimumCostBundleEdges B)
  let cell : Finset H.E := H.endpointPairCell u v
  by_cases hcell : cell.Nonempty
  · obtain ⟨e, hecell⟩ := hcell
    have heEnds : e.1 ∈ G.endpointPairCell u v := by
      have h := (H.mem_endpointPairCell_iff u v e).mp hecell
      exact (G.mem_endpointPairCell_iff u v e.1).mpr (by
        simpa [H, WeightedMultigraph.endpoints] using h)
    have heSmall :
        (G.physicalBundleCover (G.floorPairKey u v)).cost < B := by
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
      (G.floorBundle_card_le_mul_ceil_of_physicalBundleCover_cost_lt
        (G.floorPairKey u v) S B hS (fun e _he ↦ hweight e) heSmall)
  · have hz : cell.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hcell)
    change cell.card ≤ S * Nat.ceil B
    rw [hz]
    exact Nat.zero_le _

/-- Around three distinct vertices, the three minimum physical bundle costs
sum to at most twice the common local bin bound. -/
theorem three_physicalBundleCoverCosts_le_two_mul_of_packsStarsInto
    (a b c : G.V) (n : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpackA : G.PacksStarInto a n)
    (hpackB : G.PacksStarInto b n)
    (hpackC : G.PacksStarInto c n) :
    (G.physicalBundleCover (G.floorPairKey a b)).cost +
      (G.physicalBundleCover (G.floorPairKey a c)).cost +
      (G.physicalBundleCover (G.floorPairKey b c)).cost ≤ 2 * (n : ℝ) := by
  let FAB := G.floorBundle (G.floorPairKey a b)
  let FAC := G.floorBundle (G.floorPairKey a c)
  let FBC := G.floorBundle (G.floorPairKey b c)
  have hFAB : FAB = G.exactDemandEdgesBetween Finset.univ a b :=
    G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab
  have hFAC : FAC = G.exactDemandEdgesBetween Finset.univ a c :=
    G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a c hac
  have hFBC : FBC = G.exactDemandEdgesBetween Finset.univ b c :=
    G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween b c hbc
  obtain ⟨hABAC, hABBC, hACBC⟩ :=
    G.exactDemandEdgesBetween_pairwise_disjoint Finset.univ hab hac hbc
  have hincABa : ∀ e ∈ FAB, G.Inc a e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween (hFAB ▸ he)
  have hincABb : ∀ e ∈ FAB, G.Inc b e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween (hFAB ▸ he)
  have hincACa : ∀ e ∈ FAC, G.Inc a e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween (hFAC ▸ he)
  have hincACc : ∀ e ∈ FAC, G.Inc c e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween (hFAC ▸ he)
  have hincBCb : ∀ e ∈ FBC, G.Inc b e := by
    intro e he
    exact G.inc_left_of_mem_exactDemandEdgesBetween (hFBC ▸ he)
  have hincBCc : ∀ e ∈ FBC, G.Inc c e := by
    intro e he
    exact G.inc_right_of_mem_exactDemandEdgesBetween (hFBC ▸ he)
  have hpackABAC :=
    G.sum_edgeSetBinPackingInstance_packsInto_of_packsStarInto FAB FAC a
      (by simpa [hFAB, hFAC] using hABAC) hincABa hincACa hpackA
  have hpackABBC :=
    G.sum_edgeSetBinPackingInstance_packsInto_of_packsStarInto FAB FBC b
      (by simpa [hFAB, hFBC] using hABBC) hincABb hincBCb hpackB
  have hpackACBC :=
    G.sum_edgeSetBinPackingInstance_packsInto_of_packsStarInto FAC FBC c
      (by simpa [hFAC, hFBC] using hACBC) hincACc hincBCc hpackC
  have hpairA :
      BinPackingInstance.ExactDemandPatternCover.PacksInto
        (B := (G.edgeSetBinPackingInstance FAB).sum
          (G.edgeSetBinPackingInstance FAC))
        (BinPackingInstance.ExactDemandPatternCover.sumDemand
          (fun _ ↦ 1) (fun _ ↦ 1)) n := by
    simpa using
      (BinPackingInstance.unitDemand_packsInto_of_packsInto hpackABAC)
  have hpairB :
      BinPackingInstance.ExactDemandPatternCover.PacksInto
        (B := (G.edgeSetBinPackingInstance FAB).sum
          (G.edgeSetBinPackingInstance FBC))
        (BinPackingInstance.ExactDemandPatternCover.sumDemand
          (fun _ ↦ 1) (fun _ ↦ 1)) n := by
    simpa using
      (BinPackingInstance.unitDemand_packsInto_of_packsInto hpackABBC)
  have hpairC :
      BinPackingInstance.ExactDemandPatternCover.PacksInto
        (B := (G.edgeSetBinPackingInstance FAC).sum
          (G.edgeSetBinPackingInstance FBC))
        (BinPackingInstance.ExactDemandPatternCover.sumDemand
          (fun _ ↦ 1) (fun _ ↦ 1)) n := by
    simpa using
      (BinPackingInstance.unitDemand_packsInto_of_packsInto hpackACBC)
  exact
    BinPackingInstance.ExactDemandPatternCover.three_minimumExactCosts_le_two_mul_of_pairwisePacksInto
      (G.physicalBundleCover (G.floorPairKey a b))
      (G.physicalBundleCover (G.floorPairKey a c))
      (G.physicalBundleCover (G.floorPairKey b c))
      (G.physicalBundleCover_minimum (G.floorPairKey a b))
      (G.physicalBundleCover_minimum (G.floorPairKey a c))
      (G.physicalBundleCover_minimum (G.floorPairKey b c))
      (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
      hpairA hpairB hpairC

namespace Packetization

variable {G} (P : G.Packetization)

/-- A per-pair `(1+δ)` packet-count bound against the physical minimum
cost gives the scaled triangle bound. -/
theorem triangleEdgeCountAtMost_of_pairCount_le_scaled_physicalBundleCost
    (selected : Finset P.Packet) (n : ℕ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hlocal : G.LocallyPacksInto n)
    (hpair : ∀ u v, u ≠ v →
      ((P.groupedGraph.edgesBetween selected u v).card : ℝ) ≤
        (1 + delta) *
          (G.physicalBundleCover (G.floorPairKey u v)).cost) :
    P.groupedGraph.TriangleEdgeCountAtMost selected
      (2 * (1 + delta) * (n : ℝ)) := by
  intro T hT
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hT
  rw [P.groupedGraph.card_internalEdges_triple selected hab hac hbc]
  push_cast
  calc
    ((P.groupedGraph.edgesBetween selected a b).card : ℝ) +
        (P.groupedGraph.edgesBetween selected a c).card +
        (P.groupedGraph.edgesBetween selected b c).card ≤
      (1 + delta) *
          (G.physicalBundleCover (G.floorPairKey a b)).cost +
        (1 + delta) *
          (G.physicalBundleCover (G.floorPairKey a c)).cost +
        (1 + delta) *
          (G.physicalBundleCover (G.floorPairKey b c)).cost := by
      gcongr
      · exact hpair a b hab
      · exact hpair a c hac
      · exact hpair b c hbc
    _ = (1 + delta) *
        ((G.physicalBundleCover (G.floorPairKey a b)).cost +
          (G.physicalBundleCover (G.floorPairKey a c)).cost +
          (G.physicalBundleCover (G.floorPairKey b c)).cost) := by ring
    _ ≤ (1 + delta) * (2 * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (G.three_physicalBundleCoverCosts_le_two_mul_of_packsStarsInto
          a b c n hab hac hbc (hlocal a) (hlocal b) (hlocal c))
        (by linarith)
    _ = 2 * (1 + delta) * (n : ℝ) := by ring

/-- Natural additive slack absorbs the physical-bundle triangle loss. -/
theorem triangleEdgeCountAtMost_additive_of_pairCount_le_scaled_physicalBundleCost
    (selected : Finset P.Packet) (n d : ℕ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hdeltaN : delta * (n : ℝ) ≤ d)
    (hlocal : G.LocallyPacksInto n)
    (hpair : ∀ u v, u ≠ v →
      ((P.groupedGraph.edgesBetween selected u v).card : ℝ) ≤
        (1 + delta) *
          (G.physicalBundleCover (G.floorPairKey u v)).cost) :
    P.groupedGraph.TriangleEdgeCountAtMost selected
      (2 * ((n + d : ℕ) : ℝ)) := by
  have hscaled :=
    P.triangleEdgeCountAtMost_of_pairCount_le_scaled_physicalBundleCost
      selected n delta hdelta hlocal hpair
  exact fun T hT ↦ (hscaled T hT).trans (by
    push_cast
    nlinarith)

end Packetization

end

end WeightedMultigraph
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.WeightedMultigraph.physicalBundleCover_minimum
#print axioms WeightedEdgeColoring.WeightedMultigraph.smallPhysicalMinimumCostBundleGraph_pairMultiplicityAtMost
#print axioms WeightedEdgeColoring.WeightedMultigraph.three_physicalBundleCoverCosts_le_two_mul_of_packsStarsInto
#print axioms WeightedEdgeColoring.WeightedMultigraph.Packetization.triangleEdgeCountAtMost_additive_of_pairCount_le_scaled_physicalBundleCost
