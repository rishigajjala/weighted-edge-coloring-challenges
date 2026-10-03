import WeightedEdgeColoring.SubtwoPacketGraph
import WeightedEdgeColoring.SubtwoPacketLifting
import WeightedEdgeColoring.SubtwoHarmonicMargin
import WeightedEdgeColoring.BPGeneralFloorPacketBase

/-!
# The dense-block construction on actual full floor packets

Costs are normalized full-packet counts, not hypothetical fractional
edge costs. The local bin packings bound every parallel bundle, and the
harmonic charge pays for the degree of the actual packet graph.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

namespace BinPackingInstance.ExactDemandPatternCover

theorem subtwo_packsInto_left
    {A B : BinPackingInstance} {a : A.Item → ℕ} {b : B.Item → ℕ} {n : ℕ}
    (h : PacksInto (B := A.sum B) (sumDemand a b) n) :
    PacksInto (B := A) a n := by
  classical
  obtain ⟨P⟩ := h
  let pattern : Fin n → A.Pattern := fun j ↦
    { multiplicity := fun i ↦ (P.pattern j).multiplicity (Sum.inl i)
      capacity := by
        have hc := (P.pattern j).capacity
        change (∑ i : A.Item ⊕ B.Item,
          ((P.pattern j).multiplicity i : ℝ) * Sum.elim A.weight B.weight i) ≤ 1 at hc
        rw [Fintype.sum_sum_type] at hc
        exact (le_add_of_nonneg_right (Finset.sum_nonneg
          (fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (B.weight_pos i).le))).trans hc }
  refine ⟨⟨pattern, ?_⟩⟩
  intro i
  exact P.covers_exact (Sum.inl i)

end BinPackingInstance.ExactDemandPatternCover

namespace WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem subtwo_edgeSetWeightDemand_packsInto_of_packsStarInto
    (F : Finset G.E) (v : G.V) {n : ℕ}
    (hinc : ∀ e ∈ F, G.Inc v e) (hpack : G.PacksStarInto v n) :
    BinPackingInstance.ExactDemandPatternCover.PacksInto
      (B := G.edgeSetWeightBinPackingInstance F) (G.edgeSetWeightDemand F) n := by
  apply BinPackingInstance.ExactDemandPatternCover.subtwo_packsInto_left
    (B := G.edgeSetWeightBinPackingInstance ∅)
    (b := G.edgeSetWeightDemand ∅)
  exact G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto
    F ∅ v (Finset.disjoint_empty_right F) hinc (by simp) hpack

theorem subtwo_floorBundleCover_cost_le
    (a b : G.V) (hab : a ≠ b) {n : ℕ} (hpack : G.PacksStarInto a n) :
    (G.floorBundleCover (G.floorPairKey a b)).cost ≤ n := by
  have hinc : ∀ e ∈ G.floorBundle (G.floorPairKey a b), G.Inc a e := by
    intro e he
    rw [G.floorBundle_floorPairKey_eq_exactDemandEdgesBetween a b hab] at he
    exact G.inc_left_of_mem_exactDemandEdgesBetween he
  have hp := G.subtwo_edgeSetWeightDemand_packsInto_of_packsStarInto
    (G.floorBundle (G.floorPairKey a b)) a hinc hpack
  obtain ⟨C, hC⟩ :=
    BinPackingInstance.ExactDemandPatternCover.exists_cost_eq_of_packsInto hp
  exact (G.floorBundleCover_minimum _ C).trans_eq hC

theorem subtwo_fullFloorPackets_pair_le
    (a b : G.V) (hab : a ≠ b) {n : ℕ} (hpack : G.PacksStarInto a n) :
    (G.floorPacketization.groupedGraph.edgesBetween G.fullFloorPacketSet a b).card ≤ n := by
  rw [G.card_grouped_edgesBetween_fullFloorPackets a b hab]
  exact_mod_cast (G.floorBundleCover (G.floorPairKey a b)).floorPacketCount_cast_le_cost.trans
    (G.subtwo_floorBundleCover_cost_le a b hab hpack)

theorem subtwo_fullFloorPackets_degree_le
    {n : ℕ} (hlocal : G.LocallyPacksInto n) (v : G.V) :
    (G.floorPacketization.groupedGraph.degreeOn G.fullFloorPacketSet v : ℝ) ≤
      subtwoM * n := by
  have h := G.fullFloorPacketDegree_add_residualHarmonicCharge_le v
  have hn := G.fullFloorResidualHarmonicCharge_nonneg v
  have hh := G.harmonicStarCharge_le_of_packsStarInto (hlocal v)
  have hm : harmonicBinPackingConstant ≤ subtwoM := Subtwo.harmonic_lt_M.le
  have hnm := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

/-- The normalized count assigned to one selected edge. -/
noncomputable def subtwoSelectedCost (F : Finset G.E) (N : ℝ) (e : G.E) : ℝ :=
  if e ∈ F then 1 / N else 0

theorem subtwoSelectedCost_vertex (F : Finset G.E) (N : ℝ) (v : G.V) :
    G.subtwoVertexCost (G.subtwoSelectedCost F N) v =
      (G.degreeOn F v : ℝ) / N := by
  classical
  rw [G.subtwoVertexCost_eq_incidence]
  simp [subtwoSelectedCost, degreeOn, Finset.sum_ite, div_eq_mul_inv]
  left
  congr 1
  ext e
  simp [and_comm]

theorem subtwoSelectedCost_internal (F : Finset G.E) (N : ℝ) (S : Finset G.V) :
    G.subtwoInternalCost (G.subtwoSelectedCost F N) S =
      ((G.internalEdges F S).card : ℝ) / N := by
  classical
  unfold subtwoInternalCost
  simp [subtwoSelectedCost, internalEdges, Finset.sum_ite, div_eq_mul_inv]
  left
  congr 1
  ext e
  simp [and_comm]

theorem subtwo_internalEdges_pair (F : Finset G.E) (a b : G.V) :
    G.internalEdges F {a, b} = G.edgesBetween F a b := by
  classical
  ext e
  have hn := G.noLoop e
  simp only [internalEdges, edgesBetween, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton]
  aesop

/-- Full packet edges, each carrying normalized cost `1/n`. -/
noncomputable def subtwoFloorCost (n : ℕ) :
    G.floorPacketization.groupedGraph.E → ℝ :=
  G.floorPacketization.groupedGraph.subtwoSelectedCost G.fullFloorPacketSet n

theorem subtwoFloorCost_nonneg (n : ℕ) (p : G.floorPacketization.groupedGraph.E) :
    0 ≤ G.subtwoFloorCost n p := by
  unfold subtwoFloorCost subtwoSelectedCost
  split <;> positivity

theorem subtwoFloorCost_pair_le
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (C : Finset G.V) (hC : C.card = 2) :
    G.floorPacketization.groupedGraph.subtwoInternalCost (G.subtwoFloorCost n) C ≤ 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hC
  rw [subtwoFloorCost, subtwoSelectedCost_internal, subtwo_internalEdges_pair]
  have hp := G.subtwo_fullFloorPackets_pair_le a b hab (hlocal a)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).2
  simpa using (Nat.cast_le.mpr hp :
    ((G.floorPacketization.groupedGraph.edgesBetween G.fullFloorPacketSet a b).card : ℝ) ≤ n)

theorem subtwoFloorCost_degree_le
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n) (v : G.V) :
    G.floorPacketization.groupedGraph.subtwoVertexCost (G.subtwoFloorCost n) v ≤ subtwoM := by
  rw [subtwoFloorCost, subtwoSelectedCost_vertex]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_le_iff₀ hnR).2 (G.subtwo_fullFloorPackets_degree_le hlocal v)

/-- Blocks selected directly from the concrete full packets. -/
noncomputable def subtwoFloorBlock (n : ℕ) :=
  G.floorPacketization.groupedGraph.subtwoFinalBlock (G.subtwoFloorCost n)

/-- Actual quotient of the packetization, including indexed residual edges.
Only the selected full packets are colored in the ordinary base step. -/
noncomputable def subtwoFloorQuotient (n : ℕ) : WeightedMultigraph.{u} :=
  G.floorPacketization.groupedGraph.subtwoQuotient (G.subtwoFloorBlock n)

noncomputable def subtwoFloorQuotientEdges (n : ℕ) : Finset (G.subtwoFloorQuotient n).E :=
  G.floorPacketization.groupedGraph.subtwoQuotientSelectedEdges
    (G.subtwoFloorBlock n) G.fullFloorPacketSet

theorem subtwoFloorQuotient_cost_eq (n : ℕ) :
    (fun e : (G.subtwoFloorQuotient n).E ↦ G.subtwoFloorCost n e.1) =
      (G.subtwoFloorQuotient n).subtwoSelectedCost (G.subtwoFloorQuotientEdges n) n := by
  classical
  funext e
  simp [subtwoFloorCost, subtwoSelectedCost, subtwoFloorQuotientEdges,
    subtwoQuotientSelectedEdges]

theorem subtwoFloorQuotient_degree_le
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (v : (G.subtwoFloorQuotient n).V) :
    ((G.subtwoFloorQuotient n).degreeOn (G.subtwoFloorQuotientEdges n) v : ℝ) ≤
      subtwoM * n := by
  have h := G.floorPacketization.groupedGraph.subtwoFinalQuotient_degree_le
    (G.subtwoFloorCost n) (G.subtwoFloorCost_nonneg n)
    (G.subtwoFloorCost_pair_le hn hlocal) (G.subtwoFloorCost_degree_le hn hlocal) v
  change (G.subtwoFloorQuotient n).subtwoVertexCost
    (fun e ↦ G.subtwoFloorCost n e.1) v ≤ subtwoM at h
  rw [G.subtwoFloorQuotient_cost_eq, subtwoSelectedCost_vertex] at h
  exact (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).1 h

theorem subtwoFloorQuotient_oddSetDensityAtMost
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n) :
    (G.subtwoFloorQuotient n).OddSetDensityAtMost
      (G.subtwoFloorQuotientEdges n) (subtwoKappa * n) := by
  intro S hodd hthree
  have h := G.floorPacketization.groupedGraph.subtwoFinalQuotient_all_odd_sets
    (G.subtwoFloorCost n) (G.subtwoFloorCost_nonneg n)
    (G.subtwoFloorCost_pair_le hn hlocal) (G.subtwoFloorCost_degree_le hn hlocal)
    S hodd hthree
  change (G.subtwoFloorQuotient n).subtwoInternalCost
    (fun e ↦ G.subtwoFloorCost n e.1) S ≤ subtwoKappa * (S.card - 1) / 2 at h
  rw [G.subtwoFloorQuotient_cost_eq, subtwoSelectedCost_internal] at h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := (div_le_iff₀ hnR).1 h
  change 2 * ((G.subtwoFloorQuotient n).internalEdges
    (G.subtwoFloorQuotientEdges n) S).card ≤ subtwoKappa * n * (S.card - 1)
  nlinarith

/-- The physical edges in the selected crossing full packets. -/
noncomputable def subtwoFloorBaseEdges (n : ℕ) : Finset G.E :=
  G.floorPacketization.originalEdgesOfPackets
    (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
      (G.subtwoFloorBlock n) G.fullFloorPacketSet)

noncomputable def subtwoFloorBaseColor {k : ℕ} (hk : 0 < k) (n : ℕ)
    (color : (G.subtwoFloorQuotient n).E → Fin k) : G.E → Fin k :=
  G.floorPacketization.expandColor
    (G.floorPacketization.groupedGraph.subtwoLiftQuotientColor
      hk (G.subtwoFloorBlock n) color)

theorem subtwoFloorBaseColor_isFeasibleOn
    {k n : ℕ} (hk : 0 < k) (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color) :
    G.IsFeasibleOn (G.subtwoFloorBaseEdges n) (G.subtwoFloorBaseColor hk n color) :=
  G.floorPacketization.subtwo_isFeasibleOn_expand_quotient hk
    (G.subtwoFloorBlock n) G.fullFloorPacketSet color hproper

theorem subtwoFloorBaseColor_endpoint_unique
    {k n : ℕ} (hk : 0 < k) (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color)
    {e f : G.E} (he : e ∈ G.subtwoFloorBaseEdges n) (hf : f ∈ G.subtwoFloorBaseEdges n)
    {v w : G.V} (hev : G.Inc v e) (hfw : G.Inc w f)
    (hb : G.subtwoFloorBlock n v = G.subtwoFloorBlock n w)
    (hc : G.subtwoFloorBaseColor hk n color e = G.subtwoFloorBaseColor hk n color f) :
    v = w :=
  G.floorPacketization.subtwo_expanded_quotient_color_endpoint_unique
    hk (G.subtwoFloorBlock n) G.fullFloorPacketSet color hproper he hf hev hfw hb hc

/-- Apply the ordinary-coloring input to the concrete packet quotient.
This is an implication: the ordinary theorem is still proved separately. -/
theorem exists_subtwoFloorBaseColor_of_ordinary
    (hordinary : Subtwo.QuotientOrdinaryColoring.{u})
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → G.LocallyPacksInto n →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (subtwoKappa + η) * n ∧
        ∃ color : (G.subtwoFloorQuotient n).E → Fin k,
          (G.subtwoFloorQuotient n).IsProperOn (G.subtwoFloorQuotientEdges n) color := by
  obtain ⟨N, hN⟩ := hordinary η hη
  refine ⟨max N 1, ?_⟩
  intro n hn hlocal
  have hn0 : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hn)
  apply hN (G.subtwoFloorQuotient n) (G.subtwoFloorQuotientEdges n) n
    ((le_max_left N 1).trans hn)
  · exact G.subtwoFloorQuotient_degree_le hn0 hlocal
  · exact G.subtwoFloorQuotient_oddSetDensityAtMost hn0 hlocal

end WeightedMultigraph
end WeightedEdgeColoring
