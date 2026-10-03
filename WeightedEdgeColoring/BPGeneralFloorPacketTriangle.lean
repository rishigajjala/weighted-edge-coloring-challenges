import WeightedEdgeColoring.BPGeneralFloorPacketization
import WeightedEdgeColoring.BPGeneralTriangleBundles

/-!
# Triangle bound for the global coefficient-floor packetization

The full grouped packets between an unordered vertex pair are exactly the
floor packets of the corresponding physical parallel-bundle cover.  Hence
the original three star packings feed the exact-demand `2n` theorem directly.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

noncomputable section

universe u

variable (G : WeightedMultigraph.{u})

/-- Full packet labels belonging to one oriented parallel-bundle key. -/
noncomputable def fullFloorPacketsAtKey (k : G.V × G.V) :
    Finset G.floorPacketization.Packet :=
  Finset.univ.image fun q : (G.floorBundleCover k).FloorPacket ↦
    (Sum.inl ⟨k, q⟩ : G.floorPacketization.Packet)

theorem card_fullFloorPacketsAtKey (k : G.V × G.V) :
    (G.fullFloorPacketsAtKey k).card =
      (G.floorBundleCover k).floorPacketCount := by
  rw [fullFloorPacketsAtKey, Finset.card_image_iff.mpr]
  · rw [Finset.card_univ]
    exact (G.floorBundleCover k).card_floorPacket
  · intro q₁ _hq₁ q₂ _hq₂ h
    have hs := Sum.inl_injective h
    cases hs
    rfl

theorem grouped_edgesBetween_fullFloorPackets
    (u v : G.V) (huv : u ≠ v) :
    G.floorPacketization.groupedGraph.edgesBetween
        G.fullFloorPacketSet u v =
      G.fullFloorPacketsAtKey (G.floorPairKey u v) := by
  classical
  ext p
  cases p with
  | inr e =>
      simp [WeightedMultigraph.edgesBetween, fullFloorPacketSet,
        fullFloorPacketsAtKey, floorPacketization]
  | inl q =>
      rcases q with ⟨k, r⟩
      have hcanon : G.floorPairKey k.1 k.2 = k := by
        simpa using G.floorPairKey_packet_key ⟨k, r⟩
      have hpairComm : G.floorPairKey v u = G.floorPairKey u v := by
        unfold floorPairKey
        have hcode : G.floorVertexCode u ≠ G.floorVertexCode v := by
          intro h
          exact huv (G.floorVertexCode.injective h)
        by_cases h : G.floorVertexCode u < G.floorVertexCode v
        · have hn : ¬ G.floorVertexCode v < G.floorVertexCode u := by omega
          simp [h, hn]
        · have hr : G.floorVertexCode v < G.floorVertexCode u := by omega
          simp [h, hr]
      constructor
      · intro hp
        have hend : (k.1 = u ∧ k.2 = v) ∨
            (k.1 = v ∧ k.2 = u) := by
          simpa [WeightedMultigraph.edgesBetween, fullFloorPacketSet,
            floorPacketization, Packetization.groupedGraph,
            globalFloorTail, globalFloorHead] using hp
        apply Finset.mem_image.mpr
        rcases hend with h | h
        · have hk : k = G.floorPairKey u v := by
            rw [← hcanon, h.1, h.2]
          subst k
          exact ⟨r, Finset.mem_univ _, rfl⟩
        · have hk : k = G.floorPairKey u v := by
            rw [← hcanon, h.1, h.2, hpairComm]
          subst k
          exact ⟨r, Finset.mem_univ _, rfl⟩
      · intro hp
        rcases Finset.mem_image.mp hp with ⟨s, _hs, hlabel⟩
        have hq : (⟨k, r⟩ : G.GlobalFloorPacket) =
            ⟨G.floorPairKey u v, s⟩ :=
          Sum.inl_injective hlabel.symm
        have hk : k = G.floorPairKey u v := congrArg Sigma.fst hq
        subst k
        simp [WeightedMultigraph.edgesBetween, fullFloorPacketSet,
          floorPacketization, Packetization.groupedGraph,
          globalFloorTail, globalFloorHead, floorPairKey]
        by_cases h : G.floorVertexCode u < G.floorVertexCode v
        · simp [h]
        · have hr : G.floorVertexCode v < G.floorVertexCode u := by
            have hcode : G.floorVertexCode u ≠ G.floorVertexCode v := by
              intro heq
              exact huv (G.floorVertexCode.injective heq)
            omega
          simp [h]

theorem card_grouped_edgesBetween_fullFloorPackets
    (u v : G.V) (huv : u ≠ v) :
    (G.floorPacketization.groupedGraph.edgesBetween
      G.fullFloorPacketSet u v).card =
        (G.floorBundleCover (G.floorPairKey u v)).floorPacketCount := by
  rw [G.grouped_edgesBetween_fullFloorPackets u v huv,
    G.card_fullFloorPacketsAtKey]

theorem floorBundle_floorPairKey_eq_exactDemandEdgesBetween
    (u v : G.V) (huv : u ≠ v) :
    G.floorBundle (G.floorPairKey u v) =
      G.exactDemandEdgesBetween Finset.univ u v := by
  classical
  ext e
  simp only [floorBundle, exactDemandEdgesBetween, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hcode : G.floorVertexCode u ≠ G.floorVertexCode v := by
    intro h
    exact huv (G.floorVertexCode.injective h)
  unfold floorKey floorTail floorHead floorPairKey
  by_cases he : G.floorVertexCode (G.fst e) <
      G.floorVertexCode (G.snd e) <;>
    by_cases huv' : G.floorVertexCode u < G.floorVertexCode v <;>
      simp only [he, huv', if_true, if_false]
  all_goals
    constructor
    · intro h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      aesop
    · intro h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
      all_goals first
        | exact (lt_asymm he huv')
        | exact huv (G.floorVertexCode.injective (le_antisymm he huv'))

/-- The three physical parallel bundles selected by the global construction
have floor packet counts summing to at most `2n`, using only the original
three star packings. -/
theorem three_floorBundleCounts_le_two_mul_of_packsStarsInto
    (a b c : G.V) (n : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hpackA : G.PacksStarInto a n)
    (hpackB : G.PacksStarInto b n)
    (hpackC : G.PacksStarInto c n) :
    (G.floorBundleCover (G.floorPairKey a b)).floorPacketCount +
      (G.floorBundleCover (G.floorPairKey a c)).floorPacketCount +
      (G.floorBundleCover (G.floorPairKey b c)).floorPacketCount ≤
        2 * n := by
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
  have hpairA :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto FAB FAC a
      (by simpa [hFAB, hFAC] using hABAC) hincABa hincACa hpackA
  have hpairB :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto FAB FBC b
      (by simpa [hFAB, hFBC] using hABBC) hincABb hincBCb hpackB
  have hpairC :=
    G.sum_edgeSetWeightDemand_packsInto_of_packsStarInto FAC FBC c
      (by simpa [hFAC, hFBC] using hACBC) hincACc hincBCc hpackC
  apply BinPackingInstance.ExactDemandPatternCover.three_packetCounts_le_two_mul_of_pairwisePacksInto
      (A := G.edgeSetWeightBinPackingInstance FAB)
      (B := G.edgeSetWeightBinPackingInstance FAC)
      (Cinst := G.edgeSetWeightBinPackingInstance FBC)
      (firstDemand := G.edgeSetWeightDemand FAB)
      (secondDemand := G.edgeSetWeightDemand FAC)
      (thirdDemand := G.edgeSetWeightDemand FBC)
      (G.floorBundleCover (G.floorPairKey a b)).floorPacketCount
      (G.floorBundleCover (G.floorPairKey a c)).floorPacketCount
      (G.floorBundleCover (G.floorPairKey b c)).floorPacketCount n
  · exact G.edgeSetWeightDemand_pos FAB
  · exact G.edgeSetWeightDemand_pos FAC
  · exact G.edgeSetWeightDemand_pos FBC
  · intro D _hD
    exact (G.floorBundleCover (G.floorPairKey a b)).floorPacketCount_cast_le_cost.trans
        (G.floorBundleCover_minimum (G.floorPairKey a b) D)
  · intro D _hD
    exact (G.floorBundleCover (G.floorPairKey a c)).floorPacketCount_cast_le_cost.trans
        (G.floorBundleCover_minimum (G.floorPairKey a c) D)
  · intro D _hD
    exact (G.floorBundleCover (G.floorPairKey b c)).floorPacketCount_cast_le_cost.trans
        (G.floorBundleCover_minimum (G.floorPairKey b c) D)
  · exact hpairA
  · exact hpairB
  · exact hpairC

/-- The full packets of the explicit floor packetization satisfy the exact
`2n` triangle bound required by the general packet-coloring route. -/
theorem floorPacketization_triangleEdgeCountAtMost
    (n : ℕ) (hlocal : G.LocallyPacksInto n) :
    G.floorPacketization.groupedGraph.TriangleEdgeCountAtMost
      G.fullFloorPacketSet (2 * (n : ℝ)) := by
  intro S hS
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  rw [G.floorPacketization.groupedGraph.card_internalEdges_triple
    G.fullFloorPacketSet hab hac hbc]
  rw [G.card_grouped_edgesBetween_fullFloorPackets a b hab,
    G.card_grouped_edgesBetween_fullFloorPackets a c hac,
    G.card_grouped_edgesBetween_fullFloorPackets b c hbc]
  exact_mod_cast G.three_floorBundleCounts_le_two_mul_of_packsStarsInto
    a b c n hab hac hbc (hlocal a) (hlocal b) (hlocal c)
