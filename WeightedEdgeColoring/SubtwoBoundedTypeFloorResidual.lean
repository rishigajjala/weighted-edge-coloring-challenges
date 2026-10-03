import WeightedEdgeColoring.FiniteExactDemandFloorRemainderBound
import WeightedEdgeColoring.BPGeneralFloorResidualHarmonicRefinement
import WeightedEdgeColoring.SubtwoMixedGraphQuotientPairMultiplicity

/-! Fixed weight-type bundles have a demand-independent coefficient-floor residual. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

universe u
variable (G : WeightedMultigraph.{u})

private def floorResidualCopies (k : G.V × G.V)
    (x : G.EdgeSetWeightType (G.floorBundle k)) :
    Finset (G.EdgeSetPhysicalCopy (G.floorBundle k) x) :=
  Finset.univ \ Finset.univ.image
    (G.floorOccurrenceEmbedding (G.floorBundle k) (G.floorBundleCover k) x)

private theorem card_floorResidualCopies (k : G.V × G.V)
    (x : G.EdgeSetWeightType (G.floorBundle k)) :
    (G.floorResidualCopies k x).card =
      (G.floorBundleCover k).floorResidualDemand x := by
  rw [floorResidualCopies, Finset.card_sdiff]
  simp only [Finset.inter_univ]
  rw [Finset.card_image_of_injective _
    (G.floorOccurrenceEmbedding (G.floorBundle k) (G.floorBundleCover k) x).injective]
  rw [Finset.card_univ, Finset.card_univ]
  rw [G.card_edgeSetPhysicalCopy,
    (G.floorBundleCover k).card_floorOccurrence x]
  rfl

private def floorResidualBundleInjection (k : G.V × G.V) :
    {e : G.E // e ∈ G.floorBundle k ∧ e ∈ G.floorResidualEdges} ↪
      Σ x : G.EdgeSetWeightType (G.floorBundle k),
        {z : G.EdgeSetPhysicalCopy (G.floorBundle k) x //
          z ∈ G.floorResidualCopies k x} := by
  let f : {e : G.E // e ∈ G.floorBundle k ∧ e ∈ G.floorResidualEdges} →
      Σ x : G.EdgeSetWeightType (G.floorBundle k),
        {z : G.EdgeSetPhysicalCopy (G.floorBundle k) x //
          z ∈ G.floorResidualCopies k x} := fun e => by
    let x : G.EdgeSetWeightType (G.floorBundle k) :=
      ⟨G.weight e.1, Finset.mem_image.mpr ⟨e.1, e.2.1, rfl⟩⟩
    let z : G.EdgeSetPhysicalCopy (G.floorBundle k) x :=
      ⟨e.1, e.2.1, rfl⟩
    refine ⟨x, ⟨z, ?_⟩⟩
    rw [floorResidualCopies, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hz
    rcases Finset.mem_image.mp hz with ⟨o, _, ho⟩
    have ha : G.IsFloorAssigned e.1 := by
      refine ⟨⟨k, x, o⟩, ?_⟩
      exact congrArg Subtype.val ho
    exact (G.mem_floorResidualEdges_iff_not_floorAssigned e.1).mp e.2.2 ha
  refine ⟨f, ?_⟩
  intro e e' h
  apply Subtype.ext
  exact congrArg (fun z => z.2.1.1) h

/-- A bundle's unassigned physical edges are bounded by the sum of the
coefficient-floor residual demands of its distinct weight types. -/
theorem card_floorResidual_bundle_le_sum (k : G.V × G.V) :
    ((G.floorResidualEdges.filter fun e => e ∈ G.floorBundle k).card) ≤
      ∑ x : G.EdgeSetWeightType (G.floorBundle k),
        (G.floorBundleCover k).floorResidualDemand x := by
  classical
  have hcard := Fintype.card_le_of_injective (G.floorResidualBundleInjection k)
    (G.floorResidualBundleInjection k).injective
  convert hcard using 1
  · simp only [Fintype.card_subtype]
    apply congrArg Finset.card
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    tauto
  · simp [Fintype.card_sigma, G.card_floorResidualCopies k]

/-- A uniform oriented-bundle count passes to unordered endpoint pairs. -/
theorem floorResidualGraph_pairMultiplicityAtMost_of_bundleBound
    (R : ℕ)
    (hR : ∀ k : G.V × G.V,
      (G.floorResidualEdges.filter fun e => e ∈ G.floorBundle k).card ≤ R) :
    (G.edgeRestriction G.floorResidualEdges).PairMultiplicityAtMost R := by
  intro u v
  let H := G.edgeRestriction G.floorResidualEdges
  let emb : H.E ↪ G.E := ⟨Subtype.val, Subtype.val_injective⟩
  let F := H.endpointPairCell u v
  have hmap : F.map emb =
      G.floorResidualEdges.filter fun e => e ∈ G.endpointPairCell u v := by
    ext e
    simp [F, emb, H, WeightedMultigraph.endpointPairCell,
      WeightedMultigraph.endpoints, and_comm]
  have hsub :
      G.floorResidualEdges.filter (fun e => e ∈ G.endpointPairCell u v) ⊆
        G.floorResidualEdges.filter
          (fun e => e ∈ G.floorBundle (G.floorPairKey u v)) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    exact ⟨he'.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        G.floorKey_eq_floorPairKey_of_mem_endpointPairCell he'.2⟩⟩
  calc
    F.card = (F.map emb).card := (Finset.card_map emb).symm
    _ = (G.floorResidualEdges.filter
        fun e => e ∈ G.endpointPairCell u v).card :=
      congrArg Finset.card hmap
    _ ≤ (G.floorResidualEdges.filter
        fun e => e ∈ G.floorBundle (G.floorPairKey u v)).card :=
      Finset.card_le_card hsub
    _ ≤ R := hR _

/-- A fixed bound on the number of distinct weights and their reciprocal
integer parts bounds the actual physical coefficient-floor residue. -/
theorem card_floorResidual_bundle_le_uniform
    (D T : ℕ)
    (hD : ∀ k : G.V × G.V,
      Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤ D)
    (hT : ∀ e : G.E, Nat.floor (1 / G.weight e) ≤ T)
    (k : G.V × G.V) :
    (G.floorResidualEdges.filter fun e => e ∈ G.floorBundle k).card ≤
      D * ((T + 1) ^ D * T) := by
  have hlocal : ∀ x : G.EdgeSetWeightType (G.floorBundle k),
      Nat.floor (1 /
        (G.edgeSetWeightBinPackingInstance (G.floorBundle k)).weight x) ≤ T := by
    intro x
    obtain ⟨e, _he, heq⟩ := Finset.mem_image.mp x.2
    simpa [← heq] using hT e
  have hcover := (G.floorBundleCover k).sum_floorResidualDemand_le_card_mul_succ_pow_card_mul
    T hlocal
  have htypes := hD k
  have hpow : (T + 1) ^
      Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤
      (T + 1) ^ D := by
    exact Nat.pow_le_pow_right (by omega) htypes
  calc
    _ ≤ ∑ x : G.EdgeSetWeightType (G.floorBundle k),
          (G.floorBundleCover k).floorResidualDemand x :=
      G.card_floorResidual_bundle_le_sum k
    _ ≤ Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) *
          ((T + 1) ^ Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) * T) :=
      hcover
    _ ≤ D * ((T + 1) ^ D * T) := by
      exact Nat.mul_le_mul htypes (Nat.mul_le_mul_right T hpow)

/-- The same constant controls each original endpoint pair. -/
theorem floorResidualGraph_pairMultiplicityAtMost_of_boundedTypes
    (D T : ℕ)
    (hD : ∀ k : G.V × G.V,
      Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤ D)
    (hT : ∀ e : G.E, Nat.floor (1 / G.weight e) ≤ T) :
    (G.edgeRestriction G.floorResidualEdges).PairMultiplicityAtMost
      (D * ((T + 1) ^ D * T)) := by
  intro u v
  let H := G.edgeRestriction G.floorResidualEdges
  let emb : H.E ↪ G.E := ⟨Subtype.val, Subtype.val_injective⟩
  let F := H.endpointPairCell u v
  have hmap : F.map emb =
      G.floorResidualEdges.filter fun e => e ∈ G.endpointPairCell u v := by
    ext e
    simp [F, emb, H, WeightedMultigraph.endpointPairCell,
      WeightedMultigraph.endpoints, and_comm]
  have hsub :
      G.floorResidualEdges.filter (fun e => e ∈ G.endpointPairCell u v) ⊆
        G.floorResidualEdges.filter
          (fun e => e ∈ G.floorBundle (G.floorPairKey u v)) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨he'.1, ?_⟩
    exact (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        G.floorKey_eq_floorPairKey_of_mem_endpointPairCell he'.2⟩)
  calc
    F.card = (F.map emb).card := (Finset.card_map emb).symm
    _ = (G.floorResidualEdges.filter
        fun e => e ∈ G.endpointPairCell u v).card :=
      congrArg Finset.card hmap
    _ ≤ (G.floorResidualEdges.filter
        fun e => e ∈ G.floorBundle (G.floorPairKey u v)).card :=
      Finset.card_le_card hsub
    _ ≤ D * ((T + 1) ^ D * T) :=
      G.card_floorResidual_bundle_le_uniform D T hD hT _

variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- Contracting blocks of at most five vertices multiplies the bounded-type
coefficient-floor residual pair bound by at most 25. -/
theorem floorResidualQuotient_pairMultiplicityAtMost_of_boundedTypes
    (D T : ℕ) (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    (hD : ∀ k : G.V × G.V,
      Fintype.card (G.EdgeSetWeightType (G.floorBundle k)) ≤ D)
    (hT : ∀ e : G.E, Nat.floor (1 / G.weight e) ≤ T) :
    ((G.edgeRestriction G.floorResidualEdges).subtwoQuotient block).PairMultiplicityAtMost
      (25 * (D * ((T + 1) ^ D * T))) := by
  exact G.edgeRestriction_subtwoQuotient_pairMultiplicityAtMost_five
    G.floorResidualEdges block hfiber
    (G.floorResidualGraph_pairMultiplicityAtMost_of_boundedTypes D T hD hT)

end
end WeightedEdgeColoring.WeightedMultigraph
