import WeightedEdgeColoring.SubtwoTinyBlockAmbientLift

/-! Each selected block's internal mixed objects split exactly into its
endpoint-simple small objects and retained core objects. -/

namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

def internalObjects (n : ℕ) : Finset P.Object :=
  Finset.univ.filter (fun o =>
    P.mixedObjectGraph.subtwoFloorBlock n (P.mixedObjectGraph.fst o) =
      P.mixedObjectGraph.subtwoFloorBlock n (P.mixedObjectGraph.snd o))

def objectOwner (n : ℕ) (o : P.Object) :
    (P.mixedObjectGraph.subtwoFloorQuotient n).V :=
  P.mixedObjectGraph.subtwoFloorBlock n (P.mixedObjectGraph.fst o)

theorem internalObjects_owner_inc
    (n : ℕ) (o : P.Object) (ho : o ∈ P.internalObjects n)
    (v : G.V) (hv : P.mixedObjectGraph.Inc v o) :
    P.objectOwner n o = P.mixedObjectGraph.subtwoFloorBlock n v := by
  have hi := (Finset.mem_filter.mp ho).2
  rcases hv with h | h
  · simp [objectOwner, ← h]
  · simp [objectOwner, ← h, hi]

theorem internalObjects_owner_filter_eq
    (n : ℕ) (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V) :
    (P.internalObjects n).filter (fun o => P.objectOwner n o = b) =
      (Finset.univ : Finset P.Object).filter (fun o =>
        P.mixedObjectGraph.fst o ∈
          P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
            (P.mixedObjectGraph.subtwoFloorBlock n) b ∧
        P.mixedObjectGraph.snd o ∈
          P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
            (P.mixedObjectGraph.subtwoFloorBlock n) b) := by
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, internalObjects,
    objectOwner]
  simp only [WeightedMultigraph.mem_subtwoFiber]
  constructor
  · rintro ⟨hi, hb⟩
    exact ⟨hb, hi.symm.trans hb⟩
  · rintro ⟨hf, hs⟩
    exact ⟨hf.trans hs.symm, hf⟩

theorem internalObjects_owner_filter_partition
    (n : ℕ) (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V) :
    let H := P.mixedObjectGraph
    let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
    let R : Finset (H.vertexRestriction T).E :=
      Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
    let J := (H.vertexRestriction T).edgeRestriction R
    (P.internalObjects n).filter (fun o => P.objectOwner n o = b) =
      (P.smallInternalObjects T).image Subtype.val ∪
        (Finset.univ : Finset J.E).image (fun e => e.val.val) := by
  classical
  dsimp only
  let H := P.mixedObjectGraph
  let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction T).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  let J := (H.vertexRestriction T).edgeRestriction R
  rw [P.internalObjects_owner_filter_eq n b]
  ext o
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_image]
  constructor
  · rintro ⟨hf, hs⟩
    by_cases hsmall : o ∈ P.smallObjects
    · left
      refine ⟨⟨o,hsmall⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hf,hs⟩⟩
    · right
      have hcore : o ∈ P.coreObjects :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hsmall⟩
      let e : (H.vertexRestriction T).E := ⟨o,⟨hf,hs⟩⟩
      have he : e ∈ R :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcore⟩
      exact ⟨(⟨e,he⟩ : J.E), rfl⟩
  · rintro (⟨o',ho',rfl⟩ | ⟨o',ho',rfl⟩)
    · exact (Finset.mem_filter.mp ho').2
    · exact o'.val.2

theorem internalObjects_owner_filter_empty_of_rank_zero
    {n : ℕ} (hn : 0 < n) (hlocal : P.mixedObjectGraph.LocallyPacksInto n)
    (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (hrank : P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFinalRank
      (P.mixedObjectGraph.subtwoFloorCost n) b = 0) :
    (P.internalObjects n).filter (fun o => P.objectOwner n o = b) = ∅ := by
  let H := P.mixedObjectGraph
  let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  have hcard := H.floorPacketization.groupedGraph.subtwoFinalBlock_fiber_card
    (H.subtwoFloorCost n) (H.subtwoFloorCost_nonneg n)
    (H.subtwoFloorCost_pair_le hn hlocal) (H.subtwoFloorCost_degree_le hn hlocal) b
  change T.card = 1 + 2 *
    H.floorPacketization.groupedGraph.subtwoFinalRank (H.subtwoFloorCost n) b at hcard
  rw [hrank] at hcard
  have hT : T.card = 1 := by omega
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hT
  rw [P.internalObjects_owner_filter_eq n b]
  by_contra hne
  obtain ⟨o,ho⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hf,hs⟩ := (Finset.mem_filter.mp ho).2
  change H.fst o ∈ T at hf
  change H.snd o ∈ T at hs
  rw [hv] at hf hs
  have hfv : H.fst o = v := by simpa using hf
  have hsv : H.snd o = v := by simpa using hs
  have heq : H.fst o = H.snd o := hfv.trans hsv.symm
  exact H.noLoop o heq

theorem internalObjects_owner_leftover_split
    (n : ℕ) (b : (P.mixedObjectGraph.subtwoFloorQuotient n).V)
    (A : Finset
      (((P.mixedObjectGraph.vertexRestriction
        (P.mixedObjectGraph.floorPacketization.groupedGraph.subtwoFiber
          (P.mixedObjectGraph.subtwoFloorBlock n) b)).edgeRestriction
          (Finset.univ.filter (fun e => e.val ∈ P.coreObjects))).E))
    (v : G.V) :
    let H := P.mixedObjectGraph
    let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
    let R : Finset (H.vertexRestriction T).E :=
      Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
    let J := (H.vertexRestriction T).edgeRestriction R
    let edge : J.E → H.E := fun e => e.val.val
    (∑ e ∈ ((P.internalObjects n).filter (fun o => P.objectOwner n o = b)) \
        A.image edge,
      if H.Inc v e then H.weight e else 0) =
      (∑ o ∈ P.smallInternalObjects T,
        if H.Inc v o.1 then H.weight o.1 else 0) +
      (∑ e ∈ (Finset.univ.image edge) \ (A.image edge),
        if H.Inc v e then H.weight e else 0) := by
  classical
  dsimp only
  let H := P.mixedObjectGraph
  let T := H.floorPacketization.groupedGraph.subtwoFiber (H.subtwoFloorBlock n) b
  let R : Finset (H.vertexRestriction T).E :=
    Finset.univ.filter (fun e => e.val ∈ P.coreObjects)
  let J := (H.vertexRestriction T).edgeRestriction R
  let edge : J.E → H.E := fun e => e.val.val
  let small : Finset H.E := (P.smallInternalObjects T).image Subtype.val
  let core : Finset H.E := Finset.univ.image edge
  have hpart : (P.internalObjects n).filter (fun o => P.objectOwner n o = b) =
      small ∪ core := P.internalObjects_owner_filter_partition n b
  have hdis : Disjoint small core := by
    apply Finset.disjoint_left.mpr
    intro o hoSmall hoCore
    obtain ⟨s,hs,heqs⟩ := Finset.mem_image.mp hoSmall
    obtain ⟨c,_,heqc⟩ := Finset.mem_image.mp hoCore
    have hsmall : o ∈ P.smallObjects := heqs ▸ s.2
    have hcore : o ∈ P.coreObjects := by
      rw [← heqc]
      exact (Finset.mem_filter.mp c.2).2
    exact (P.smallObject_not_core hsmall) hcore
  have hsub : A.image edge ⊆ core := Finset.image_subset_image
    (Finset.subset_univ A)
  have hsd : Disjoint small (A.image edge) := hdis.mono_right hsub
  have hsplit : (small ∪ core) \ A.image edge =
      small ∪ (core \ A.image edge) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hs|hc,ha⟩
      · exact Or.inl hs
      · exact Or.inr ⟨hc,ha⟩
    · rintro (hs|⟨hc,ha⟩)
      · exact ⟨Or.inl hs, (Finset.disjoint_left.mp hsd) hs⟩
      · exact ⟨Or.inr hc,ha⟩
  have hdis' : Disjoint small (core \ A.image edge) :=
    hdis.mono_right (by intro e he; exact (Finset.mem_sdiff.mp he).1)
  calc
    _ = ∑ e ∈ small ∪ (core \ A.image edge),
        if H.Inc v e then H.weight e else 0 := by
          rw [hpart, hsplit]
          rfl
    _ = (∑ e ∈ small, if H.Inc v e then H.weight e else 0) +
        (∑ e ∈ core \ A.image edge, if H.Inc v e then H.weight e else 0) :=
          Finset.sum_union hdis'
    _ = _ := by
      congr 1
      rw [Finset.sum_image]
      intro a _ b _ h
      exact Subtype.val_injective h

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
