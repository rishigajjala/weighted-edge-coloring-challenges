import WeightedEdgeColoring.SubtwoPacketQuotientBase
import WeightedEdgeColoring.BPGeneralFloorPacketBase
import WeightedEdgeColoring.SubtwoBundleCharge
import WeightedEdgeColoring.SubtwoPacketLabelCounts
import WeightedEdgeColoring.SubtwoExteriorChargeSum

/-! Selected crossing packet colors and residual crossing physical edges are
charged to the same original exterior harmonic star. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}}
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

/-- A crossing edge has exactly one original endpoint in each incident
block. This elementary identity is the aggregation bridge for both packet
counts and physical charges. -/
theorem crossingEdge_sum_incidence_fiber
    (G : WeightedMultigraph.{u}) (block : G.V → Q) (q : Q)
    (e : G.E) (he : block (G.fst e) ≠ block (G.snd e)) (a : ℝ) :
    (∑ v ∈ G.subtwoFiber block q,
      if G.Inc v e then a else 0) =
      if (G.subtwoQuotient block).Inc q (⟨e, he⟩) then a else 0 := by
  classical
  by_cases hf : block (G.fst e) = q
  · have hs : block (G.snd e) ≠ q := by
      intro hsq
      exact he (hf.trans hsq.symm)
    have hmem : G.fst e ∈ G.subtwoFiber block q :=
      (G.mem_subtwoFiber block q _).2 hf
    rw [Finset.sum_eq_single (G.fst e)]
    · have hi : G.Inc (G.fst e) e := Or.inl rfl
      have hq : (G.subtwoQuotient block).Inc q (⟨e, he⟩) := Or.inl hf
      simp [hi, hq]
    · intro v hv hne
      have hvq := (G.mem_subtwoFiber block q v).1 hv
      by_cases hi : G.Inc v e
      · rcases hi with hfst | hsnd
        · exact False.elim (hne hfst.symm)
        · exact False.elim (hs ((congrArg block hsnd).trans hvq))
      · simp [hi]
    · intro hnot
      exact False.elim (hnot hmem)
  · by_cases hs : block (G.snd e) = q
    · have hmem : G.snd e ∈ G.subtwoFiber block q :=
        (G.mem_subtwoFiber block q _).2 hs
      rw [Finset.sum_eq_single (G.snd e)]
      · have hi : G.Inc (G.snd e) e := Or.inr rfl
        have hq : (G.subtwoQuotient block).Inc q (⟨e, he⟩) := Or.inr hs
        simp [hi, hq]
      · intro v hv hne
        have hvq := (G.mem_subtwoFiber block q v).1 hv
        by_cases hi : G.Inc v e
        · rcases hi with hfst | hsnd
          · exact False.elim (hf ((congrArg block hfst).trans hvq))
          · exact False.elim (hne hsnd.symm)
        · simp [hi]
      · intro hnot
        exact False.elim (hnot hmem)
    · have hzero :
          (∑ v ∈ G.subtwoFiber block q,
            if G.Inc v e then a else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro v hv
        have hvq := (G.mem_subtwoFiber block q v).1 hv
        have hnot : ¬G.Inc v e := by
          rintro (hfst | hsnd)
          · exact hf ((congrArg block hfst).trans hvq)
          · exact hs ((congrArg block hsnd).trans hvq)
        simp [hnot]
      rw [hzero]
      have hnot : ¬(G.subtwoQuotient block).Inc q (⟨e, he⟩) := by
        rintro (hfst | hsnd)
        · exact hf hfst
        · exact hs hsnd
      simp [hnot]

theorem quotientCharge_eq_sum_fiberCharge
    (G : WeightedMultigraph.{u}) (block : G.V → Q) (q : Q)
    (F : Finset G.E) (charge : ℝ → ℝ)
    (hcross : ∀ e ∈ F, block (G.fst e) ≠ block (G.snd e)) :
    (G.subtwoQuotient block).chargeOn charge
        (G.subtwoQuotientSelectedEdges block F) q =
      ∑ v ∈ G.subtwoFiber block q, G.chargeOn charge F v := by
  classical
  let H := G.subtwoQuotient block
  have hleft :
      H.chargeOn charge (G.subtwoQuotientSelectedEdges block F) q =
        ∑ e : G.E, if block (G.fst e) ≠ block (G.snd e) then
          (if e ∈ F then
            (if block (G.fst e) = q ∨ block (G.snd e) = q then
              charge (G.weight e) else 0) else 0) else 0 := by
    unfold chargeOn
    change (∑ e ∈ (Finset.univ : Finset H.E).filter (fun e => e.1 ∈ F),
      if H.Inc q e then charge (H.weight e) else 0) = _
    rw [Finset.sum_filter]
    simpa only [H, subtwoQuotient] using
      (G.subtwo_sum_quotient_edges block
        (fun e => if e ∈ F then
          (if block (G.fst e) = q ∨ block (G.snd e) = q then
            charge (G.weight e) else 0) else 0))
  have hright :
      (∑ v ∈ G.subtwoFiber block q, G.chargeOn charge F v) =
        ∑ e : G.E, if block (G.fst e) ≠ block (G.snd e) then
          (if e ∈ F then
            (if block (G.fst e) = q ∨ block (G.snd e) = q then
              charge (G.weight e) else 0) else 0) else 0 := by
    unfold chargeOn
    rw [Finset.sum_comm]
    calc
      (∑ e ∈ F, ∑ v ∈ G.subtwoFiber block q,
        if G.Inc v e then charge (G.weight e) else 0) =
          ∑ e ∈ F, if block (G.fst e) = q ∨ block (G.snd e) = q then
            charge (G.weight e) else 0 := by
        apply Finset.sum_congr rfl
        intro e heF
        simpa only [subtwoQuotient] using
          G.crossingEdge_sum_incidence_fiber block q e (hcross e heF)
            (charge (G.weight e))
      _ = ∑ e : G.E, if e ∈ F then
          (if block (G.fst e) = q ∨ block (G.snd e) = q then
            charge (G.weight e) else 0) else 0 := by
        calc
          (∑ e ∈ F, if block (G.fst e) = q ∨ block (G.snd e) = q then
            charge (G.weight e) else 0) =
              ∑ e ∈ F, if e ∈ F then
                (if block (G.fst e) = q ∨ block (G.snd e) = q then
                  charge (G.weight e) else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro e heF
            simp [heF]
          _ = _ := by
            apply Finset.sum_subset (Finset.subset_univ F)
            intro e _ heF
            simp [heF]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases heF : e ∈ F
        · simp [heF, hcross e heF]
        · simp [heF]
  rw [hleft, hright]

theorem chargeOn_one_eq_degreeOn (G : WeightedMultigraph.{u})
    (F : Finset G.E) (v : G.V) :
    G.chargeOn (fun _ => 1) F v = (G.degreeOn F v : ℝ) := by
  unfold chargeOn degreeOn
  rw [← Finset.sum_filter]
  simp

namespace Packetization
variable (P : G.Packetization)

/-- At a contracted vertex, this is the original endpoint represented by a
crossing packet. Only incident packets are counted below. -/
def quotientOriginalEndpointLabel (block : G.V → Q) (q : Q)
    (p : (P.groupedGraph.subtwoQuotient block).E) : G.V :=
  if block (P.tail p.1) = q then P.tail p.1 else P.head p.1

theorem quotientOriginalEndpointLabel_eq_iff_inc
    (block : G.V → Q) (q : Q)
    (p : (P.groupedGraph.subtwoQuotient block).E)
    (v : G.V) (hv : block v = q)
    (hpq : (P.groupedGraph.subtwoQuotient block).Inc q p) :
    P.quotientOriginalEndpointLabel block q p = v ↔
      P.groupedGraph.Inc v p.1 := by
  change block (P.tail p.1) = q ∨ block (P.head p.1) = q at hpq
  change P.quotientOriginalEndpointLabel block q p = v ↔
    (P.tail p.1 = v ∨ P.head p.1 = v)
  unfold quotientOriginalEndpointLabel
  by_cases ht : block (P.tail p.1) = q
  · have hh : block (P.head p.1) ≠ q := by
      intro he
      exact p.2 (ht.trans he.symm)
    simp only [if_pos ht]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact False.elim (hh ((congrArg block h).trans hv))
  · have hh := hpq.resolve_left ht
    simp only [if_neg ht]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact False.elim (ht ((congrArg block h).trans hv))
      · exact h

theorem card_usedQuotientPacketColors_originalEndpoint
    (block : G.V → Q) (S : Finset P.Packet)
    {k : ℕ} (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    (q : Q) (v : G.V) (hv : block v = q) :
    ((P.groupedGraph.subtwoQuotient block).subtwoUsedPacketLabelColors
      (P.groupedGraph.subtwoQuotientSelectedEdges block S)
      color (P.quotientOriginalEndpointLabel block) q v).card =
    P.groupedGraph.degreeOn
      (P.groupedGraph.subtwoCrossingSelectedEdges block S) v := by
  classical
  rw [(P.groupedGraph.subtwoQuotient block).card_subtwoUsedPacketLabelColors
    (P.groupedGraph.subtwoQuotientSelectedEdges block S) color hproper
    (P.quotientOriginalEndpointLabel block) q v]
  unfold WeightedMultigraph.degreeOn
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    have h := Finset.mem_filter.mp hp
    have hpS : p.1 ∈ S := (Finset.mem_filter.mp h.1).2
    have hpq : (P.groupedGraph.subtwoQuotient block).Inc q p := h.2.1
    have hlabel : P.quotientOriginalEndpointLabel block q p = v := h.2.2
    have hvinc : P.groupedGraph.Inc v p.1 :=
      (P.quotientOriginalEndpointLabel_eq_iff_inc block q p v hv hpq).1 hlabel
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hpS, p.2⟩, hvinc⟩
  · intro p hp r hr heq
    exact Subtype.ext heq
  · intro p hp
    have h := Finset.mem_filter.mp hp
    have hpS : p ∈ S := (Finset.mem_filter.mp h.1).1
    have hcross : block (P.tail p) ≠ block (P.head p) :=
      (Finset.mem_filter.mp h.1).2
    have hvinc : P.groupedGraph.Inc v p := h.2
    let p' : (P.groupedGraph.subtwoQuotient block).E := ⟨p, hcross⟩
    have hpq : (P.groupedGraph.subtwoQuotient block).Inc q p' := by
      change block (P.tail p) = q ∨ block (P.head p) = q
      rcases hvinc with ht | hh
      · exact Or.inl ((congrArg block ht).trans hv)
      · exact Or.inr ((congrArg block hh).trans hv)
    refine ⟨p', ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpS⟩, hpq, ?_⟩
    exact (P.quotientOriginalEndpointLabel_eq_iff_inc
      block q p' v hv hpq).2 hvinc

theorem sum_usedQuotientPacketColors_eq_degree
    (block : G.V → Q) (S : Finset P.Packet)
    {k : ℕ} (color : (P.groupedGraph.subtwoQuotient block).E → Fin k)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    (q : Q) :
    (∑ v ∈ G.subtwoFiber block q,
      (((P.groupedGraph.subtwoQuotient block).subtwoUsedPacketLabelColors
        (P.groupedGraph.subtwoQuotientSelectedEdges block S)
        color (P.quotientOriginalEndpointLabel block) q v).card : ℝ)) =
      ((P.groupedGraph.subtwoQuotient block).degreeOn
        (P.groupedGraph.subtwoQuotientSelectedEdges block S) q : ℝ) := by
  classical
  have hcount :
      (∑ v ∈ G.subtwoFiber block q,
        (((P.groupedGraph.subtwoQuotient block).subtwoUsedPacketLabelColors
          (P.groupedGraph.subtwoQuotientSelectedEdges block S)
          color (P.quotientOriginalEndpointLabel block) q v).card : ℝ)) =
        ∑ v ∈ G.subtwoFiber block q,
          (P.groupedGraph.degreeOn
            (P.groupedGraph.subtwoCrossingSelectedEdges block S) v : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact_mod_cast P.card_usedQuotientPacketColors_originalEndpoint
      block S color hproper q v ((G.mem_subtwoFiber block q v).1 hv)
  rw [hcount]
  let Scross := P.groupedGraph.subtwoCrossingSelectedEdges block S
  have hcross : ∀ p ∈ Scross,
      block (P.groupedGraph.fst p) ≠ block (P.groupedGraph.snd p) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hqsel : P.groupedGraph.subtwoQuotientSelectedEdges block Scross =
      P.groupedGraph.subtwoQuotientSelectedEdges block S := by
    ext p
    simp [Scross, subtwoQuotientSelectedEdges, subtwoCrossingSelectedEdges,
      p.2]
  have hsum := P.groupedGraph.quotientCharge_eq_sum_fiberCharge
    block q Scross (fun _ => 1) hcross
  rw [hqsel, (P.groupedGraph.subtwoQuotient block).chargeOn_one_eq_degreeOn] at hsum
  simp_rw [P.groupedGraph.chargeOn_one_eq_degreeOn] at hsum
  exact hsum.symm

theorem crossing_originalEdgesOfPackets (block : G.V → Q)
    (S : Finset P.Packet) :
    P.originalEdgesOfPackets
        (P.groupedGraph.subtwoCrossingSelectedEdges block S) =
      G.subtwoCrossingSelectedEdges block (P.originalEdgesOfPackets S) := by
  classical
  ext e
  simp [originalEdgesOfPackets, subtwoCrossingSelectedEdges]
  intro _
  exact P.packetOf_crossing_iff block e

/-- Each selected packet carrying at least one harmonic unit pays for one
occupied packet color at every incident original vertex. -/
theorem selectedDegree_le_harmonicCharge
    (S : Finset P.Packet)
    (hpacket : ∀ p ∈ S, 1 ≤ P.packetCharge harmonicCharge p)
    (v : G.V) :
    (P.groupedGraph.degreeOn S v : ℝ) ≤
      G.chargeOn harmonicCharge (P.originalEdgesOfPackets S) v := by
  rw [P.chargeOn_originalEdgesOfPackets harmonicCharge S v]
  unfold WeightedMultigraph.degreeOn
  calc
    ((S.filter (P.groupedGraph.Inc v)).card : ℝ) =
        ∑ p ∈ S.filter (P.groupedGraph.Inc v), (1 : ℝ) := by simp
    _ ≤ ∑ p ∈ S.filter (P.groupedGraph.Inc v),
        P.packetCharge harmonicCharge p := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpacket p (Finset.mem_filter.mp hp).1
    _ = ∑ p ∈ S,
        if P.groupedGraph.Inc v p
          then P.packetCharge harmonicCharge p else 0 := by
      rw [Finset.sum_filter]
      rfl

theorem crossingSelectedDegree_add_residualCharge_le
    (block : G.V → Q) (S : Finset P.Packet)
    (hpacket : ∀ p ∈ S, 1 ≤ P.packetCharge harmonicCharge p)
    (v : G.V) :
    let Fcross := G.subtwoCrossingSelectedEdges block Finset.univ
    let Fsel := P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S)
    (P.groupedGraph.degreeOn
        (P.groupedGraph.subtwoCrossingSelectedEdges block S) v : ℝ) +
      G.chargeOn harmonicCharge (Fcross \ Fsel) v ≤
        G.chargeOn harmonicCharge Fcross v := by
  dsimp only
  let Scross := P.groupedGraph.subtwoCrossingSelectedEdges block S
  let Fcross := G.subtwoCrossingSelectedEdges block Finset.univ
  let Fsel := P.originalEdgesOfPackets Scross
  have hsel : (P.groupedGraph.degreeOn Scross v : ℝ) ≤
      G.chargeOn harmonicCharge Fsel v := by
    apply P.selectedDegree_le_harmonicCharge Scross
    intro p hp
    exact hpacket p (Finset.mem_filter.mp hp).1
  have hsubset : Fsel ⊆ Fcross := by
    intro e he
    change e ∈ P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S) at he
    rw [P.crossing_originalEdgesOfPackets block S] at he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩
  have hdisj : Disjoint Fsel (Fcross \ Fsel) := by
    rw [Finset.disjoint_left]
    intro e heF heR
    exact (Finset.mem_sdiff.mp heR).2 heF
  have hunion : Fsel ∪ (Fcross \ Fsel) = Fcross :=
    Finset.union_sdiff_of_subset hsubset
  calc
    (P.groupedGraph.degreeOn Scross v : ℝ) +
        G.chargeOn harmonicCharge (Fcross \ Fsel) v ≤
      G.chargeOn harmonicCharge Fsel v +
        G.chargeOn harmonicCharge (Fcross \ Fsel) v :=
      add_le_add hsel le_rfl
    _ = G.chargeOn harmonicCharge (Fsel ∪ (Fcross \ Fsel)) v :=
      (G.chargeOn_union hdisj v).symm
    _ = G.chargeOn harmonicCharge Fcross v := by rw [hunion]

end Packetization

theorem crossingCharge_eq_exteriorCharge (G : WeightedMultigraph.{u})
    (block : G.V → Q) (v : G.V) :
    G.chargeOn harmonicCharge
      (G.subtwoCrossingSelectedEdges block Finset.univ) v =
    G.subtwoExteriorHarmonicCharge
      (G.subtwoFiber block (block v)) v := by
  classical
  unfold chargeOn subtwoExteriorHarmonicCharge
  change
    (∑ e ∈ Finset.univ.filter
      (fun e : G.E => block (G.fst e) ≠ block (G.snd e)),
        if G.Inc v e then harmonicCharge (G.weight e) else 0) = _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : G.Inc v e
  · have hcross :
        (block (G.fst e) ≠ block (G.snd e)) ↔
          ¬(G.fst e ∈ G.subtwoFiber block (block v) ∧
            G.snd e ∈ G.subtwoFiber block (block v)) := by
      rcases hi with hf | hs
      · simp [G.mem_subtwoFiber, hf, ne_comm]
      · simp [G.mem_subtwoFiber, hs, ne_comm]
    simp [subtwoCrossingSelectedEdges, hi, hcross]
  · simp [subtwoCrossingSelectedEdges, hi]

/-- The floor-packet base consumes at most the physical exterior harmonic
charge of each original endpoint. -/
theorem subtwoFloor_crossingPacketDegree_add_residualCharge_le
    (G : WeightedMultigraph.{u}) (n : ℕ) (v : G.V) :
    let block := G.subtwoFloorBlock n
    let S := G.fullFloorPacketSet
    let Fcross := G.subtwoCrossingSelectedEdges block Finset.univ
    let Fsel := G.floorPacketization.originalEdgesOfPackets
      (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges block S)
    (G.floorPacketization.groupedGraph.degreeOn
      (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges block S) v : ℝ) +
      G.chargeOn harmonicCharge (Fcross \ Fsel) v ≤
        G.subtwoExteriorHarmonicCharge
          (G.subtwoFiber block (block v)) v := by
  dsimp only
  have h := G.floorPacketization.crossingSelectedDegree_add_residualCharge_le
    (G.subtwoFloorBlock n) G.fullFloorPacketSet (by
      intro p hp
      rw [← G.harmonicFullFloorPacketSet_eq_fullFloorPacketSet] at hp
      exact G.one_le_packetCharge_of_mem_harmonicFullFloorPacketSet hp) v
  dsimp only at h
  rw [G.crossingCharge_eq_exteriorCharge (G.subtwoFloorBlock n) v] at h
  exact h

/-- In the actual selected quotient coloring, packet colors carrying one
original endpoint label plus the uncolored exterior harmonic charge are
bounded by that endpoint's original exterior harmonic charge. -/
theorem subtwoFloor_originalLabelColors_add_residualCharge_le
    (G : WeightedMultigraph.{u}) (n : ℕ)
    {k : ℕ} (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color)
    (q : (G.subtwoFloorQuotient n).V) (v : G.V)
    (hv : G.subtwoFloorBlock n v = q) :
    let block := G.subtwoFloorBlock n
    let Fcross := G.subtwoCrossingSelectedEdges block Finset.univ
    let Fsel := G.floorPacketization.originalEdgesOfPackets
      (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
        block G.fullFloorPacketSet)
    (((G.subtwoFloorQuotient n).subtwoUsedPacketLabelColors
      (G.subtwoFloorQuotientEdges n) color
      (G.floorPacketization.quotientOriginalEndpointLabel block) q v).card : ℝ) +
        G.chargeOn harmonicCharge (Fcross \ Fsel) v ≤
      G.subtwoExteriorHarmonicCharge (G.subtwoFiber block q) v := by
  dsimp only
  have hcount := G.floorPacketization.card_usedQuotientPacketColors_originalEndpoint
    (G.subtwoFloorBlock n) G.fullFloorPacketSet color hproper q v hv
  have hcharge := G.subtwoFloor_crossingPacketDegree_add_residualCharge_le n v
  dsimp only at hcharge
  simp only [subtwoFloorQuotient, subtwoFloorQuotientEdges]
  rw [hcount]
  rw [← hv]
  exact hcharge

/-- The actual block boundary has at most the original harmonic constant's
charge. Higher-rank blocks only reduce this bound. -/
theorem subtwoFloorBlock_exterior_harmonic_le_M
    (G : WeightedMultigraph.{u}) {n : ℕ}
    (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V) :
    G.subtwoBoundaryCost (fun e ↦ harmonicCharge (G.weight e))
      (G.floorPacketization.groupedGraph.subtwoFiber
        (G.subtwoFloorBlock n) q) ≤ subtwoM * n := by
  have h := G.subtwoFloorBlock_boundary_harmonic_le hn hlocal q
  dsimp only at h
  have hr :
      (0 : ℝ) ≤
        (G.floorPacketization.groupedGraph.subtwoFinalRank
          (G.subtwoFloorCost n) q : ℝ) := Nat.cast_nonneg _
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold subtwoM at h ⊢
  unfold subtwoKappa at h
  nlinarith [mul_nonneg hr hnR]

/-- A palette padded to the sub-two base target leaves a quarter-bin reserve
after the actual harmonic exterior charge is paid. -/
theorem subtwoFloor_exteriorReserve_quarter
    {n K : ℕ} {occupied residual Missing : ℝ}
    (hK : subtwoKappa * n ≤ K)
    (hcharge : occupied + residual ≤ subtwoM * n)
    (hmissing : Missing = K - occupied) :
    residual + (1 / 4 : ℝ) * n ≤ Missing := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [hmissing]
  unfold subtwoKappa at hK
  unfold subtwoM at hcharge
  nlinarith

/-- Summing the endpoint-label accounting over an actual block charges all
used packet labels and uncolored crossing physical weight to the original
block boundary, hence to `M n`. -/
theorem subtwoFloor_originalLabelBudget_block
    (G : WeightedMultigraph.{u}) {n k : ℕ}
    (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color)
    (q : (G.subtwoFloorQuotient n).V) :
    let block := G.subtwoFloorBlock n
    let fiber := G.subtwoFiber block q
    let Fcross := G.subtwoCrossingSelectedEdges block Finset.univ
    let Fsel := G.floorPacketization.originalEdgesOfPackets
      (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
        block G.fullFloorPacketSet)
    (∑ v ∈ fiber,
      (((G.subtwoFloorQuotient n).subtwoUsedPacketLabelColors
        (G.subtwoFloorQuotientEdges n) color
        (G.floorPacketization.quotientOriginalEndpointLabel block) q v).card : ℝ)) +
      (∑ v ∈ fiber,
        G.chargeOn harmonicCharge (Fcross \ Fsel) v) ≤ subtwoM * n := by
  dsimp only
  let fiber := G.subtwoFiber (G.subtwoFloorBlock n) q
  have hlocalBudget : ∀ v ∈ fiber,
      (((G.subtwoFloorQuotient n).subtwoUsedPacketLabelColors
        (G.subtwoFloorQuotientEdges n) color
        (G.floorPacketization.quotientOriginalEndpointLabel
          (G.subtwoFloorBlock n)) q v).card : ℝ) +
        G.chargeOn harmonicCharge
          (G.subtwoCrossingSelectedEdges (G.subtwoFloorBlock n) Finset.univ \
            G.floorPacketization.originalEdgesOfPackets
              (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
                (G.subtwoFloorBlock n) G.fullFloorPacketSet)) v ≤
        G.subtwoExteriorHarmonicCharge fiber v := by
    intro v hv
    have hblock := (G.mem_subtwoFiber (G.subtwoFloorBlock n) q v).1 hv
    exact G.subtwoFloor_originalLabelColors_add_residualCharge_le
      n color hproper q v hblock
  have hsum := Finset.sum_le_sum (fun v hv => hlocalBudget v hv)
  rw [Finset.sum_add_distrib] at hsum
  have hexterior := G.sum_subtwoExteriorHarmonicCharge fiber
  have hboundary := G.subtwoFloorBlock_exterior_harmonic_le_M hn hlocal q
  change (∑ v ∈ fiber, G.subtwoExteriorHarmonicCharge fiber v) =
    G.subtwoBoundaryCost (fun e ↦ harmonicCharge (G.weight e)) fiber at hexterior
  rw [hexterior] at hsum
  exact hsum.trans hboundary

end
end WeightedEdgeColoring.WeightedMultigraph
