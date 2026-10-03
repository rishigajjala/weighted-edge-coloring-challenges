import WeightedEdgeColoring.SubtwoPacketQuotientCharge
import WeightedEdgeColoring.SubtwoQuotientSplitInflation

/-! The physical floor quotient has the quarter-bin harmonic reserve. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
set_option maxHeartbeats 1000000 in
noncomputable section
universe u

/-- The unselected physical quotient edges are exactly the crossing
original edges not covered by selected crossing floor packets. -/
private theorem subtwoFloorPhysicalResidualEdges_eq
    (G : WeightedMultigraph.{u}) {n k : ℕ} (hk : 0 < k)
    (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color) :
    let block := G.subtwoFloorBlock n
    let Fcross := G.subtwoCrossingSelectedEdges block Finset.univ
    let Fsel := G.floorPacketization.originalEdgesOfPackets
      (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
        block G.fullFloorPacketSet)
    (G.subtwoFloorPhysicalColoredPacketBase hk n color hproper).residualEdges =
      G.subtwoQuotientSelectedEdges block (Fcross \ Fsel) := by
  classical
  dsimp only
  change Finset.univ \
    (G.subtwoFloorPhysicalColoredPacketBase hk n color hproper).fullEdges = _
  rw [G.subtwoFloorPhysicalColoredPacketBase_fullEdges hk n color hproper]
  rw [G.floorPacketization.crossing_originalEdgesOfPackets]
  rw [show G.subtwoFloorBaseEdges n =
      G.subtwoCrossingSelectedEdges (G.subtwoFloorBlock n)
        (G.floorPacketization.originalEdgesOfPackets G.fullFloorPacketSet) from
    G.floorPacketization.crossing_originalEdgesOfPackets _ _]
  ext e
  simp [subtwoQuotientSelectedEdges, subtwoCrossingSelectedEdges, e.property]

/-- Padded κ floor colors leave one quarter of a local bin for each quotient
vertex after the physical harmonic residual is counted. -/
theorem subtwoFloorPhysical_harmonicReserve_quarter
    (G : WeightedMultigraph.{u}) {n k : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (hK : subtwoKappa * n ≤ k)
    (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color)
    (q : (G.subtwoFloorQuotient n).V) :
    let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
    C.residualGraph.starCharge harmonicCharge q + (n : ℝ) / 4 ≤
      ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor q).card := by
  dsimp only
  let block := G.subtwoFloorBlock n
  let Fcross := G.subtwoCrossingSelectedEdges block Finset.univ
  let Fsel := G.floorPacketization.originalEdgesOfPackets
    (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
      block G.fullFloorPacketSet)
  let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
  have hcross : ∀ e ∈ Fcross \ Fsel,
      block (G.fst e) ≠ block (G.snd e) := by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).2
  have hres : C.residualGraph.starCharge harmonicCharge q =
      ∑ v ∈ G.subtwoFiber block q,
        G.chargeOn harmonicCharge (Fcross \ Fsel) v := by
    rw [show C.residualGraph.starCharge harmonicCharge q =
      (G.subtwoQuotient block).chargeOn harmonicCharge C.residualEdges q by
        exact (G.subtwoQuotient block).edgeRestriction_starCharge
          harmonicCharge C.residualEdges q]
    rw [G.subtwoFloorPhysicalResidualEdges_eq hk color hproper]
    exact G.quotientCharge_eq_sum_fiberCharge block q _ _ hcross
  have hocc :
      (∑ v ∈ G.subtwoFiber block q,
        (((G.subtwoFloorQuotient n).subtwoUsedPacketLabelColors
          (G.subtwoFloorQuotientEdges n) color
          (G.floorPacketization.quotientOriginalEndpointLabel block) q v).card : ℝ)) =
      ((G.subtwoFloorQuotient n).degreeOn
        (G.subtwoFloorQuotientEdges n) q : ℝ) :=
    G.floorPacketization.sum_usedQuotientPacketColors_eq_degree
      block G.fullFloorPacketSet color hproper q
  have hbudget := G.subtwoFloor_originalLabelBudget_block hn hlocal
    color hproper q
  dsimp only at hbudget
  rw [hocc, ← hres] at hbudget
  have hmiss :
      (((G.subtwoQuotient block).missingColorsAt C.fullEdges C.baseColor q).card : ℝ) =
      k - (G.subtwoFloorQuotient n).degreeOn
        (G.subtwoFloorQuotientEdges n) q := by
    have hp := C.packetization.missingColorsAt_originalEdgesOfPackets
      C.fullPackets C.packetColor q
    have hq := (G.subtwoFloorQuotient n).card_missingColorsAt
      (G.subtwoFloorQuotientEdges n) color hproper q
    change (G.subtwoQuotient block).missingColorsAt C.fullEdges
      C.baseColor q =
      (G.subtwoFloorQuotient n).missingColorsAt
        (G.subtwoFloorQuotientEdges n) color q at hp
    rw [hp, hq]
    have hd : (G.subtwoFloorQuotient n).degreeOn
        (G.subtwoFloorQuotientEdges n) q ≤ k := by
      calc
        (G.subtwoFloorQuotient n).degreeOn
            (G.subtwoFloorQuotientEdges n) q =
            (((G.subtwoFloorQuotientEdges n).filter
              ((G.subtwoFloorQuotient n).Inc q)).image color).card := by
              rw [Finset.card_image_iff.mpr (hproper q)]
              rfl
        _ ≤ k := by
          simpa using Finset.card_le_card
            (Finset.subset_univ
              (((G.subtwoFloorQuotientEdges n).filter
                ((G.subtwoFloorQuotient n).Inc q)).image color))
    exact Nat.cast_sub hd
  convert subtwoFloor_exteriorReserve_quarter hK hbudget hmiss using 1 <;>
    ring

/-- The same actual quotient palette has a fifth-bin reserve after assigning
tiny residual edges their inflated artificial charge. -/
theorem subtwoFloorPhysical_splitReserve_fifth
    (G : WeightedMultigraph.{u}) {n k : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (hK : subtwoKappa * n ≤ k)
    (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color)
    (finite : Finset
      (G.subtwoFloorPhysicalColoredPacketBase hk n color hproper).residualGraph.E)
    (tau : ℝ) (htau0 : 0 ≤ tau) (htau : tau ≤ (1 : ℝ) / 40)
    (htiny : ∀ q,
      (G.subtwoFloorPhysicalColoredPacketBase hk n color hproper).quotientTinyStarWeight
        finite q ≤ n)
    (q : (G.subtwoFloorQuotient n).V) :
    let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
    C.quotientSplitStarCharge finite tau q + (n : ℝ) / 5 ≤
      ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor q).card := by
  dsimp only
  let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
  have hinflate := C.quotientSplitStarCharge_le_harmonic_add_twoTau
    finite tau n htau0 (by linarith) (Nat.cast_nonneg n) htiny q
  have hquarter := G.subtwoFloorPhysical_harmonicReserve_quarter
    hk hn hlocal hK color hproper q
  have hquarter' : C.residualGraph.starCharge harmonicCharge q +
      (1 / 4 : ℝ) * n ≤
      ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor q).card := by
    convert hquarter using 1 <;> ring
  convert inflatedReserve_fifth_of_quarter (Nat.cast_nonneg n) htau0 htau
    hinflate hquarter' using 1 <;> ring

/-- The tiny residual weight is paid by its ordinary harmonic charge, so the
upper palette size bounds its aggregate load without a separate block-fiber
estimate. -/
theorem subtwoFloorPhysical_splitReserve_fifth_of_paletteBound
    (G : WeightedMultigraph.{u}) {n k : ℕ}
    (hk : 0 < k) (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (hK : subtwoKappa * n ≤ k) (hKupper : (k : ℝ) ≤ 4 * n)
    (color : (G.subtwoFloorQuotient n).E → Fin k)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) color)
    (finite : Finset
      (G.subtwoFloorPhysicalColoredPacketBase hk n color hproper).residualGraph.E)
    (tau : ℝ) (htau0 : 0 ≤ tau) (htau : tau ≤ (1 : ℝ) / 160)
    (q : (G.subtwoFloorQuotient n).V) :
    let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
    C.quotientSplitStarCharge finite tau q + (n : ℝ) / 5 ≤
      ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor q).card := by
  dsimp only
  let C := G.subtwoFloorPhysicalColoredPacketBase hk n color hproper
  have htinyharm : C.quotientTinyStarWeight finite q ≤
      C.residualGraph.starCharge harmonicCharge q := by
    unfold GeneralColoredPacketBase.quotientTinyStarWeight starCharge
    apply Finset.sum_le_sum
    intro e _
    by_cases he : e.1 ∈ finite
    · simp [he, harmonicCharge_nonneg]
    · simpa [he] using weight_le_harmonicCharge_of_unit
        (C.residualGraph.weight_pos e.1)
        (C.residualGraph.weight_le_one e.1)
  have hquarter := G.subtwoFloorPhysical_harmonicReserve_quarter
    hk hn hlocal hK color hproper q
  have hmissK : (((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
      C.fullEdges C.baseColor q).card : ℝ) ≤ k := by
    have hcard : ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor q).card ≤ k := by
      simpa using Finset.card_le_card
        (Finset.subset_univ
          ((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
            C.fullEdges C.baseColor q))
    exact_mod_cast hcard
  have htiny : C.quotientTinyStarWeight finite q ≤ 4 * n := by
    have h := htinyharm
    dsimp only at hquarter
    linarith
  have hinflate := C.quotientSplitStarCharge_le_harmonic_add_tinyWeight
    finite tau htau0 (by linarith) q
  have hratio : tau / (1 - tau) ≤ 2 * tau := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - tau)).2
    nlinarith [mul_nonneg htau0 (by linarith : 0 ≤ 1 / 2 - tau)]
  have htiny0 : 0 ≤ C.quotientTinyStarWeight finite q := by
    unfold GeneralColoredPacketBase.quotientTinyStarWeight
    apply Finset.sum_nonneg
    intro e _
    split
    · exact le_rfl
    · exact C.residualGraph.weight_nonneg e.1
  have hcost : tau / (1 - tau) * C.quotientTinyStarWeight finite q ≤
      8 * tau * n := by
    have h1 := mul_le_mul_of_nonneg_right hratio htiny0
    have h2 := mul_le_mul_of_nonneg_left htiny (by positivity : 0 ≤ 2 * tau)
    nlinarith
  have hfinal : C.quotientSplitStarCharge finite tau q + n / 5 ≤
      (((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor q).card : ℝ) := by
    change C.residualGraph.starCharge harmonicCharge q + (n : ℝ) / 4 ≤
      (((G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
        C.fullEdges C.baseColor q).card : ℝ) at hquarter
    change C.quotientSplitStarCharge finite tau q ≤
      C.residualGraph.starCharge harmonicCharge q +
        tau / (1 - tau) * C.quotientTinyStarWeight finite q at hinflate
    nlinarith
  exact hfinal

end
end WeightedEdgeColoring.WeightedMultigraph
