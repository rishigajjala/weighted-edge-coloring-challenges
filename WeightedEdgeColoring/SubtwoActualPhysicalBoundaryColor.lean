import WeightedEdgeColoring.SubtwoPhysicalBoundaryAssembly
import WeightedEdgeColoring.SubtwoBoundaryFiberLabel
import WeightedEdgeColoring.SubtwoPacketQuotientCharge
import WeightedEdgeColoring.SubtwoActualQuotientResidualMultiplicity

/-! The floor packet base and a supported residual decoder yield one actual
physical crossing-edge coloring and endpoint label map. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 3000000
universe u

theorem subtwoFloorBaseEdges_crossing_eq
    (G : WeightedMultigraph.{u}) (n : ℕ) :
    G.subtwoCrossingSelectedEdges (G.subtwoFloorBlock n)
      (G.subtwoFloorBaseEdges n) = G.subtwoFloorBaseEdges n := by
  classical
  ext e
  constructor
  · intro he
    exact (Finset.mem_filter.mp he).1
  · intro he
    apply Finset.mem_filter.mpr
    refine ⟨he, ?_⟩
    exact (G.floorPacketization.packetOf_crossing_iff
      (G.subtwoFloorBlock n) e).1
        (Finset.mem_filter.mp (Finset.mem_filter.mp he).2).2

/-- Deterministic final floor-boundary lift.  The residual label budget is
kept as a numerical input, while feasibility, endpoint support, and the
packet part of the label charge are established from the actual objects. -/
theorem exists_subtwoFloorPhysicalBoundaryColor
    (G : WeightedMultigraph.{u}) {n K : ℕ}
    (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (hK : 0 < K)
    (baseColor : (G.subtwoFloorQuotient n).E → Fin K)
    (hproper : (G.subtwoFloorQuotient n).IsProperOn
      (G.subtwoFloorQuotientEdges n) baseColor)
    (mixed :
      (G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientHybridGraph.E →
        Fin K)
    (hmixed :
      (G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientHybridGraph.IsProperOn
        (G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientHybridPacketEdges
        mixed)
    (R : Finset
      ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
        mixed hmixed).residualGraph.E)
    (color :
      ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
        mixed hmixed).residualGraph.E → Fin K)
    (hfeasible :
      ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
        mixed hmixed).residualGraph.IsFeasibleOn R color)
    (hmissing : ∀ e ∈ R,
      color e ∈ (G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
          ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
            mixed hmixed).fullEdges
          ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
            mixed hmixed).baseColor
          ((G.subtwoQuotient (G.subtwoFloorBlock n)).fst e.1) ∧
      color e ∈ (G.subtwoQuotient (G.subtwoFloorBlock n)).missingColorsAt
          ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
            mixed hmixed).fullEdges
          ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
            mixed hmixed).baseColor
          ((G.subtwoQuotient (G.subtwoFloorBlock n)).snd e.1))
    (selectedLabel : (G.subtwoQuotient (G.subtwoFloorBlock n)).V →
      Fin K → Option (Fin 6))
    (hselected : ∀ e ∈ R, ∀ q
      (hinc : ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
        mixed hmixed).residualGraph.Inc q e),
      selectedLabel q (color e) =
        some (G.subtwoQuotientResidualEdgeLabel
          (G.subtwoFloorBlock n)
          (G.subtwoFloorBlock_fiber_card_le_five hn hlocal)
          ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
            mixed hmixed) q ⟨e,hinc⟩))
    (labelError loss : ℝ)
    (hlabelBudget : ∀ v : G.V,
      ((Finset.univ.filter fun c : Fin K =>
        selectedLabel (G.subtwoFloorBlock n v) c =
          some (G.subtwoLocalSixLabel (G.subtwoFloorBlock n)
            (G.subtwoFloorBlock_fiber_card_le_five hn hlocal)
            (G.subtwoFloorBlock n v) v)).card : ℝ) ≤
        G.chargeOn harmonicCharge
          (G.subtwoCrossingSelectedEdges (G.subtwoFloorBlock n) Finset.univ \
            G.subtwoFloorBaseEdges n) v + labelError)
    (hloss : ∀ q,
      (∑ e ∈ Finset.univ \ R,
        if ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
          mixed hmixed).residualGraph.Inc q e
        then ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
          mixed hmixed).residualGraph.weight e else 0) ≤ loss) :
    let block := G.subtwoFloorBlock n
    let Fboundary := G.subtwoFloorBaseEdges n ∪
      G.selectedResidualOriginalEdges block
        ((G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper).quotientRecoloredBase
          mixed hmixed) R
    ∃ (boundary : G.E → Fin K)
      (labels : (G.subtwoQuotient block).V → Fin K → Option (Fin 6)),
      G.IsFeasibleOn Fboundary boundary ∧
      (∀ e ∈ Fboundary, ∀ v, G.Inc v e →
        labels (block v) (boundary e) =
          some (G.subtwoLocalSixLabel block
            (G.subtwoFloorBlock_fiber_card_le_five hn hlocal)
            (block v) v)) ∧
      (∀ v : G.V,
        ((Finset.univ.filter fun c : Fin K =>
          labels (block v) c =
            some (G.subtwoLocalSixLabel block
              (G.subtwoFloorBlock_fiber_card_le_five hn hlocal)
              (block v) v)).card : ℝ) ≤
          G.subtwoExteriorHarmonicCharge
            (G.subtwoFiber block (block v)) v + labelError) ∧
      ∀ v, (∑ e ∈ G.subtwoCrossingSelectedEdges block Finset.univ \ Fboundary,
        if G.Inc v e then G.weight e else 0) ≤ loss := by
  classical
  dsimp only
  let block := G.subtwoFloorBlock n
  let C := G.subtwoFloorPhysicalColoredPacketBase hK n baseColor hproper
  let C' := C.quotientRecoloredBase mixed hmixed
  let fiber := G.subtwoFloorBlock_fiber_card_le_five hn hlocal
  have hfull : C'.fullEdges = G.subtwoQuotientSelectedEdges block
      (G.subtwoFloorBaseEdges n) := by
    simpa [C',C] using G.subtwoFloorPhysicalColoredPacketBase_fullEdges
      hK n baseColor hproper
  have hcross := G.subtwoFloorBaseEdges_crossing_eq n
  have hunique : ∀ e ∈ G.subtwoCrossingSelectedEdges block
      (G.subtwoFloorBaseEdges n),
      ∀ f ∈ G.subtwoCrossingSelectedEdges block (G.subtwoFloorBaseEdges n),
      ∀ v w, G.Inc v e → G.Inc w f → block v = block w →
        G.subtwoLiftQuotientColor hK block C'.baseColor e =
          G.subtwoLiftQuotientColor hK block C'.baseColor f → v = w := by
    intro e he f hf v w hve hfw hb hc
    have he' : e ∈ G.subtwoFloorBaseEdges n := by simpa [block,hcross] using he
    have hf' : f ∈ G.subtwoFloorBaseEdges n := by simpa [block,hcross] using hf
    exact G.subtwoRecoloredPacketBase_original_endpoint_unique
      G.floorPacketization hK block G.fullFloorPacketSet baseColor hproper
      mixed hmixed he' hf' (Finset.mem_filter.mp he).2
      (Finset.mem_filter.mp hf).2 hve hfw hb (by
        simpa [C,C',subtwoLiftQuotientColor,
          (Finset.mem_filter.mp he).2,
          (Finset.mem_filter.mp hf).2] using hc)
  obtain ⟨boundary,labels,hfeas,hsupport,hcounts,hleft⟩ :=
    G.exists_physicalBoundary_partialColor block fiber hK C'
      (G.subtwoFloorBaseEdges n) hfull hunique R color hfeasible
      hmissing selectedLabel hselected loss hloss
  have hEdges : G.subtwoCrossingSelectedEdges block
      (G.subtwoFloorBaseEdges n) = G.subtwoFloorBaseEdges n := by
    simpa only [block] using hcross
  rw [hEdges] at hfeas hsupport hcounts hleft
  refine ⟨boundary,labels,hfeas,hsupport,?_,hleft⟩
  intro v
  have hbase := G.subtwoRecoloredBaseLabelClass_card_le_packetDegree
    G.floorPacketization block fiber hK G.fullFloorPacketSet
    baseColor hproper mixed hmixed (block v) v rfl
  have htotal := hcounts (block v)
    (G.subtwoLocalSixLabel block fiber (block v) v)
  have hcharge := G.subtwoFloor_crossingPacketDegree_add_residualCharge_le n v
  dsimp only at hcharge
  have hcharge' :
      (G.floorPacketization.groupedGraph.degreeOn
        (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
          block G.fullFloorPacketSet) v : ℝ) +
        G.chargeOn harmonicCharge
          (G.subtwoCrossingSelectedEdges block Finset.univ \
            G.subtwoFloorBaseEdges n) v ≤
        G.subtwoExteriorHarmonicCharge
          (G.subtwoFiber block (block v)) v := by
    simpa only [subtwoFloorBaseEdges] using hcharge
  have hselectedBudget := hlabelBudget v
  have hbase' :
      ((Finset.univ.filter fun c : Fin K =>
          ∃ w, block w = block v ∧
            (∃ e ∈ G.subtwoFloorBaseEdges n,
              G.Inc w e ∧ G.subtwoLiftQuotientColor hK block C'.baseColor e = c) ∧
            G.subtwoLocalSixLabel block fiber (block v) w =
              G.subtwoLocalSixLabel block fiber (block v) v).card : ℝ) ≤
        G.floorPacketization.groupedGraph.degreeOn
          (G.floorPacketization.groupedGraph.subtwoCrossingSelectedEdges
            block G.fullFloorPacketSet) v := by
    exact_mod_cast (by simpa [subtwoFloorBaseEdges,C,C'] using hbase)
  have htotalR :
      (((Finset.univ.filter fun c : Fin K =>
        labels (block v) c =
          some (G.subtwoLocalSixLabel block fiber (block v) v)).card : ℝ)) ≤
        ((Finset.univ.filter fun c : Fin K =>
          ∃ w, block w = block v ∧
            (∃ e ∈ G.subtwoFloorBaseEdges n,
              G.Inc w e ∧ G.subtwoLiftQuotientColor hK block C'.baseColor e = c) ∧
            G.subtwoLocalSixLabel block fiber (block v) w =
              G.subtwoLocalSixLabel block fiber (block v) v).card : ℝ) +
        ((Finset.univ.filter fun c : Fin K =>
          selectedLabel (block v) c =
            some (G.subtwoLocalSixLabel block fiber (block v) v)).card : ℝ) := by
    exact_mod_cast htotal
  nlinarith [hcharge']

end
end WeightedEdgeColoring.WeightedMultigraph
