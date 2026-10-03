import WeightedEdgeColoring.SubtwoBoundaryCombinedLabel
import WeightedEdgeColoring.SubtwoPacketQuotientBase
import WeightedEdgeColoring.SubtwoQuotientHybrid
import WeightedEdgeColoring.SubtwoPacketQuotientCharge
import WeightedEdgeColoring.SubtwoMixedGraphLocalSixLabels

/-! Recolored quotient packets still have one original endpoint per
block and color. -/

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}}
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

namespace Packetization

variable (P : G.Packetization)

theorem subtwoQuotientColoredPacketBase_original_endpoint_unique
    {K : ℕ} (hK : 0 < K) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin K)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    {e f : G.E}
    (he : e ∈ P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S))
    (hf : f ∈ P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S))
    (hecross : block (G.fst e) ≠ block (G.snd e))
    (hfcross : block (G.fst f) ≠ block (G.snd f))
    {v w : G.V} (hv : G.Inc v e) (hw : G.Inc w f)
    (hb : block v = block w)
    (hc : (P.subtwoQuotientColoredPacketBase hK block S color hproper).baseColor
        ⟨e, hecross⟩ =
      (P.subtwoQuotientColoredPacketBase hK block S color hproper).baseColor
        ⟨f, hfcross⟩) :
    v = w := by
  have hepcross :
      block (P.groupedGraph.fst (P.packetOf e)) ≠
        block (P.groupedGraph.snd (P.packetOf e)) :=
    (P.packetOf_crossing_iff block e).2 hecross
  have hfpcross :
      block (P.groupedGraph.fst (P.packetOf f)) ≠
        block (P.groupedGraph.snd (P.packetOf f)) :=
    (P.packetOf_crossing_iff block f).2 hfcross
  exact P.subtwo_expanded_quotient_color_endpoint_unique hK block S color
    hproper he hf hv hw hb (by
      simpa [subtwoQuotientColoredPacketBase,
        WeightedMultigraph.GeneralColoredPacketBase.baseColor,
        WeightedMultigraph.Packetization.expandColor,
        WeightedMultigraph.subtwoLiftQuotientColor,
        WeightedMultigraph.Packetization.subtwoQuotientPacketization,
        hecross, hfcross, hepcross, hfpcross] using hc)

/-- Every physical full-packet color at an original vertex is counted in
the corresponding quotient packet label class. -/
theorem originalBaseColorClass_subset_packetLabelClass
    {K : ℕ} (hK : 0 < K) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin K)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    (q : Q) (v : G.V) (hv : block v = q) :
    (Finset.univ.filter fun c : Fin K ↦
      ∃ e ∈ P.originalEdgesOfPackets
        (P.groupedGraph.subtwoCrossingSelectedEdges block S),
        G.Inc v e ∧
          G.subtwoLiftQuotientColor hK block
            (P.subtwoQuotientColoredPacketBase hK block S color hproper).baseColor e = c) ⊆
      (P.groupedGraph.subtwoQuotient block).subtwoUsedPacketLabelColors
        (P.groupedGraph.subtwoQuotientSelectedEdges block S)
        color (P.quotientOriginalEndpointLabel block) q v := by
  classical
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  obtain ⟨e, he, hve, hce⟩ := hc
  have hedata := Finset.mem_filter.mp he
  have hpS := Finset.mem_filter.mp hedata.2
  have hcross : block (G.fst e) ≠ block (G.snd e) :=
    (P.packetOf_crossing_iff block e).1 hpS.2
  let pQ : (P.groupedGraph.subtwoQuotient block).E :=
    ⟨P.packetOf e, hpS.2⟩
  have hpq : (P.groupedGraph.subtwoQuotient block).Inc q pQ := by
    have hinc := (P.incidence v e).2 hve
    rcases hinc with h | h
    · exact Or.inl ((congrArg block h).trans hv)
    · exact Or.inr ((congrArg block h).trans hv)
  have hlabel : P.quotientOriginalEndpointLabel block q pQ = v :=
    (P.quotientOriginalEndpointLabel_eq_iff_inc
      block q pQ v hv hpq).2 ((P.incidence v e).2 hve)
  have hcolor : color pQ = c := by
    simpa [subtwoQuotientColoredPacketBase,
      WeightedMultigraph.GeneralColoredPacketBase.baseColor,
      WeightedMultigraph.Packetization.subtwoQuotientPacketization,
      WeightedMultigraph.subtwoLiftQuotientColor, hcross]
      using hce
  apply Finset.mem_image.mpr
  refine ⟨pQ, ?_, hcolor⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpS.1⟩,
    hpq, hlabel⟩

end Packetization

/-- Recoloring the quotient full packets through the hybrid construction
keeps the unique physical endpoint of each color at every block. -/
theorem subtwoRecoloredPacketBase_original_endpoint_unique
    (P : G.Packetization)
    {K : ℕ} (hK : 0 < K) (block : G.V → Q) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin K)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    (mixed :
      (P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientHybridGraph.E →
        Fin K)
    (hmixed :
      (P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientHybridGraph.IsProperOn
        (P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientHybridPacketEdges
        mixed)
    {e f : G.E}
    (he : e ∈ P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S))
    (hf : f ∈ P.originalEdgesOfPackets
      (P.groupedGraph.subtwoCrossingSelectedEdges block S))
    (hecross : block (G.fst e) ≠ block (G.snd e))
    (hfcross : block (G.fst f) ≠ block (G.snd f))
    {v w : G.V} (hv : G.Inc v e) (hw : G.Inc w f)
    (hb : block v = block w)
    (hc : ((P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientRecoloredBase
        mixed hmixed).baseColor ⟨e, hecross⟩ =
      ((P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientRecoloredBase
        mixed hmixed).baseColor ⟨f, hfcross⟩) :
    v = w := by
  let C := P.subtwoQuotientColoredPacketBase hK block S color hproper
  let C' := C.quotientRecoloredBase mixed hmixed
  let recolor : (P.groupedGraph.subtwoQuotient block).E → Fin K :=
    fun p => mixed (Sum.inl p)
  have hrecolor : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) recolor := by
    simpa [C, C', recolor, WeightedMultigraph.Packetization.subtwoQuotientColoredPacketBase,
      WeightedMultigraph.GeneralColoredPacketBase.fullEdges,
      WeightedMultigraph.GeneralColoredPacketBase.fullPackets,
      WeightedMultigraph.GeneralColoredPacketBase.packetColor] using C'.packetProper
  apply P.subtwoQuotientColoredPacketBase_original_endpoint_unique
    hK block S recolor hrecolor he hf hecross hfcross hv hw hb
  simpa [C, C', recolor, WeightedMultigraph.GeneralColoredPacketBase.quotientRecoloredBase,
    WeightedMultigraph.Packetization.subtwoQuotientColoredPacketBase,
    WeightedMultigraph.GeneralColoredPacketBase.baseColor] using hc

/-- A six-symbol base label class after recoloring is no larger than the
original number of selected packets at that physical endpoint. -/
theorem subtwoRecoloredBaseLabelClass_card_le_packetDegree
    (P : G.Packetization)
    (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (hK : 0 < K) (S : Finset P.Packet)
    (color : (P.groupedGraph.subtwoQuotient block).E → Fin K)
    (hproper : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) color)
    (mixed :
      (P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientHybridGraph.E →
        Fin K)
    (hmixed :
      (P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientHybridGraph.IsProperOn
        (P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientHybridPacketEdges
        mixed)
    (q : Q) (v : G.V) (hv : block v = q) :
    (Finset.univ.filter fun c : Fin K ↦
      ∃ w, block w = q ∧
        (∃ e ∈ P.originalEdgesOfPackets
          (P.groupedGraph.subtwoCrossingSelectedEdges block S),
          G.Inc w e ∧
            G.subtwoLiftQuotientColor hK block
              ((P.subtwoQuotientColoredPacketBase hK block S color hproper).quotientRecoloredBase
                mixed hmixed).baseColor e = c) ∧
        G.subtwoLocalSixLabel block hfiber q w =
          G.subtwoLocalSixLabel block hfiber q v).card ≤
      P.groupedGraph.degreeOn
        (P.groupedGraph.subtwoCrossingSelectedEdges block S) v := by
  classical
  let recolor : (P.groupedGraph.subtwoQuotient block).E → Fin K :=
    fun p => mixed (Sum.inl p)
  let C := P.subtwoQuotientColoredPacketBase hK block S color hproper
  let C' := C.quotientRecoloredBase mixed hmixed
  have hrecolor : (P.groupedGraph.subtwoQuotient block).IsProperOn
      (P.groupedGraph.subtwoQuotientSelectedEdges block S) recolor := by
    simpa [C, C', recolor,
      WeightedMultigraph.Packetization.subtwoQuotientColoredPacketBase]
      using C'.packetProper
  have hinj : ∀ b w x, block w = b → block x = b →
      G.subtwoLocalSixLabel block hfiber b w =
        G.subtwoLocalSixLabel block hfiber b x → w = x := by
    intro b w x hw hx heq
    exact G.subtwoLocalSixLabel_injective_on_fiber block hfiber b
      ((G.mem_subtwoFiber block b w).2 hw)
      ((G.mem_subtwoFiber block b x).2 hx) heq
  let Fbase := P.originalEdgesOfPackets
    (P.groupedGraph.subtwoCrossingSelectedEdges block S)
  let base := G.subtwoLiftQuotientColor hK block C'.baseColor
  have hfirst := G.boundaryBaseLabelClass_subset_vertexColors
    Fbase block base (G.subtwoLocalSixLabel block hfiber) hinj v
  have hsecond :
      (Finset.univ.filter fun c : Fin K ↦
        ∃ e ∈ Fbase, G.Inc v e ∧ base e = c) ⊆
      (P.groupedGraph.subtwoQuotient block).subtwoUsedPacketLabelColors
        (P.groupedGraph.subtwoQuotientSelectedEdges block S)
        recolor (P.quotientOriginalEndpointLabel block) q v := by
    simpa [C, C', Fbase, base, recolor,
      WeightedMultigraph.GeneralColoredPacketBase.quotientRecoloredBase,
      WeightedMultigraph.Packetization.subtwoQuotientColoredPacketBase] using
      P.originalBaseColorClass_subset_packetLabelClass
        hK block S recolor hrecolor q v hv
  have hcard := Finset.card_le_card (hfirst.trans hsecond)
  simpa [Fbase, base, hv,
    P.card_usedQuotientPacketColors_originalEndpoint
      block S recolor hrecolor q v hv] using hcard

end
