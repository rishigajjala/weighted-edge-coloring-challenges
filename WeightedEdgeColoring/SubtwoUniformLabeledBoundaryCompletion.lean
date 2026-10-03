import WeightedEdgeColoring.SubtwoUniformBoundaryCompletion
import WeightedEdgeColoring.SubtwoBoundaryFiberLabel
import WeightedEdgeColoring.SubtwoBoundaryLabelAllowance

/-! The boundary decoder's six-symbol interface suffices for physical completion. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
universe u

theorem exists_uniform_labeledBoundary_completion
    (S : ℕ) (hS : 0 < S) (η padding rate constant : ℝ)
    (hη : 0 < η) (hpadding : 0 < padding) (hrate0 : 0 ≤ rate)
    (hrate : rate ≤ padding / 20) (hconstant : 0 ≤ constant) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (G : WeightedMultigraph.{u})
        (P : G.GeneralTinyThresholdPacketization ((1 : ℝ) / S))
        (n : ℕ), N ≤ n → P.mixedObjectGraph.LocallyPacksInto n →
      let H := P.mixedObjectGraph
      let block := H.subtwoFloorBlock n
      ∀ (K : ℕ), 0 < K →
      ((1999 / 1000 : ℝ) + padding / 2) * n ≤ K →
      ∀ (hfiber : ∀ q, (H.subtwoFiber block q).card ≤ 5)
        (labels : (H.subtwoFloorQuotient n).V → Fin K → Option (Fin 6)),
      (∀ q v, block v = q →
        (Fintype.card {c : Fin K // labels q c =
          some (H.subtwoLocalSixLabel block hfiber q v)} : ℝ) ≤
        H.subtwoExteriorHarmonicCharge (H.subtwoFiber block q) v +
          rate * n + constant) →
      ∀ (B : Finset H.E) (boundary : H.E → Fin K) (loss : ℝ),
      B ⊆ H.subtwoCrossingSelectedEdges block Finset.univ →
      H.IsFeasibleOn B boundary →
      (∀ e ∈ B, ∀ v, H.Inc v e →
        labels (block v) (boundary e) =
          some (H.subtwoLocalSixLabel block hfiber (block v) v)) →
      (∀ v, (∑ e ∈ H.subtwoCrossingSelectedEdges block Finset.univ \ B,
        if H.Inc v e then H.weight e else 0) ≤ loss) →
      ∃ (F : Finset H.E) (color : H.E → Fin K),
        H.IsFeasibleOn F color ∧ (∀ e ∈ B, color e = boundary e) ∧
        ∀ v, (∑ e ∈ Finset.univ \ F, if H.Inc v e then H.weight e else 0) ≤
          loss + 25 / (S : ℝ) + η * n := by
  obtain ⟨Ninside,hNinside,hinside⟩ :=
    exists_uniform_tinyBoundary_completion S hS η hη
  obtain ⟨Nlabels,hlabels⟩ := exists_uniform_boundaryLabelAllowance
    padding rate constant hpadding hrate0 hrate hconstant
  refine ⟨max Ninside Nlabels, lt_of_lt_of_le hNinside (le_max_left _ _), ?_⟩
  intro G P n hn hlocal
  dsimp only
  intro K hK hKlower hfiber labels hcounts B boundary loss hB hboundary hsupport hloss
  have hnInside := (le_max_left Ninside Nlabels).trans hn
  have hnLabels := (le_max_right Ninside Nlabels).trans hn
  have hnpos : 0 < n := lt_of_lt_of_le hNinside hnInside
  obtain ⟨D,hD,hDpalette⟩ := hlabels n hnLabels
  let H := P.mixedObjectGraph
  let block := H.subtwoFloorBlock n
  let fiberLabels := H.subtwoBoundaryFiberLabel block hfiber labels
  apply hinside G P n hnInside hlocal D K hK fiberLabels
  · intro q v
    have hv : block v.1 = q := (H.mem_subtwoFiber block q v.1).1 v.2
    have hc := hcounts q v.1 hv
    change (Fintype.card {c : Fin K //
      H.subtwoBoundaryFiberLabel block hfiber labels q c = some v} : ℝ) ≤ _
    rw [H.subtwoBoundaryFiberLabel_class_card block hfiber labels q v]
    apply boundaryLabelAllowance_normalizedCharge hnpos _ hD
    simpa only [add_assoc] using hc
  · exact boundaryLabelAllowance_palette hDpalette hKlower
  · exact hB
  · exact hboundary
  · intro e he v hev
    exact H.subtwoBoundaryFiberLabel_support block hfiber labels v (boundary e)
      (hsupport e he v hev)
  · exact hloss

end
end WeightedEdgeColoring.WeightedMultigraph
