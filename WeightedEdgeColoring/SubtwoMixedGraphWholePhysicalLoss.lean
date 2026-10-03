import WeightedEdgeColoring.SubtwoMixedGraphFullDecoder
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeWholeLoss
import WeightedEdgeColoring.MultigraphDyadicLargeEdgeExtraCapture

/-!
# Whole physical residual of the selected mixed decoder
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

variable (G : WeightedMultigraph)
variable {Color Class : Type*} [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

theorem ordinarySelectedEdges_relabel_selectedDyadicAny
    (K N : ℕ) (bucket : G.E → Class) (gamma : ℝ) (reserve : ℕ)
    (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))) :
    G.ordinarySelectedEdges
      ((G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
        residual x M).map
          (OrdinarySlotChoice.colorEquiv
            (Fintype.equivFin Color)).toEmbedding) =
      G.selectedDyadicOrdinaryEdges K N bucket gamma reserve residual x M := by
  classical
  ext e
  simp only [ordinarySelectedEdges, selectedDyadicOrdinaryEdges,
    selectedDyadicOrdinaryBaseOptionsAny, Finset.mem_image]
  constructor
  · rintro ⟨oFin, hoFin, he⟩
    rcases Finset.mem_map.mp hoFin with ⟨o, ho, rfl⟩
    exact ⟨o, ho, he⟩
  · rintro ⟨o, ho, he⟩
    refine ⟨(OrdinarySlotChoice.colorEquiv
      (Fintype.equivFin Color)) o, ?_, he⟩
    exact Finset.mem_map.mpr ⟨o, ho, rfl⟩

/-- The relabelled physical assignment leaves exactly the unmatched large
edges and the tiny edges for which the integral decision is `none`. -/
theorem uncolored_selectedMixed_joint_starWeight_eq
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (T : Finset G.E) (hT : ∀ e, e ∈ T ↔ G.weight e < beta)
    (decision : {e : G.E // e ∈ T} → Option (Fin (Fintype.card Color)))
    (hdisjoint : Disjoint
      (G.ordinarySelectedEdges
        ((G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
          residual x M).map
            (OrdinarySlotChoice.colorEquiv
              (Fintype.equivFin Color)).toEmbedding)) T)
    (v : G.V) :
    (∑ e ∈ Finset.univ \ (G.ordinarySelectedEdges
        ((G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
          residual x M).map
            (OrdinarySlotChoice.colorEquiv
              (Fintype.equivFin Color)).toEmbedding) ∪
        G.tinyDecisionColoredEdges T decision),
      if G.Inc v e then G.weight e else 0) =
      G.dyadicLargeRemainingStarWeight K N beta bucket gamma reserve residual x
        M v + G.tinyResidualIntegralLossLoad decision v := by
  classical
  let O := (G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
    residual x M).map
      (OrdinarySlotChoice.colorEquiv
        (Fintype.equivFin Color)).toEmbedding
  have hset : Finset.univ \ (G.ordinarySelectedEdges O ∪
      G.tinyDecisionColoredEdges T decision) =
      G.dyadicLargeEdgesRemainingAfterOrdinary K N beta bucket gamma reserve
        residual x M ∪ (T \ G.tinyDecisionColoredEdges T decision) := by
    ext e
    have hordTiny : e ∈ G.ordinarySelectedEdges O → e ∉ T := by
      intro heOrd heTiny
      exact Finset.disjoint_left.mp hdisjoint heOrd heTiny
    have htinyColored : e ∈ G.tinyDecisionColoredEdges T decision → e ∈ T := by
      intro he
      exact (Finset.mem_filter.mp he).1
    rw [G.ordinarySelectedEdges_relabel_selectedDyadicAny
      K N bucket gamma reserve residual x M]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      dyadicLargeEdgesRemainingAfterOrdinary, G.mem_largeEdgeJobs]
    by_cases hlarge : beta ≤ G.weight e
    · have hnotTiny : e ∉ T := fun he ↦ not_lt_of_ge hlarge ((hT e).mp he)
      have hnotTinyColored : e ∉ G.tinyDecisionColoredEdges T decision :=
        fun he ↦ hnotTiny (htinyColored he)
      simp [hlarge, hnotTiny, hnotTinyColored]
    · have htiny : e ∈ T := (hT e).mpr (lt_of_not_ge hlarge)
      have hnotOrdinary : e ∉ G.selectedDyadicOrdinaryEdges K N bucket gamma
          reserve residual x M := by
        rw [← G.ordinarySelectedEdges_relabel_selectedDyadicAny
          K N bucket gamma reserve residual x M]
        exact fun he ↦ hordTiny he htiny
      simp [hlarge, htiny, hnotOrdinary]
  change (∑ e ∈ Finset.univ \ (G.ordinarySelectedEdges O ∪
      G.tinyDecisionColoredEdges T decision),
      if G.Inc v e then G.weight e else 0) = _
  rw [hset]
  have hparts : Disjoint
      (G.dyadicLargeEdgesRemainingAfterOrdinary K N beta bucket gamma reserve
        residual x M) (T \ G.tinyDecisionColoredEdges T decision) := by
    rw [Finset.disjoint_left]
    intro e heLarge heTiny
    have hge := G.mem_largeEdgeJobs.mp (Finset.mem_sdiff.mp heLarge).1
    have hlt := (hT e).mp (Finset.mem_sdiff.mp heTiny).1
    exact (not_lt_of_ge hge) hlt
  rw [Finset.sum_union hparts]
  unfold dyadicLargeRemainingStarWeight
  rw [Finset.sum_filter]
  rw [G.tinyResidualIntegralLossLoad_eq_sum_sdiff]

/-- Uniform endpoint loss after the ordinary matching, extra-slot capture,
and tiny rounding.  All terms are local to one endpoint except the explicit
bucket-rounding sum. -/
theorem uncolored_selectedMixed_joint_starWeight_le
    (K N : ℕ) (beta : ℝ) (bucket : G.E → Class) (gamma ratio : ℝ)
    (reserve : ℕ) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)))
    (hM : ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
      (G.dyadicLargeEdgeMass K bucket gamma reserve residual x)).IsPartialMatching M)
    (T : Finset G.E) (hT : ∀ e, e ∈ T ↔ G.weight e < beta)
    (decision : {e : G.E // e ∈ T} → Option (Fin (Fintype.card Color)))
    (hdisjoint : Disjoint
      (G.ordinarySelectedEdges
        ((G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
          residual x M).map
            (OrdinarySlotChoice.colorEquiv
              (Fintype.equivFin Color)).toEmbedding)) T)
    (hr0 : ∀ e, 0 ≤ residual e) (hreserve : 0 < reserve)
    (hgamma1 : gamma < 1)
    (upper : Class → ℝ) (hupper0 : ∀ h, 0 ≤ upper h)
    (hweight : ∀ e, G.weight e ≤ upper (bucket e))
    (hratio : ∀ e, upper (bucket e) ≤ ratio * G.weight e)
    (largeLoss tinyLoss : G.V → ℝ)
    (hlarge : ∀ v, G.uncoveredLargeStarWeight
      ((G.dyadicLargeEdgeOptionSystem K bucket gamma reserve residual).quantized N
        (G.dyadicLargeEdgeMass K bucket gamma reserve residual x))
      beta M v ≤ largeLoss v)
    (htiny : ∀ v, G.tinyResidualIntegralLossLoad decision v ≤ tinyLoss v)
    (v : G.V) :
    (∑ e ∈ Finset.univ \ (G.ordinarySelectedEdges
        ((G.selectedDyadicOrdinaryBaseOptionsAny K N bucket gamma reserve
          residual x M).map
            (OrdinarySlotChoice.colorEquiv
              (Fintype.equivFin Color)).toEmbedding) ∪
        G.tinyDecisionColoredEdges T decision),
      if G.Inc v e then G.weight e else 0) ≤
      largeLoss v +
        2 * ratio * G.weightedResidualStar residual v / (1 - gamma) +
        2 * (1 + (reserve : ℝ)) * ∑ h, upper h + tinyLoss v := by
  rw [G.uncolored_selectedMixed_joint_starWeight_eq K N beta bucket gamma
    reserve residual x M T hT decision hdisjoint v]
  have hremain := G.dyadicLargeRemainingStarWeight_le_uncovered_add_extra
    K N beta bucket gamma reserve residual x M hM v
  have hextra := G.selectedDyadicExtraEdges_starWeight_le_weightedResidual
    K N bucket gamma ratio reserve residual x M hM hr0 hreserve hgamma1
    upper hupper0 hweight hratio v
  linarith [hlarge v, htiny v]

variable {Label : Type*} [Fintype Label] [DecidableEq Label]
variable (proposal : G.E → Color → ℝ)
variable (edgeLabel : ∀ v : G.V, G.StarEdge v → Label)
variable (qLaw : ∀ v : G.V, Color → Finset (G.StarEdge v) → ℝ)
variable {s β qstep r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R : ∀ v c label,
  G.BoundedProfileRealization
    (G.conditionalEndpointProposal (edgeLabel v)
      (fun e : G.StarEdge v ↦ proposal e.1 c) (qLaw v c) label)
    s β qstep r hβ hr)

theorem selectedMixedRelabeledOrdinary_disjoint_tiny
    (rho omega : ℝ)
    (choice : ∀ v : G.V,
      G.MixedGraphPackedState proposal edgeLabel qLaw R)
    (bucket : G.E → Class) (gamma : ℝ) (reserve N : ℕ)
    (M : Finset (QuantizedCopy N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β qstep r)
        bucket gamma reserve
        (G.selectedMixedLargeResidual proposal edgeLabel qLaw R
          rho omega choice)
        (G.selectedMixedNormalizedLargeOptionMass
          proposal edgeLabel qLaw R rho omega choice)))) :
    Disjoint
      (G.ordinarySelectedEdges
        ((G.selectedDyadicOrdinaryBaseOptionsAny
          (explicitLargeSlotBound β qstep r) N bucket gamma reserve
          (G.selectedMixedLargeResidual proposal edgeLabel qLaw R
            rho omega choice)
          (G.selectedMixedNormalizedLargeOptionMass
            proposal edgeLabel qLaw R rho omega choice) M).map
            (OrdinarySlotChoice.colorEquiv
              (Fintype.equivFin Color)).toEmbedding))
      (G.selectedMixedTinyEdges (β := β)) := by
  classical
  rw [Finset.disjoint_left]
  intro e heOrd heTiny
  rcases (G.mem_ordinarySelectedEdges_iff _ e).mp heOrd with
    ⟨oFin, hoFin, rfl⟩
  rcases Finset.mem_map.mp hoFin with ⟨o, ho, rfl⟩
  have hpos := G.selectedDyadicOrdinaryBaseOptionsAny_mass_pos
    (explicitLargeSlotBound β qstep r) N bucket gamma reserve
    (G.selectedMixedLargeResidual proposal edgeLabel qLaw R rho omega choice)
    (G.selectedMixedNormalizedLargeOptionMass
      proposal edgeLabel qLaw R rho omega choice) M ho
  have hzero := G.selectedMixedNormalizedLargeOptionMass_eq_zero_of_tiny
    proposal edgeLabel qLaw R rho omega choice o.job o.color
    o.leftPlace o.rightPlace (G.mem_selectedMixedTinyEdges.mp heTiny)
  exact (ne_of_gt hpos) hzero

end WeightedMultigraph

end

end WeightedEdgeColoring
