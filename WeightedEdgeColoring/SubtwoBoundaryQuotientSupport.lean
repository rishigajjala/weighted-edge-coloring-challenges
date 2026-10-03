import WeightedEdgeColoring.SubtwoBoundaryPacketEndpoint
import WeightedEdgeColoring.SubtwoOriginalEndpointLabelCharge

/-! A color missing at a quotient block is absent from every physical base
edge at that block.  This is the bridge from positive proposal support to
the base-first boundary label map. -/

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem not_boundaryBaseUses_of_quotient_missing
    (block : G.V → Q) {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E)
    (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (q : Q) (c : Fin K)
    (hmissing : c ∈ (G.subtwoQuotient block).missingColorsAt
      C.fullEdges C.baseColor q) :
    ¬ G.boundaryBaseUses
      (G.subtwoCrossingSelectedEdges block F) block
      (G.subtwoLiftQuotientColor hK block C.baseColor) q c := by
  rintro ⟨v, hvq, e, he, hve, hce⟩
  have hF : e ∈ F := (Finset.mem_filter.mp he).1
  have hcross : block (G.fst e) ≠ block (G.snd e) :=
    (Finset.mem_filter.mp he).2
  let eQ : (G.subtwoQuotient block).E := ⟨e, hcross⟩
  have heFull : eQ ∈ C.fullEdges := by
    rw [hfull]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hF⟩
  have hinc : (G.subtwoQuotient block).Inc q eQ := by
    rcases hve with h | h
    · exact Or.inl ((congrArg block h).trans hvq)
    · exact Or.inr ((congrArg block h).trans hvq)
  have hc : C.baseColor eQ = c := by
    simpa [WeightedMultigraph.subtwoLiftQuotientColor, hcross, eQ] using hce
  exact ((G.subtwoQuotient block).not_mem_missingColorsAt_of_used
    heFull hinc) (hc ▸ hmissing)

theorem quotientFullEdges_image_eq_crossing
    (block : G.V → Q) {K : ℕ}
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E)
    (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F) :
    C.fullEdges.image Subtype.val =
      G.subtwoCrossingSelectedEdges block F := by
  classical
  ext e
  constructor
  · intro heImage
    obtain ⟨eQ, heQ, rfl⟩ := Finset.mem_image.mp heImage
    rw [hfull] at heQ
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp heQ).2, eQ.2⟩
  · intro he
    let eQ : (G.subtwoQuotient block).E :=
      ⟨e, (Finset.mem_filter.mp he).2⟩
    apply Finset.mem_image.mpr
    refine ⟨eQ, ?_, rfl⟩
    rw [hfull]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).1⟩

/-- The physical full packet base is feasible after quotient expansion,
even though the contraction incidence is only one-way at original vertices. -/
theorem feasibleOn_liftQuotientPacketBase
    (block : G.V → Q) {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E)
    (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F) :
    G.IsFeasibleOn (G.subtwoCrossingSelectedEdges block F)
      (G.subtwoLiftQuotientColor hK block C.baseColor) := by
  classical
  intro v c
  have hinj : Function.Injective
      (fun e : (G.subtwoQuotient block).E => e.1) :=
    Subtype.val_injective
  calc
    G.colorLoadOn (G.subtwoCrossingSelectedEdges block F)
        (G.subtwoLiftQuotientColor hK block C.baseColor) v c ≤
      (G.subtwoQuotient block).colorLoadOn C.fullEdges C.baseColor
        (block v) c := by
        rw [← G.quotientFullEdges_image_eq_crossing block C F hfull]
        unfold colorLoadOn
        rw [Finset.sum_image hinj.injOn]
        apply Finset.sum_le_sum
        intro e he
        have hcolor : G.subtwoLiftQuotientColor hK block C.baseColor e.1 =
            C.baseColor e := by
          simp [subtwoLiftQuotientColor, e.2]
        rw [hcolor]
        by_cases hv : G.Inc v e.1
        · have hvQ : (G.subtwoQuotient block).Inc (block v) e := by
            rcases hv with h | h
            · exact Or.inl (congrArg block h)
            · exact Or.inr (congrArg block h)
          simp only [hv, hvQ, true_and]
          rfl
        · simp only [hv, false_and, if_false]
          split_ifs
          · exact (G.subtwoQuotient block).weight_nonneg e
          · exact le_rfl
    _ ≤ 1 := C.baseColor_feasibleOn (block v) c

/-- Selected residual quotient edges, regarded as their original indexed
crossing edges. -/
def selectedResidualOriginalEdges
    (block : G.V → Q) {K : ℕ}
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (R : Finset C.residualGraph.E) : Finset G.E :=
  R.image (fun e => e.1.1)

/-- The selected residual color is lifted first through edge restriction,
then through quotient contraction. -/
def liftSelectedResidualOriginalColor
    (block : G.V → Q) {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (color : C.residualGraph.E → Fin K) : G.E → Fin K :=
  G.subtwoLiftQuotientColor hK block
    ((G.subtwoQuotient block).liftRestrictedColor hK C.residualEdges color)

theorem liftSelectedResidualOriginalColor_source
    (block : G.V → Q) {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (color : C.residualGraph.E → Fin K) (e : C.residualGraph.E) :
    G.liftSelectedResidualOriginalColor block hK C color e.1.1 = color e := by
  simp [liftSelectedResidualOriginalColor, subtwoLiftQuotientColor,
    liftRestrictedColor, e.1.2]

/-- A feasible selected coloring on the contracted residual graph is
feasible on the actual original crossing edges: each original vertex sees
only a subset of its block's selected edges. -/
theorem feasibleOn_liftSelectedResidualOriginalColor
    (block : G.V → Q) {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (R : Finset C.residualGraph.E)
    (color : C.residualGraph.E → Fin K)
    (hfeasible : C.residualGraph.IsFeasibleOn R color) :
    G.IsFeasibleOn (G.selectedResidualOriginalEdges block C R)
      (G.liftSelectedResidualOriginalColor block hK C color) := by
  classical
  intro v c
  have hinj : Function.Injective
      (fun e : C.residualGraph.E => e.1.1) := by
    intro e f h
    exact Subtype.ext (Subtype.ext h)
  calc
    G.colorLoadOn (G.selectedResidualOriginalEdges block C R)
        (G.liftSelectedResidualOriginalColor block hK C color) v c ≤
      C.residualGraph.colorLoadOn R color (block v) c := by
        unfold colorLoadOn selectedResidualOriginalEdges
        rw [Finset.sum_image hinj.injOn]
        apply Finset.sum_le_sum
        intro e he
        rw [G.liftSelectedResidualOriginalColor_source block hK C color e]
        by_cases hv : G.Inc v e.1.1
        · have hvQ : C.residualGraph.Inc (block v) e := by
            rcases hv with h | h
            · exact Or.inl (congrArg block h)
            · exact Or.inr (congrArg block h)
          simp only [hv, hvQ, true_and]
          rfl
        · simp only [hv, false_and, if_false]
          split_ifs
          · exact C.residualGraph.weight_nonneg e
          · exact le_rfl
    _ ≤ 1 := hfeasible (block v) c

/-- Positive proposal support makes the lifted residual color absent from
the physical full-packet base at both original endpoints. -/
theorem liftedResidual_not_boundaryBaseUses
    (block : G.V → Q) {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E)
    (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (R : Finset C.residualGraph.E)
    (color : C.residualGraph.E → Fin K)
    (proposal : C.residualGraph.E → Fin K → ℝ)
    (hsupport : ∀ e c, 0 < proposal e c →
      c ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).fst e.1) ∧
      c ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).snd e.1))
    (hpositive : ∀ e ∈ R, 0 < proposal e (color e))
    {e : G.E}
    (he : e ∈ G.selectedResidualOriginalEdges block C R)
    {v : G.V} (hv : G.Inc v e) :
    ¬ G.boundaryBaseUses
      (G.subtwoCrossingSelectedEdges block F) block
      (G.subtwoLiftQuotientColor hK block C.baseColor)
      (block v)
      (G.liftSelectedResidualOriginalColor block hK C color e) := by
  obtain ⟨eR, heR, heval⟩ := Finset.mem_image.mp he
  subst e
  rw [G.liftSelectedResidualOriginalColor_source block hK C color eR]
  have hs := hsupport eR (color eR) (hpositive eR heR)
  have hvQ : (G.subtwoQuotient block).Inc (block v) eR.1 := by
    rcases hv with h | h
    · exact Or.inl (congrArg block h)
    · exact Or.inr (congrArg block h)
  rcases hvQ with h | h
  · exact G.not_boundaryBaseUses_of_quotient_missing block hK C F hfull
      (block v) (color eR) (h ▸ hs.1)
  · exact G.not_boundaryBaseUses_of_quotient_missing block hK C F hfull
      (block v) (color eR) (h ▸ hs.2)

/-- The canonical six-symbol selected word at a quotient vertex decodes to
the original physical endpoint of each lifted selected residual edge. -/
theorem liftedResidual_selectedSixLabel
    (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (R : Finset C.residualGraph.E)
    (color : C.residualGraph.E → Fin K)
    (selectedLabel : Q → Fin K → Option (Fin 6))
    (hselected : ∀ e ∈ R, ∀ q (hinc : C.residualGraph.Inc q e),
      selectedLabel q (color e) =
        some (G.subtwoQuotientResidualEdgeLabel block hfiber C q
          ⟨e, hinc⟩))
    {e : G.E}
    (he : e ∈ G.selectedResidualOriginalEdges block C R)
    {v : G.V} (hv : G.Inc v e) :
    selectedLabel (block v)
      (G.liftSelectedResidualOriginalColor block hK C color e) =
        some (G.subtwoLocalSixLabel block hfiber (block v) v) := by
  obtain ⟨eR, heR, heval⟩ := Finset.mem_image.mp he
  subst e
  rw [G.liftSelectedResidualOriginalColor_source block hK C color eR]
  have hvQ : C.residualGraph.Inc (block v) eR := by
    rcases hv with h | h
    · exact Or.inl (congrArg block h)
    · exact Or.inr (congrArg block h)
  have hlabel := hselected eR heR (block v) hvQ
  rw [hlabel]
  congr 1
  exact (G.subtwoQuotientResidualEdgeLabel_eq_iff_inc
    block hfiber C (block v) ⟨eR, hvQ⟩ v rfl).2 hv

/-- One actual boundary label map covers both the recolored full packets
and the positive-support selected residual edges.  Its label classes are
bounded by the separate base and selected-word classes. -/
theorem exists_combinedPhysicalBoundaryLabel
    (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (hK : 0 < K)
    (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E)
    (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (hunique : ∀ e ∈ G.subtwoCrossingSelectedEdges block F,
      ∀ f ∈ G.subtwoCrossingSelectedEdges block F,
      ∀ v w, G.Inc v e → G.Inc w f → block v = block w →
        G.subtwoLiftQuotientColor hK block C.baseColor e =
          G.subtwoLiftQuotientColor hK block C.baseColor f → v = w)
    (R : Finset C.residualGraph.E)
    (color : C.residualGraph.E → Fin K)
    (proposal : C.residualGraph.E → Fin K → ℝ)
    (hsupport : ∀ e c, 0 < proposal e c →
      c ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).fst e.1) ∧
      c ∈ (G.subtwoQuotient block).missingColorsAt
          C.fullEdges C.baseColor ((G.subtwoQuotient block).snd e.1))
    (hpositive : ∀ e ∈ R, 0 < proposal e (color e))
    (selectedLabel : Q → Fin K → Option (Fin 6))
    (hselected : ∀ e ∈ R, ∀ q (hinc : C.residualGraph.Inc q e),
      selectedLabel q (color e) =
        some (G.subtwoQuotientResidualEdgeLabel block hfiber C q
          ⟨e, hinc⟩)) :
    ∃ boundaryLabel : Q → Fin K → Option (Fin 6),
      (∀ e ∈ G.subtwoCrossingSelectedEdges block F,
        ∀ v, G.Inc v e →
          boundaryLabel (block v)
            (G.subtwoLiftQuotientColor hK block C.baseColor e) =
              some (G.subtwoLocalSixLabel block hfiber (block v) v)) ∧
      (∀ e ∈ G.selectedResidualOriginalEdges block C R,
        ∀ v, G.Inc v e →
          boundaryLabel (block v)
            (G.liftSelectedResidualOriginalColor block hK C color e) =
              some (G.subtwoLocalSixLabel block hfiber (block v) v)) ∧
      ∀ q label,
        (Finset.univ.filter fun c : Fin K ↦
          boundaryLabel q c = some label).card ≤
          (Finset.univ.filter fun c : Fin K ↦
            ∃ v, block v = q ∧
              (∃ e ∈ G.subtwoCrossingSelectedEdges block F,
                G.Inc v e ∧
                  G.subtwoLiftQuotientColor hK block C.baseColor e = c) ∧
              G.subtwoLocalSixLabel block hfiber q v = label).card +
          (Finset.univ.filter fun c : Fin K ↦
            selectedLabel q c = some label).card := by
  let base := G.subtwoLiftQuotientColor hK block C.baseColor
  let residual := G.liftSelectedResidualOriginalColor block hK C color
  let labels : Q → G.V → Fin 6 := G.subtwoLocalSixLabel block hfiber
  let boundaryLabel := G.combinedBoundaryLabel
    (G.subtwoCrossingSelectedEdges block F) block base labels selectedLabel
  refine ⟨boundaryLabel, ?_, ?_, ?_⟩
  · intro e he v hv
    exact G.combinedBoundaryLabel_base _ block base labels selectedLabel
      hunique he hv
  · intro e he v hv
    apply G.combinedBoundaryLabel_residual
      (G.subtwoCrossingSelectedEdges block F)
      (G.selectedResidualOriginalEdges block C R)
      block base residual labels selectedLabel
    · intro f hf w hw
      exact G.liftedResidual_not_boundaryBaseUses
        block hK C F hfull R color proposal hsupport hpositive hf hw
    · intro f hf w hw
      exact G.liftedResidual_selectedSixLabel
        block hfiber hK C R color selectedLabel hselected hf hw
    · exact he
    · exact hv
  · intro q label
    exact G.combinedBoundaryLabel_class_card_le
      (G.subtwoCrossingSelectedEdges block F) block base labels
      selectedLabel q label

end
end WeightedEdgeColoring.WeightedMultigraph
