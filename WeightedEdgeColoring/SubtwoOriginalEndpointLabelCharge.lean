import WeightedEdgeColoring.SubtwoMixedGraphLocalSixLabels
import WeightedEdgeColoring.SubtwoQuotientLabelAccounting
import WeightedEdgeColoring.SubtwoPacketQuotientCharge

/-! Labelled quotient charge is charge at one original endpoint. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem subtwoQuotientOriginalEndpoint_eq_iff_inc
    (block : G.V → Q) (q : Q) (e : (G.subtwoQuotient block).StarEdge q)
    (v : G.V) (hv : block v = q) :
    G.subtwoQuotientOriginalEndpoint block q e = v ↔ G.Inc v e.1.1 := by
  unfold subtwoQuotientOriginalEndpoint
  change (if block (G.fst e.1.1) = q then G.fst e.1.1 else G.snd e.1.1) = v ↔
    G.fst e.1.1 = v ∨ G.snd e.1.1 = v
  by_cases hf : block (G.fst e.1.1) = q
  · simp only [hf, if_true]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · exact (e.1.2 (hf.trans ((congrArg block h).trans hv).symm)).elim
  · simp only [hf, if_false]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact (hf ((congrArg block h).trans hv)).elim
      · exact h

/-- The canonical six-symbol label on a residual quotient star. -/
def subtwoQuotientResidualEdgeLabel
    (block : G.V → Q) (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (q : Q) (e : C.residualGraph.StarEdge q) : Fin 6 :=
  G.subtwoQuotientEdgeLabel block hfiber q ⟨e.1.1, e.2⟩

theorem subtwoQuotientResidualEdgeLabel_eq_iff_inc
    (block : G.V → Q) (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (q : Q) (e : C.residualGraph.StarEdge q) (v : G.V) (hv : block v = q) :
    G.subtwoQuotientResidualEdgeLabel block hfiber C q e =
      G.subtwoLocalSixLabel block hfiber q v ↔ G.Inc v e.1.1.1 := by
  have hv' := (G.mem_subtwoFiber block q v).2 hv
  change G.subtwoLocalSixLabel block hfiber q
      (G.subtwoQuotientOriginalEndpoint block q ⟨e.1.1, e.2⟩) =
        G.subtwoLocalSixLabel block hfiber q v ↔ _
  constructor
  · intro h
    apply (G.subtwoQuotientOriginalEndpoint_eq_iff_inc
      block q ⟨e.1.1, e.2⟩ v hv).1
    exact G.subtwoLocalSixLabel_injective_on_fiber block hfiber q
      (G.subtwoQuotientOriginalEndpoint_mem_fiber block q ⟨e.1.1, e.2⟩) hv' h
  · intro h
    rw [(G.subtwoQuotientOriginalEndpoint_eq_iff_inc
      block q ⟨e.1.1, e.2⟩ v hv).2 h]

/-- This exact identity applies to harmonic charge, physical weight, or any
other function of an edge's weight. -/
theorem sum_quotientResidualLabelCharge_eq_original
    (block : G.V → Q) (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (q : Q) (v : G.V) (hv : block v = q) (charge : ℝ → ℝ) :
    (∑ e : C.residualGraph.StarEdge q,
      if G.subtwoQuotientResidualEdgeLabel block hfiber C q e =
          G.subtwoLocalSixLabel block hfiber q v
        then charge (C.residualGraph.weight e.1) else 0) =
    G.chargeOn charge (G.subtwoCrossingSelectedEdges block Finset.univ \ F) v := by
  classical
  rw [← Finset.sum_filter]
  unfold chargeOn
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun e _ => e.1.1.1)
  · intro e he
    have hlabel := (Finset.mem_filter.mp he).2
    have hinc := (G.subtwoQuotientResidualEdgeLabel_eq_iff_inc
      block hfiber C q e v hv).1 hlabel
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, hinc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.1.1.2⟩
    · intro heF
      have hnot := (Finset.mem_sdiff.mp e.1.2).2
      apply hnot
      rw [hfull]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heF⟩
  · intro e _ f _ hef
    exact Subtype.ext (Subtype.ext (Subtype.ext hef))
  · intro e he
    have h := Finset.mem_filter.mp he
    have hcross := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h.1).1).2
    have hnot := (Finset.mem_sdiff.mp h.1).2
    let eQ : (G.subtwoQuotient block).E := ⟨e,hcross⟩
    have heR : eQ ∈ C.residualEdges := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hfull]
      intro heF
      exact hnot (Finset.mem_filter.mp heF).2
    have hiQ : (G.subtwoQuotient block).Inc q eQ := by
      rcases h.2 with hfst | hsnd
      · exact Or.inl ((congrArg block hfst).trans hv)
      · exact Or.inr ((congrArg block hsnd).trans hv)
    let eR : C.residualGraph.StarEdge q := ⟨⟨eQ,heR⟩,hiQ⟩
    refine ⟨eR, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact (G.subtwoQuotientResidualEdgeLabel_eq_iff_inc
      block hfiber C q eR v hv).2 h.2
  · intro e _
    rfl

theorem quotientResidual_labelledTinyWeight_le_local
    (block : G.V → Q) (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K n : ℕ} (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (finite : Finset C.residualGraph.E)
    (q : Q) (v : G.V) (hv : block v = q) (hlocal : G.LocallyPacksInto n) :
    (∑ e : C.residualGraph.StarEdge q,
      if G.subtwoQuotientResidualEdgeLabel block hfiber C q e =
          G.subtwoLocalSixLabel block hfiber q v ∧ e.1 ∉ finite
        then C.residualGraph.weight e.1 else 0) ≤ n := by
  classical
  calc
    _ ≤ ∑ e : C.residualGraph.StarEdge q,
        if G.subtwoQuotientResidualEdgeLabel block hfiber C q e =
          G.subtwoLocalSixLabel block hfiber q v
        then C.residualGraph.weight e.1 else 0 := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hl : G.subtwoQuotientResidualEdgeLabel block hfiber C q e =
          G.subtwoLocalSixLabel block hfiber q v
      · by_cases he : e.1 ∈ finite
        · simpa only [hl, he, not_true_eq_false, and_false, if_false, if_true]
            using C.residualGraph.weight_nonneg e.1
        · simp only [hl, he, not_false_eq_true, and_self, if_true, le_refl]
      · simp only [hl, false_and, if_false, le_refl]
    _ = G.chargeOn (fun w => w)
        (G.subtwoCrossingSelectedEdges block Finset.univ \ F) v :=
      G.sum_quotientResidualLabelCharge_eq_original block hfiber C F hfull q v hv
        (fun w : ℝ => w)
    _ ≤ G.starWeight v := by
      rw [G.starWeight_eq_inc_sum]
      unfold chargeOn
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro e _ _
      split_ifs
      · exact G.weight_nonneg e
      · exact le_rfl
    _ ≤ n := G.starWeight_le_of_packsStarInto (hlocal v)

/-- All colors of the local law are charged to the original residual star.
In particular, the inflation here depends on `n`, not on the block size. -/
theorem sum_quotientLabelMass_le_originalResidualCharge
    (block : G.V → Q) (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K n : ℕ} (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (finite : Finset C.residualGraph.E) (tau : ℝ)
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (q : Q) (v : G.V) (hv : block v = q) (hlocal : G.LocallyPacksInto n)
    {Color : Type*} [Fintype Color]
    (x : C.residualGraph.E → Color → ℝ)
    (labelMass : Color → ℝ) (overhead : ℝ)
    (hmass : ∀ e, ∑ c, x e c ≤ 1)
    (hlabel : ∀ c, labelMass c ≤
      (∑ e : C.residualGraph.StarEdge q,
        if G.subtwoQuotientResidualEdgeLabel block hfiber C q e =
          G.subtwoLocalSixLabel block hfiber q v
        then C.quotientSplitCharge finite tau e.1 * x e.1 c else 0) + overhead) :
    (∑ c, labelMass c) ≤
      G.chargeOn harmonicCharge
        (G.subtwoCrossingSelectedEdges block Finset.univ \ F) v +
          2 * tau * n + Fintype.card Color * overhead := by
  have hsum := C.sum_labelMass_le_splitLabelCharge finite tau (by linarith)
    q (G.subtwoQuotientResidualEdgeLabel block hfiber C q)
    (G.subtwoLocalSixLabel block hfiber q v) x labelMass overhead hmass hlabel
  have hinflate := C.splitLabelCharge_le_harmonic_add_twoTau finite tau n
    htau0 htauHalf (Nat.cast_nonneg n)
    q (G.subtwoQuotientResidualEdgeLabel block hfiber C q)
    (G.subtwoLocalSixLabel block hfiber q v)
    (G.quotientResidual_labelledTinyWeight_le_local
      block hfiber C F hfull finite q v hv hlocal)
  rw [G.sum_quotientResidualLabelCharge_eq_original
    block hfiber C F hfull q v hv harmonicCharge] at hinflate
  exact hsum.trans (add_le_add hinflate le_rfl)

end
end WeightedEdgeColoring.WeightedMultigraph
