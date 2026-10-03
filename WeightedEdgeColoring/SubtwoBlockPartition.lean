import WeightedEdgeColoring.SubtwoBlockSelection
import WeightedEdgeColoring.SubtwoBlockMerging
import WeightedEdgeColoring.SubtwoQuotientBounds
import Mathlib.Tactic

/-!
# Concrete quotient labels for disjoint selected blocks

Given a finite disjoint family of vertex sets, each selected vertex is labelled
by its unique block and each other vertex by its singleton. The quotient type
contains precisely the labels that occur, so it has no empty fibers.
-/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable def subtwoSelectedLabel
    (F : Finset (Finset G.V)) (v : G.V) : Finset G.V :=
  if h : ∃ S ∈ F, v ∈ S then Classical.choose h else {v}

theorem subtwoSelectedLabel_mem_self
    (F : Finset (Finset G.V)) (v : G.V) :
    v ∈ G.subtwoSelectedLabel F v := by
  classical
  unfold subtwoSelectedLabel
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · simp

theorem subtwoSelectedLabel_eq_of_mem
    (F : Finset (Finset G.V))
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (S : Finset G.V) (hS : S ∈ F) (v : G.V) (hv : v ∈ S) :
    G.subtwoSelectedLabel F v = S := by
  classical
  unfold subtwoSelectedLabel
  have h : ∃ T ∈ F, v ∈ T := ⟨S, hS, hv⟩
  rw [dif_pos h]
  obtain ⟨hT, hvT⟩ := Classical.choose_spec h
  by_contra hne
  have hd := hdis (Classical.choose h) hT S hS hne
  exact (Finset.disjoint_left.mp hd) hvT hv

theorem subtwoSelectedLabel_eq_singleton_of_unused
    (F : Finset (Finset G.V)) (v : G.V)
    (hunused : ∀ S ∈ F, v ∉ S) :
    G.subtwoSelectedLabel F v = {v} := by
  classical
  unfold subtwoSelectedLabel
  rw [dif_neg]
  rintro ⟨S, hS, hv⟩
  exact hunused S hS hv

/-- The quotient has one vertex for each actual selected block or unused
singleton. -/
abbrev SubtwoSelectedQuotient (F : Finset (Finset G.V)) :=
  {S : Finset G.V // S ∈ Set.range (G.subtwoSelectedLabel F)}

noncomputable instance subtwoSelectedQuotientFintype
    (F : Finset (Finset G.V)) : Fintype (G.SubtwoSelectedQuotient F) :=
  Fintype.ofFinite _

noncomputable def subtwoSelectedBlock
    (F : Finset (Finset G.V)) (v : G.V) : G.SubtwoSelectedQuotient F :=
  ⟨G.subtwoSelectedLabel F v, ⟨v, rfl⟩⟩

theorem subtwoSelectedBlock_fiber_eq
    (F : Finset (Finset G.V))
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (S : Finset G.V) (hS : S ∈ F) (v : G.V) (hv : v ∈ S) :
    G.subtwoFiber (G.subtwoSelectedBlock F)
      (G.subtwoSelectedBlock F v) = S := by
  classical
  have hlabel := G.subtwoSelectedLabel_eq_of_mem F hdis S hS v hv
  ext w
  simp only [G.mem_subtwoFiber, subtwoSelectedBlock, Subtype.mk.injEq]
  rw [hlabel]
  constructor
  · intro hw
    rw [← hw]
    exact G.subtwoSelectedLabel_mem_self F w
  · intro hw
    exact G.subtwoSelectedLabel_eq_of_mem F hdis S hS w hw

theorem subtwoSelectedBlock_unused_fiber_eq
    (F : Finset (Finset G.V))
    (v : G.V) (hunused : ∀ S ∈ F, v ∉ S) :
    G.subtwoFiber (G.subtwoSelectedBlock F)
      (G.subtwoSelectedBlock F v) = {v} := by
  classical
  have hlabel := G.subtwoSelectedLabel_eq_singleton_of_unused F v hunused
  ext w
  simp only [G.mem_subtwoFiber, subtwoSelectedBlock, Subtype.mk.injEq]
  rw [hlabel]
  constructor
  · intro hw
    have hmem := G.subtwoSelectedLabel_mem_self F w
    rw [hw] at hmem
    simpa using hmem
  · intro hw
    have heq : w = v := by simpa using hw
    subst w
    exact hlabel

theorem subtwoSelectedBlock_fiber_eq_label
    (F : Finset (Finset G.V))
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (q : G.SubtwoSelectedQuotient F) :
    G.subtwoFiber (G.subtwoSelectedBlock F) q = q.val := by
  classical
  obtain ⟨v, hv⟩ := q.property
  have hq : q = G.subtwoSelectedBlock F v := Subtype.ext hv.symm
  subst q
  by_cases h : ∃ S ∈ F, v ∈ S
  · obtain ⟨S, hS, hvS⟩ := h
    rw [G.subtwoSelectedBlock_fiber_eq F hdis S hS v hvS]
    exact (G.subtwoSelectedLabel_eq_of_mem F hdis S hS v hvS).symm
  · have hunused : ∀ S ∈ F, v ∉ S := by
      intro S hS hvS
      exact h ⟨S, hS, hvS⟩
    rw [G.subtwoSelectedBlock_unused_fiber_eq F v hunused]
    exact (G.subtwoSelectedLabel_eq_singleton_of_unused F v hunused).symm

theorem subtwoSelectedQuotient_classify
    (F : Finset (Finset G.V))
    (hdis : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (q : G.SubtwoSelectedQuotient F) :
    q.val ∈ F ∨ ∃ v : G.V, q.val = {v} ∧
      (∀ S ∈ F, v ∉ S) := by
  classical
  obtain ⟨v, hv⟩ := q.property
  by_cases h : ∃ S ∈ F, v ∈ S
  · obtain ⟨S, hS, hvS⟩ := h
    left
    have hlabel := G.subtwoSelectedLabel_eq_of_mem F hdis S hS v hvS
    rw [hlabel] at hv
    exact hv ▸ hS
  · right
    refine ⟨v, ?_, ?_⟩
    · exact hv.symm.trans (G.subtwoSelectedLabel_eq_singleton_of_unused F v
        (by intro S hS hvS; exact h ⟨S, hS, hvS⟩))
    · intro S hS hvS
      exact h ⟨S, hS, hvS⟩

theorem subtwoSelectedBlock_surjective
    (F : Finset (Finset G.V)) :
    Function.Surjective (G.subtwoSelectedBlock F) := by
  intro q
  obtain ⟨v, hv⟩ := q.property
  exact ⟨v, Subtype.ext hv⟩

theorem subtwoSelectedBlock_expand_injective
    (F : Finset (Finset G.V)) :
    Function.Injective (G.subtwoExpand (G.subtwoSelectedBlock F)) := by
  intro S T h
  ext q
  obtain ⟨v, rfl⟩ := G.subtwoSelectedBlock_surjective F q
  have hv : v ∈ G.subtwoExpand (G.subtwoSelectedBlock F) S ↔
      v ∈ G.subtwoExpand (G.subtwoSelectedBlock F) T := by
    rw [h]
  simpa using hv

/-- The first quotient is constructed from the canonical family of all
original dense triangles. -/
abbrev SubtwoFirstQuotient (cost : G.E → ℝ) :=
  G.SubtwoSelectedQuotient (G.subtwoDenseTriangles cost subtwoKappa)

noncomputable def subtwoFirstBlock (cost : G.E → ℝ) :
    G.V → G.SubtwoFirstQuotient cost :=
  G.subtwoSelectedBlock (G.subtwoDenseTriangles cost subtwoKappa)

def subtwoFirstRank (cost : G.E → ℝ)
    (q : G.SubtwoFirstQuotient cost) : ℕ :=
  if q.val.card = 3 then 1 else 0

theorem subtwoFirstRank_le_one (cost : G.E → ℝ)
    (q : G.SubtwoFirstQuotient cost) :
    G.subtwoFirstRank cost q ≤ 1 := by
  unfold subtwoFirstRank
  split_ifs <;> omega

theorem subtwoFirstBlock_fiber
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFirstQuotient cost) :
    G.subtwoFiber (G.subtwoFirstBlock cost) q = q.val := by
  apply G.subtwoSelectedBlock_fiber_eq_label
  exact G.subtwoDenseTriangles_pairwise_disjoint cost subtwoM subtwoKappa
    hcost hpair hdegree
    (by unfold subtwoM subtwoKappa; norm_num)
    (by unfold subtwoM subtwoKappa; norm_num)

theorem subtwoFirstBlock_fiber_card
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFirstQuotient cost) :
    (G.subtwoFiber (G.subtwoFirstBlock cost) q).card =
      1 + 2 * G.subtwoFirstRank cost q := by
  have hdis := G.subtwoDenseTriangles_pairwise_disjoint cost subtwoM
    subtwoKappa hcost hpair hdegree
    (by unfold subtwoM subtwoKappa; norm_num)
    (by unfold subtwoM subtwoKappa; norm_num)
  rw [G.subtwoFirstBlock_fiber cost hcost hpair hdegree]
  rcases G.subtwoSelectedQuotient_classify _ hdis q with hsel | ⟨v, hv, _⟩
  · have hcard := (G.mem_subtwoDenseTriangles cost subtwoKappa q.val).mp hsel
    simp [subtwoFirstRank, hcard.1]
  · rw [hv]
    have hnot : q.val.card ≠ 3 := by rw [hv]; simp
    simp [subtwoFirstRank, hv]

theorem subtwoFirstBlock_dense_fiber
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFirstQuotient cost)
    (hrank : G.subtwoFirstRank cost q = 1) :
    subtwoKappa < G.subtwoInternalCost cost
      (G.subtwoFiber (G.subtwoFirstBlock cost) q) := by
  have hdis := G.subtwoDenseTriangles_pairwise_disjoint cost subtwoM
    subtwoKappa hcost hpair hdegree
    (by unfold subtwoM subtwoKappa; norm_num)
    (by unfold subtwoM subtwoKappa; norm_num)
  rw [G.subtwoFirstBlock_fiber cost hcost hpair hdegree]
  rcases G.subtwoSelectedQuotient_classify _ hdis q with hsel | ⟨v, hv, _⟩
  · exact ((G.mem_subtwoDenseTriangles cost subtwoKappa q.val).mp hsel).2
  · have hcard : q.val.card = 1 := by rw [hv]; simp
    unfold subtwoFirstRank at hrank
    simp [hcard] at hrank

/-- The middle selection runs on the quotient actually constructed from
all original dense triangles. -/
noncomputable def subtwoActualMiddleTriangles (cost : G.E → ℝ) :
    Finset (Finset (G.SubtwoFirstQuotient cost)) :=
  G.subtwoMiddleDenseTriangles (G.subtwoFirstBlock cost)
    (G.subtwoFirstRank cost) cost

theorem subtwoActualMiddleTriangles_pairwise_disjoint
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM) :
    ∀ S ∈ G.subtwoActualMiddleTriangles cost,
      ∀ T ∈ G.subtwoActualMiddleTriangles cost,
        S ≠ T → Disjoint S T := by
  exact G.subtwoMiddleDenseTriangles_pairwise_disjoint
    (G.subtwoFirstBlock cost) (G.subtwoFirstRank cost) cost
    hcost hdegree
    (G.subtwoFirstBlock_fiber_card cost hcost hpair hdegree)
    (G.subtwoFirstRank_le_one cost)
    (G.subtwoFirstBlock_dense_fiber cost hcost hpair hdegree)

theorem subtwoActualMiddleTriangles_lift
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFirstQuotient cost))
    (hS : S ∈ G.subtwoActualMiddleTriangles cost) :
    (G.subtwoExpand (G.subtwoFirstBlock cost) S).card = 5 ∧
      2 * subtwoKappa < G.subtwoInternalCost cost
        (G.subtwoExpand (G.subtwoFirstBlock cost) S) := by
  exact G.subtwoMiddleDenseTriangles_lift
    (G.subtwoFirstBlock cost) (G.subtwoFirstRank cost) cost
    hcost
    (G.subtwoFirstBlock_fiber_card cost hcost hpair hdegree)
    (G.subtwoFirstBlock_dense_fiber cost hcost hpair hdegree)
    S hS

theorem subtwoActualMiddleTriangles_expansions_disjoint
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S T : Finset (G.SubtwoFirstQuotient cost))
    (hS : S ∈ G.subtwoActualMiddleTriangles cost)
    (hT : T ∈ G.subtwoActualMiddleTriangles cost)
    (hne : S ≠ T) :
    Disjoint (G.subtwoExpand (G.subtwoFirstBlock cost) S)
      (G.subtwoExpand (G.subtwoFirstBlock cost) T) := by
  exact G.subtwoMiddleDenseTriangles_expansions_disjoint
    (G.subtwoFirstBlock cost) (G.subtwoFirstRank cost) cost
    hcost hdegree
    (G.subtwoFirstBlock_fiber_card cost hcost hpair hdegree)
    (G.subtwoFirstRank_le_one cost)
    (G.subtwoFirstBlock_dense_fiber cost hcost hpair hdegree)
    S T hS hT hne

/-- No one-block dense quotient triangle remains outside the canonical
middle family. -/
theorem subtwoActualMiddleTriangles_exhaust
    (cost : G.E → ℝ)
    (S : Finset (G.SubtwoFirstQuotient cost))
    (hcard : S.card = 3)
    (hrank : (∑ q ∈ S, G.subtwoFirstRank cost q) = 1)
    (hnot : S ∉ G.subtwoActualMiddleTriangles cost) :
    (G.subtwoQuotient (G.subtwoFirstBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S ≤ subtwoKappa := by
  by_contra h
  have hdense : subtwoKappa <
      (G.subtwoQuotient (G.subtwoFirstBlock cost)).subtwoInternalCost
        (fun e => cost e.1) S := lt_of_not_ge h
  exact hnot ((G.mem_subtwoMiddleDenseTriangles
    (G.subtwoFirstBlock cost) (G.subtwoFirstRank cost) cost S).mpr
      ⟨hcard, hrank, hdense⟩)

/-- Original vertices used by the middle-stage five-blocks. -/
noncomputable def subtwoActualMiddleVertices (cost : G.E → ℝ) :
    Finset G.V :=
  (G.subtwoActualMiddleTriangles cost).biUnion
    (G.subtwoExpand (G.subtwoFirstBlock cost))

/-- First-stage triangles incorporated in a middle five-block are removed
from the final list; the others remain as three-blocks. -/
noncomputable def subtwoRemainingTriangles (cost : G.E → ℝ) :
    Finset (Finset G.V) :=
  (G.subtwoDenseTriangles cost subtwoKappa).filter fun S =>
    Disjoint S (G.subtwoActualMiddleVertices cost)

/-- The second-stage five-blocks in the original graph. -/
noncomputable def subtwoMiddleFives (cost : G.E → ℝ) :
    Finset (Finset G.V) :=
  (G.subtwoActualMiddleTriangles cost).image
    (G.subtwoExpand (G.subtwoFirstBlock cost))

/-- The third-stage dense five-blocks use only ordinary vertices left
after the middle selection. -/
noncomputable def subtwoFinalOrdinaryFives (cost : G.E → ℝ) :
    Finset (Finset G.V) :=
  (G.subtwoDenseOrdinaryFives cost subtwoKappa).filter fun S =>
    Disjoint S (G.subtwoActualMiddleVertices cost)

/-- This is the actual three-stage selected family. Its complement is
partitioned into singleton fibers by `subtwoSelectedBlock`. -/
noncomputable def subtwoThreeStageBlocks (cost : G.E → ℝ) :
    Finset (Finset G.V) :=
  (G.subtwoRemainingTriangles cost ∪ G.subtwoMiddleFives cost) ∪
    G.subtwoFinalOrdinaryFives cost

/-- A first-stage triangle touched by the middle selection is entirely
inside one middle-stage expansion. -/
theorem subtwo_original_triangle_middle_all_or_none
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset G.V)
    (hS : S ∈ G.subtwoDenseTriangles cost subtwoKappa) :
    S ⊆ G.subtwoActualMiddleVertices cost ∨
      Disjoint S (G.subtwoActualMiddleVertices cost) := by
  classical
  by_cases htouch : ∃ v ∈ S, v ∈ G.subtwoActualMiddleVertices cost
  · left
    obtain ⟨v, hvS, hvMiddle⟩ := htouch
    obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hvMiddle
    have hdis := G.subtwoDenseTriangles_pairwise_disjoint cost
      subtwoM subtwoKappa hcost hpair hdegree
      (by unfold subtwoM subtwoKappa; norm_num)
      (by unfold subtwoM subtwoKappa; norm_num)
    intro w hwS
    apply Finset.mem_biUnion.mpr
    refine ⟨T, hT, ?_⟩
    have heqv := G.subtwoSelectedLabel_eq_of_mem
      (G.subtwoDenseTriangles cost subtwoKappa) hdis S hS v hvS
    have heqw := G.subtwoSelectedLabel_eq_of_mem
      (G.subtwoDenseTriangles cost subtwoKappa) hdis S hS w hwS
    have hblock : G.subtwoFirstBlock cost w =
        G.subtwoFirstBlock cost v := Subtype.ext (heqw.trans heqv.symm)
    rw [G.mem_subtwoExpand, hblock]
    exact (G.mem_subtwoExpand (G.subtwoFirstBlock cost) T v).mp hvT
  · right
    apply Finset.disjoint_left.mpr
    intro v hvS hvMiddle
    exact htouch ⟨v, hvS, hvMiddle⟩

/-- Every original vertex left as a final singleton is outside the
first-stage triangle union. -/
theorem subtwo_unused_final_vertex_ordinary
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (v : G.V)
    (hunused : ∀ S ∈ G.subtwoThreeStageBlocks cost, v ∉ S) :
    v ∈ G.subtwoOrdinaryAfterTriangles cost subtwoKappa := by
  classical
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ v, ?_⟩
  intro hvTri
  obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp hvTri
  rcases G.subtwo_original_triangle_middle_all_or_none cost hcost
    hpair hdegree S hS with hcovered | hfree
  · obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp (hcovered hvS)
    have hblock : G.subtwoExpand (G.subtwoFirstBlock cost) T ∈
        G.subtwoThreeStageBlocks cost := by
      simp only [subtwoThreeStageBlocks, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨T, hT, rfl⟩))
    exact hunused _ hblock hvT
  · have hremain : S ∈ G.subtwoThreeStageBlocks cost := by
      simp only [subtwoThreeStageBlocks, Finset.mem_union,
        subtwoRemainingTriangles, Finset.mem_filter]
      exact Or.inl (Or.inl ⟨hS, hfree⟩)
    exact hunused S hremain hvS

theorem subtwo_middle_five_subset_vertices
    (cost : G.E → ℝ) (S : Finset G.V)
    (hS : S ∈ G.subtwoMiddleFives cost) :
    S ⊆ G.subtwoActualMiddleVertices cost := by
  classical
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨T, hT, hv⟩

theorem subtwoMiddleFives_pairwise_disjoint
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM) :
    ∀ S ∈ G.subtwoMiddleFives cost,
      ∀ T ∈ G.subtwoMiddleFives cost,
        S ≠ T → Disjoint S T := by
  intro S hS T hT hne
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hT
  apply G.subtwoActualMiddleTriangles_expansions_disjoint cost
    hcost hpair hdegree A B hA hB
  intro heq
  exact hne (congrArg _ heq)

theorem subtwoThreeStageBlocks_pairwise_disjoint
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM) :
    ∀ S ∈ G.subtwoThreeStageBlocks cost,
      ∀ T ∈ G.subtwoThreeStageBlocks cost,
        S ≠ T → Disjoint S T := by
  classical
  have htri := G.subtwoDenseTriangles_pairwise_disjoint cost
    subtwoM subtwoKappa hcost hpair hdegree
      (by unfold subtwoM subtwoKappa; norm_num)
      (by unfold subtwoM subtwoKappa; norm_num)
  have hfive := G.subtwoDenseOrdinaryFives_pairwise_disjoint
    cost hcost hdegree hpair
  have hmiddle := G.subtwoMiddleFives_pairwise_disjoint
    cost hcost hpair hdegree
  intro S hS T hT hne
  simp only [subtwoThreeStageBlocks, Finset.mem_union,
    subtwoRemainingTriangles, subtwoFinalOrdinaryFives,
    Finset.mem_filter] at hS hT
  rcases hS with ((⟨hSdense, hSfree⟩ | hSmiddle) | ⟨hSfive, hSfree⟩) <;>
    rcases hT with ((⟨hTdense, hTfree⟩ | hTmiddle) | ⟨hTfive, hTfree⟩)
  · exact htri S hSdense T hTdense hne
  · exact Finset.disjoint_of_subset_right
      (G.subtwo_middle_five_subset_vertices cost T hTmiddle) hSfree
  · exact G.subtwo_triangle_five_disjoint cost S T hSdense hTfive
  · exact (Finset.disjoint_of_subset_right
      (G.subtwo_middle_five_subset_vertices cost S hSmiddle) hTfree).symm
  · exact hmiddle S hSmiddle T hTmiddle hne
  · exact (Finset.disjoint_of_subset_right
      (G.subtwo_middle_five_subset_vertices cost S hSmiddle) hTfree).symm
  · exact (G.subtwo_triangle_five_disjoint cost T S hTdense hSfive).symm
  · exact Finset.disjoint_of_subset_right
      (G.subtwo_middle_five_subset_vertices cost T hTmiddle) hSfree
  · exact hfive S hSfive T hTfive hne

theorem subtwoThreeStageBlocks_density
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset G.V) (hS : S ∈ G.subtwoThreeStageBlocks cost) :
    (S.card = 3 ∧ subtwoKappa < G.subtwoInternalCost cost S) ∨
      (S.card = 5 ∧ 2 * subtwoKappa < G.subtwoInternalCost cost S) := by
  classical
  simp only [subtwoThreeStageBlocks, Finset.mem_union,
    subtwoRemainingTriangles, subtwoFinalOrdinaryFives,
    Finset.mem_filter] at hS
  rcases hS with ((⟨hS, _⟩ | hS) | ⟨hS, _⟩)
  · exact Or.inl ((G.mem_subtwoDenseTriangles cost subtwoKappa S).mp hS)
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact Or.inr (G.subtwoActualMiddleTriangles_lift cost
      hcost hpair hdegree T hT)
  · have h := (G.mem_subtwoDenseOrdinaryFives cost subtwoKappa S).mp hS
    exact Or.inr ⟨h.1, h.2.2⟩

/-- The actual final quotient map contracts the three selected families
and leaves every other original vertex as a singleton. -/
abbrev SubtwoFinalQuotient (cost : G.E → ℝ) :=
  G.SubtwoSelectedQuotient (G.subtwoThreeStageBlocks cost)

noncomputable def subtwoFinalBlock (cost : G.E → ℝ) :
    G.V → G.SubtwoFinalQuotient cost :=
  G.subtwoSelectedBlock (G.subtwoThreeStageBlocks cost)

def subtwoFinalRank (cost : G.E → ℝ)
    (q : G.SubtwoFinalQuotient cost) : ℕ :=
  if q.val.card = 3 then 1 else if q.val.card = 5 then 2 else 0

theorem subtwoFinalBlock_fiber
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFinalQuotient cost) :
    G.subtwoFiber (G.subtwoFinalBlock cost) q = q.val := by
  apply G.subtwoSelectedBlock_fiber_eq_label
  exact G.subtwoThreeStageBlocks_pairwise_disjoint cost
    hcost hpair hdegree

theorem subtwoFinalBlock_fiber_card
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFinalQuotient cost) :
    (G.subtwoFiber (G.subtwoFinalBlock cost) q).card =
      1 + 2 * G.subtwoFinalRank cost q := by
  have hdis := G.subtwoThreeStageBlocks_pairwise_disjoint cost
    hcost hpair hdegree
  rw [G.subtwoFinalBlock_fiber cost hcost hpair hdegree]
  rcases G.subtwoSelectedQuotient_classify _ hdis q with hsel | ⟨v, hv, _⟩
  · rcases G.subtwoThreeStageBlocks_density cost hcost hpair hdegree
      q.val hsel with ⟨hcard, _⟩ | ⟨hcard, _⟩
    · simp [subtwoFinalRank, hcard]
    · simp [subtwoFinalRank, hcard]
  · rw [hv]
    have hcard : q.val.card = 1 := by rw [hv]; simp
    simp [subtwoFinalRank, hv]

theorem subtwoFinalBlock_fiber_paid
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFinalQuotient cost) :
    (G.subtwoFinalRank cost q : ℝ) * subtwoKappa ≤
      G.subtwoInternalCost cost
        (G.subtwoFiber (G.subtwoFinalBlock cost) q) := by
  have hdis := G.subtwoThreeStageBlocks_pairwise_disjoint cost
    hcost hpair hdegree
  rw [G.subtwoFinalBlock_fiber cost hcost hpair hdegree]
  rcases G.subtwoSelectedQuotient_classify _ hdis q with hsel | ⟨v, hv, _⟩
  · rcases G.subtwoThreeStageBlocks_density cost hcost hpair hdegree
      q.val hsel with ⟨hcard, hdense⟩ | ⟨hcard, hdense⟩
    · simpa [subtwoFinalRank, hcard] using hdense.le
    · simpa [subtwoFinalRank, hcard] using hdense.le
  · have hzero : G.subtwoInternalCost cost q.val = 0 := by
      rw [hv]
      exact G.subtwo_internal_singleton cost v
    have hcard : q.val.card = 1 := by rw [hv]; simp
    have hrank : G.subtwoFinalRank cost q = 0 := by
      simp [subtwoFinalRank, hcard]
    rw [hrank]
    norm_num
    rw [hzero]

theorem subtwoFinalRank_zero_classify
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFinalQuotient cost)
    (hzero : G.subtwoFinalRank cost q = 0) :
    ∃ v : G.V, q.val = {v} ∧
      (∀ S ∈ G.subtwoThreeStageBlocks cost, v ∉ S) := by
  have hdis := G.subtwoThreeStageBlocks_pairwise_disjoint cost
    hcost hpair hdegree
  rcases G.subtwoSelectedQuotient_classify _ hdis q with hsel | hsingle
  · rcases G.subtwoThreeStageBlocks_density cost hcost hpair hdegree
      q.val hsel with ⟨hcard, _⟩ | ⟨hcard, _⟩
    · simp [subtwoFinalRank, hcard] at hzero
    · simp [subtwoFinalRank, hcard] at hzero
  · exact hsingle

theorem subtwoFinalRank_one_classify
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFinalQuotient cost)
    (hone : G.subtwoFinalRank cost q = 1) :
    q.val ∈ G.subtwoRemainingTriangles cost := by
  classical
  have hcard : q.val.card = 3 := by
    unfold subtwoFinalRank at hone
    split_ifs at hone with h3 h5 <;> omega
  have hdis := G.subtwoThreeStageBlocks_pairwise_disjoint cost
    hcost hpair hdegree
  rcases G.subtwoSelectedQuotient_classify _ hdis q with hsel | ⟨v, hv, _⟩
  · simp only [subtwoThreeStageBlocks, Finset.mem_union] at hsel
    rcases hsel with ((hremain | hmiddle) | hfive)
    · exact hremain
    · obtain ⟨T, hT, hTval⟩ := Finset.mem_image.mp hmiddle
      have hc := (G.subtwoActualMiddleTriangles_lift cost
        hcost hpair hdegree T hT).1
      rw [hTval] at hc
      omega
    · have hc := ((G.mem_subtwoDenseOrdinaryFives cost
        subtwoKappa q.val).mp (Finset.mem_filter.mp hfive).1).1
      omega
  · rw [hv] at hcard
    simp at hcard

noncomputable def subtwoFirstOfFinal (cost : G.E → ℝ)
    (q : G.SubtwoFinalQuotient cost) : G.SubtwoFirstQuotient cost :=
  G.subtwoFirstBlock cost (Classical.choose q.property)

theorem subtwoFirstOfFinal_corresponds
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (q : G.SubtwoFinalQuotient cost)
    (hrank : G.subtwoFinalRank cost q ≤ 1) :
    G.subtwoFiber (G.subtwoFirstBlock cost)
      (G.subtwoFirstOfFinal cost q) = q.val ∧
      G.subtwoFirstRank cost (G.subtwoFirstOfFinal cost q) =
        G.subtwoFinalRank cost q := by
  classical
  let v := Classical.choose q.property
  have hvlabel : G.subtwoSelectedLabel
      (G.subtwoThreeStageBlocks cost) v = q.val :=
    Classical.choose_spec q.property
  have hvq : v ∈ q.val := by
    rw [← hvlabel]
    exact G.subtwoSelectedLabel_mem_self
      (G.subtwoThreeStageBlocks cost) v
  have hdis := G.subtwoDenseTriangles_pairwise_disjoint cost
    subtwoM subtwoKappa hcost hpair hdegree
    (by unfold subtwoM subtwoKappa; norm_num)
    (by unfold subtwoM subtwoKappa; norm_num)
  by_cases hzero : G.subtwoFinalRank cost q = 0
  · obtain ⟨w, hw, hunused⟩ := G.subtwoFinalRank_zero_classify
      cost hcost hpair hdegree q hzero
    have hvw : v = w := by simpa [hw] using hvq
    subst w
    have hvOrd := G.subtwo_unused_final_vertex_ordinary
      cost hcost hpair hdegree v hunused
    have hnone : ∀ T ∈ G.subtwoDenseTriangles cost subtwoKappa,
        v ∉ T := by
      intro T hT hvT
      have hvOcc : v ∈ G.subtwoTriangleVertices cost subtwoKappa :=
        Finset.mem_biUnion.mpr ⟨T, hT, hvT⟩
      exact (Finset.mem_sdiff.mp hvOrd).2 hvOcc
    have hfirst : G.subtwoSelectedLabel
        (G.subtwoDenseTriangles cost subtwoKappa) v = {v} :=
      G.subtwoSelectedLabel_eq_singleton_of_unused _ v hnone
    have hfiber := G.subtwoSelectedBlock_unused_fiber_eq
      (G.subtwoDenseTriangles cost subtwoKappa) v hnone
    constructor
    · change G.subtwoFiber
        (G.subtwoSelectedBlock (G.subtwoDenseTriangles cost subtwoKappa))
        (G.subtwoSelectedBlock (G.subtwoDenseTriangles cost subtwoKappa) v) =
        q.val
      exact hfiber.trans hw.symm
    · change (if (G.subtwoSelectedLabel
          (G.subtwoDenseTriangles cost subtwoKappa) v).card = 3
          then 1 else 0) = G.subtwoFinalRank cost q
      rw [hfirst, hzero]
      simp
  · have hone : G.subtwoFinalRank cost q = 1 := by omega
    have hremain := G.subtwoFinalRank_one_classify
      cost hcost hpair hdegree q hone
    have hT : q.val ∈ G.subtwoDenseTriangles cost subtwoKappa :=
      (Finset.mem_filter.mp hremain).1
    have hfirst := G.subtwoSelectedLabel_eq_of_mem
      (G.subtwoDenseTriangles cost subtwoKappa) hdis
      q.val hT v hvq
    have hfiber := G.subtwoSelectedBlock_fiber_eq
      (G.subtwoDenseTriangles cost subtwoKappa) hdis
      q.val hT v hvq
    have hcard := ((G.mem_subtwoDenseTriangles cost subtwoKappa q.val).mp hT).1
    constructor
    · change G.subtwoFiber
        (G.subtwoSelectedBlock (G.subtwoDenseTriangles cost subtwoKappa))
        (G.subtwoSelectedBlock (G.subtwoDenseTriangles cost subtwoKappa) v) =
        q.val
      exact hfiber
    · change (if (G.subtwoSelectedLabel
          (G.subtwoDenseTriangles cost subtwoKappa) v).card = 3
          then 1 else 0) = G.subtwoFinalRank cost q
      rw [hfirst, hcard, hone]
      simp

theorem subtwo_unused_final_vertex_not_middle
    (cost : G.E → ℝ)
    (v : G.V)
    (hunused : ∀ S ∈ G.subtwoThreeStageBlocks cost, v ∉ S) :
    v ∉ G.subtwoActualMiddleVertices cost := by
  classical
  intro hv
  obtain ⟨T, hT, hvT⟩ := Finset.mem_biUnion.mp hv
  have hblock : G.subtwoExpand (G.subtwoFirstBlock cost) T ∈
      G.subtwoThreeStageBlocks cost := by
    simp only [subtwoThreeStageBlocks, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨T, hT, rfl⟩))
  exact hunused _ hblock hvT

theorem subtwoFinalBlock_zero_rank_vertices_unused
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (hzero : ∀ q ∈ S, G.subtwoFinalRank cost q = 0)
    (v : G.V)
    (hv : v ∈ G.subtwoExpand (G.subtwoFinalBlock cost) S) :
    (∀ B ∈ G.subtwoThreeStageBlocks cost, v ∉ B) ∧
      v ∈ G.subtwoOrdinaryAfterTriangles cost subtwoKappa ∧
      v ∉ G.subtwoActualMiddleVertices cost := by
  have hq : G.subtwoFinalBlock cost v ∈ S :=
    (G.mem_subtwoExpand (G.subtwoFinalBlock cost) S v).mp hv
  obtain ⟨w, hw, hunused⟩ := G.subtwoFinalRank_zero_classify
    cost hcost hpair hdegree (G.subtwoFinalBlock cost v) (hzero _ hq)
  have hvself : v ∈ (G.subtwoFinalBlock cost v).val :=
    G.subtwoSelectedLabel_mem_self (G.subtwoThreeStageBlocks cost) v
  rw [hw] at hvself
  have heq : v = w := by simpa using hvself
  subst w
  exact ⟨hunused,
    G.subtwo_unused_final_vertex_ordinary cost hcost hpair hdegree v hunused,
    G.subtwo_unused_final_vertex_not_middle cost v hunused⟩

theorem subtwoFinalQuotient_zero_rank_cost_eq
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (hzero : ∀ q ∈ S, G.subtwoFinalRank cost q = 0) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S =
        G.subtwoInternalCost cost
          (G.subtwoExpand (G.subtwoFinalBlock cost) S) := by
  have hsum : (∑ q ∈ S,
      G.subtwoInternalCost cost
        (G.subtwoFiber (G.subtwoFinalBlock cost) q)) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨v, hv, _⟩ := G.subtwoFinalRank_zero_classify
      cost hcost hpair hdegree q (hzero q hq)
    rw [G.subtwoFinalBlock_fiber cost hcost hpair hdegree, hv]
    exact G.subtwo_internal_singleton cost v
  have h := G.subtwo_contraction_internal_identity
    (G.subtwoFinalBlock cost) cost S
  rw [hsum, add_zero] at h
  exact h.symm

theorem subtwoFinalQuotient_zero_rank_triangle
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (htri : S.card = 3)
    (hrank : (∑ q ∈ S, G.subtwoFinalRank cost q) = 0) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S ≤ subtwoKappa := by
  classical
  have hzero : ∀ q ∈ S, G.subtwoFinalRank cost q = 0 := by
    intro q hq
    have hle := Finset.single_le_sum
      (fun r _ => Nat.zero_le (G.subtwoFinalRank cost r)) hq
    omega
  let U := G.subtwoExpand (G.subtwoFinalBlock cost) S
  have hUcard : U.card = 3 := by
    have hc := G.subtwo_expand_card_of_fiber_sizes
      (G.subtwoFinalBlock cost) S (G.subtwoFinalRank cost)
      (by intro q _; exact G.subtwoFinalBlock_fiber_card cost hcost hpair hdegree q)
    rw [htri, hrank] at hc
    exact hc
  have hUordinary : U ⊆
      G.subtwoOrdinaryAfterTriangles cost subtwoKappa := by
    intro v hv
    exact (G.subtwoFinalBlock_zero_rank_vertices_unused cost
      hcost hpair hdegree S hzero v hv).2.1
  have hcosteq := G.subtwoFinalQuotient_zero_rank_cost_eq
    cost hcost hpair hdegree S hzero
  rw [hcosteq]
  by_contra h
  have hdense : subtwoKappa < G.subtwoInternalCost cost U :=
    lt_of_not_ge h
  have hUselected : U ∈ G.subtwoDenseTriangles cost subtwoKappa :=
    (G.mem_subtwoDenseTriangles cost subtwoKappa U).mpr
      ⟨hUcard, hdense⟩
  have hpos : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hpos
  have hvTri : v ∈ G.subtwoTriangleVertices cost subtwoKappa :=
    Finset.mem_biUnion.mpr ⟨U, hUselected, hv⟩
  exact (Finset.mem_sdiff.mp (hUordinary hv)).2 hvTri

theorem subtwoFinalQuotient_zero_rank_five
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (hfive : S.card = 5)
    (hrank : (∑ q ∈ S, G.subtwoFinalRank cost q) = 0) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S ≤ 2 * subtwoKappa := by
  classical
  have hzero : ∀ q ∈ S, G.subtwoFinalRank cost q = 0 := by
    intro q hq
    have hle := Finset.single_le_sum
      (fun r _ => Nat.zero_le (G.subtwoFinalRank cost r)) hq
    omega
  let U := G.subtwoExpand (G.subtwoFinalBlock cost) S
  have hUcard : U.card = 5 := by
    have hc := G.subtwo_expand_card_of_fiber_sizes
      (G.subtwoFinalBlock cost) S (G.subtwoFinalRank cost)
      (by intro q _; exact G.subtwoFinalBlock_fiber_card cost hcost hpair hdegree q)
    rw [hfive, hrank] at hc
    exact hc
  have hUordinary : U ⊆
      G.subtwoOrdinaryAfterTriangles cost subtwoKappa := by
    intro v hv
    exact (G.subtwoFinalBlock_zero_rank_vertices_unused cost
      hcost hpair hdegree S hzero v hv).2.1
  have hUfree : Disjoint U (G.subtwoActualMiddleVertices cost) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvMiddle
    exact (G.subtwoFinalBlock_zero_rank_vertices_unused cost
      hcost hpair hdegree S hzero v hv).2.2 hvMiddle
  have hcosteq := G.subtwoFinalQuotient_zero_rank_cost_eq
    cost hcost hpair hdegree S hzero
  rw [hcosteq]
  by_contra h
  have hdense : 2 * subtwoKappa < G.subtwoInternalCost cost U :=
    lt_of_not_ge h
  have hUfive : U ∈ G.subtwoDenseOrdinaryFives cost subtwoKappa :=
    (G.mem_subtwoDenseOrdinaryFives cost subtwoKappa U).mpr
      ⟨hUcard, hUordinary, hdense⟩
  have hUselected : U ∈ G.subtwoThreeStageBlocks cost := by
    simp only [subtwoThreeStageBlocks, Finset.mem_union,
      subtwoFinalOrdinaryFives, Finset.mem_filter]
    exact Or.inr ⟨hUfive, hUfree⟩
  have hpos : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hpos
  exact (G.subtwoFinalBlock_zero_rank_vertices_unused cost
    hcost hpair hdegree S hzero v hv).1 U hUselected hv

/-- A final quotient triangle of rank one has the same vertices, ranks,
and crossing charge when viewed in the actual first quotient. -/
theorem subtwoFinalQuotient_degree_le
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM) :
    ∀ q : G.SubtwoFinalQuotient cost,
      (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoVertexCost
        (fun e => cost e.1) q ≤ subtwoM := by
  intro q
  rw [G.subtwo_quotient_vertex_cost,
    G.subtwoFinalBlock_fiber cost hcost hpair hdegree]
  have hdis := G.subtwoThreeStageBlocks_pairwise_disjoint cost
    hcost hpair hdegree
  rcases G.subtwoSelectedQuotient_classify _ hdis q with hsel | ⟨v, hv, _⟩
  · rcases G.subtwoThreeStageBlocks_density cost hcost hpair hdegree
      q.val hsel with ⟨hcard, hdense⟩ | ⟨hcard, hdense⟩
    · have hb := G.subtwo_triangle_boundary_lt cost q.val
        subtwoM subtwoKappa hcard
        (by intro v _; exact hdegree v) hdense
      have hc := subtwo_constant_inequalities.2.1
      linarith
    · have hb := G.subtwo_five_boundary_lt cost q.val
        subtwoM subtwoKappa hcard
        (by intro v _; exact hdegree v) hdense
      have hc : 5 * subtwoM - 4 * subtwoKappa < subtwoM := by
        unfold subtwoM subtwoKappa
        norm_num
      linarith
  · rw [hv, G.subtwo_boundary_singleton]
    exact hdegree v

/-- Every final quotient five-set containing a contracted block is
automatically below the five-set threshold. -/
theorem subtwoFinalQuotient_five_with_block
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (hfive : S.card = 5)
    (hblock : 1 ≤ ∑ q ∈ S, G.subtwoFinalRank cost q) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S < 2 * subtwoKappa := by
  apply G.subtwo_quotient_five_with_block
    (G.subtwoFinalBlock cost) cost S (G.subtwoFinalRank cost)
    subtwoM subtwoKappa hfive hblock hcost
  · intro v _
    exact hdegree v
  · intro q _
    exact G.subtwoFinalBlock_fiber_card cost hcost hpair hdegree q
  · intro q _
    exact G.subtwoFinalBlock_fiber_paid cost hcost hpair hdegree q
  · exact subtwo_constant_inequalities.2.1.le
  · exact subtwo_constant_inequalities.2.2.2

/-- A triangle containing at least two units of contracted rank also
falls below the triangle threshold by expansion and subtraction. -/
theorem subtwoFinalQuotient_triangle_high_rank
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (htri : S.card = 3)
    (hrank : 2 ≤ ∑ q ∈ S, G.subtwoFinalRank cost q) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S < subtwoKappa := by
  have h := G.subtwo_quotient_set_cost_bound
    (G.subtwoFinalBlock cost) cost S (G.subtwoFinalRank cost)
    subtwoM subtwoKappa hcost
    (by intro v _; exact hdegree v)
    (by intro q _; exact G.subtwoFinalBlock_fiber_card cost hcost hpair hdegree q)
    (by intro q _; exact G.subtwoFinalBlock_fiber_paid cost hcost hpair hdegree q)
  rw [htri] at h
  have hreal : (2 : ℝ) ≤
      (∑ q ∈ S, G.subtwoFinalRank cost q : ℕ) := by exact_mod_cast hrank
  have hMk := subtwo_constant_inequalities.2.1
  have hc : 3 * subtwoM / 2 + 2 * (subtwoM - subtwoKappa) <
      subtwoKappa := by
    unfold subtwoM subtwoKappa
    norm_num
  have hsum : (2 : ℝ) ≤
      ∑ q ∈ S, (G.subtwoFinalRank cost q : ℝ) := by
    simpa using hreal
  have hprod := mul_nonpos_of_nonpos_of_nonneg
    (show subtwoM - subtwoKappa ≤ 0 by linarith)
    (show (0 : ℝ) ≤
      (∑ q ∈ S, (G.subtwoFinalRank cost q : ℝ)) - 2 by linarith)
  norm_num at h
  nlinarith only [h, hc, hprod]

theorem subtwoFinalQuotient_rank_one_transport
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (htri : S.card = 3)
    (hrank : (∑ q ∈ S, G.subtwoFinalRank cost q) = 1) :
    let A := S.image (G.subtwoFirstOfFinal cost)
    A.card = 3 ∧
      (∑ p ∈ A, G.subtwoFirstRank cost p) = 1 ∧
      (G.subtwoQuotient (G.subtwoFirstBlock cost)).subtwoInternalCost
        (fun e => cost e.1) A =
      (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
        (fun e => cost e.1) S := by
  classical
  dsimp
  let f := G.subtwoFirstOfFinal cost
  have hbound : ∀ q ∈ S, G.subtwoFinalRank cost q ≤ 1 := by
    intro q hq
    have hle := Finset.single_le_sum
      (fun r _ => Nat.zero_le (G.subtwoFinalRank cost r)) hq
    omega
  have hcor : ∀ q ∈ S,
      G.subtwoFiber (G.subtwoFirstBlock cost) (f q) = q.val ∧
      G.subtwoFirstRank cost (f q) = G.subtwoFinalRank cost q := by
    intro q hq
    exact G.subtwoFirstOfFinal_corresponds cost hcost hpair hdegree
      q (hbound q hq)
  have hinj : ∀ q ∈ S, ∀ r ∈ S, f q = f r → q = r := by
    intro q hq r hr heq
    have hfq := (hcor q hq).1
    have hfr := (hcor r hr).1
    rw [heq] at hfq
    exact Subtype.ext (hfq.symm.trans hfr)
  have hAcard : (S.image f).card = 3 := by
    rw [Finset.card_image_iff.mpr hinj]
    exact htri
  have hArank : (∑ p ∈ S.image f, G.subtwoFirstRank cost p) = 1 := by
    rw [Finset.sum_image hinj]
    calc
      (∑ q ∈ S, G.subtwoFirstRank cost (f q)) =
          ∑ q ∈ S, G.subtwoFinalRank cost q := by
            apply Finset.sum_congr rfl
            intro q hq
            exact (hcor q hq).2
      _ = 1 := hrank
  have hExpand : G.subtwoExpand (G.subtwoFirstBlock cost) (S.image f) =
      G.subtwoExpand (G.subtwoFinalBlock cost) S := by
    ext v
    simp only [G.mem_subtwoExpand]
    constructor
    · intro hv
      obtain ⟨q, hq, hfq⟩ := Finset.mem_image.mp hv
      have hmem : v ∈ G.subtwoFiber (G.subtwoFirstBlock cost) (f q) :=
        (G.mem_subtwoFiber (G.subtwoFirstBlock cost) (f q) v).mpr hfq.symm
      rw [(hcor q hq).1] at hmem
      have hfinal : G.subtwoFinalBlock cost v = q :=
        (G.mem_subtwoFiber (G.subtwoFinalBlock cost) q v).mp
          (by rw [G.subtwoFinalBlock_fiber cost hcost hpair hdegree]; exact hmem)
      rw [hfinal]
      exact hq
    · intro hv
      let q := G.subtwoFinalBlock cost v
      have hmem : v ∈ G.subtwoFiber (G.subtwoFinalBlock cost) q := by
        exact (G.mem_subtwoFiber (G.subtwoFinalBlock cost) q v).mpr rfl
      rw [G.subtwoFinalBlock_fiber cost hcost hpair hdegree] at hmem
      have hfirst : G.subtwoFirstBlock cost v = f q :=
        (G.mem_subtwoFiber (G.subtwoFirstBlock cost) (f q) v).mp
          (by rw [(hcor q hv).1]; exact hmem)
      exact Finset.mem_image.mpr ⟨q, hv, hfirst.symm⟩
  have hsum :
      (∑ p ∈ S.image f,
        G.subtwoInternalCost cost
          (G.subtwoFiber (G.subtwoFirstBlock cost) p)) =
      ∑ q ∈ S,
        G.subtwoInternalCost cost
          (G.subtwoFiber (G.subtwoFinalBlock cost) q) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro q hq
    rw [(hcor q hq).1,
      G.subtwoFinalBlock_fiber cost hcost hpair hdegree]
  have hfirst := G.subtwo_contraction_internal_identity
    (G.subtwoFirstBlock cost) cost (S.image f)
  have hfinal := G.subtwo_contraction_internal_identity
    (G.subtwoFinalBlock cost) cost S
  rw [hExpand, hsum] at hfirst
  exact ⟨hAcard, hArank, by linarith only [hfirst, hfinal]⟩

theorem subtwoFinalQuotient_rank_one_triangle
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (htri : S.card = 3)
    (hrank : (∑ q ∈ S, G.subtwoFinalRank cost q) = 1) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S ≤ subtwoKappa := by
  classical
  let f := G.subtwoFirstOfFinal cost
  let A := S.image f
  obtain ⟨hAcard, hArank, hcosteq⟩ :=
    G.subtwoFinalQuotient_rank_one_transport cost hcost hpair
      hdegree S htri hrank
  by_contra h
  have hdense : subtwoKappa <
      (G.subtwoQuotient (G.subtwoFirstBlock cost)).subtwoInternalCost
        (fun e => cost e.1) A := by
    rw [hcosteq]
    exact lt_of_not_ge h
  have hA : A ∈ G.subtwoActualMiddleTriangles cost :=
    (G.mem_subtwoMiddleDenseTriangles
      (G.subtwoFirstBlock cost) (G.subtwoFirstRank cost) cost A).mpr
        ⟨hAcard, hArank, hdense⟩
  have hpos : 0 < ∑ q ∈ S, G.subtwoFinalRank cost q := by omega
  obtain ⟨q, hqS, hqPos⟩ := Finset.sum_pos_iff.mp hpos
  have hqLe := Finset.single_le_sum
    (fun r _ => Nat.zero_le (G.subtwoFinalRank cost r)) hqS
  have hqRank : G.subtwoFinalRank cost q = 1 := by omega
  have hremain := G.subtwoFinalRank_one_classify
    cost hcost hpair hdegree q hqRank
  have hfree := (Finset.mem_filter.mp hremain).2
  let v := Classical.choose q.property
  have hvq : v ∈ q.val := by
    have hvlabel : G.subtwoSelectedLabel
        (G.subtwoThreeStageBlocks cost) v = q.val :=
      Classical.choose_spec q.property
    rw [← hvlabel]
    exact G.subtwoSelectedLabel_mem_self
      (G.subtwoThreeStageBlocks cost) v
  have hvMiddle : v ∈ G.subtwoActualMiddleVertices cost := by
    apply Finset.mem_biUnion.mpr
    refine ⟨A, hA, ?_⟩
    apply (G.mem_subtwoExpand (G.subtwoFirstBlock cost) A v).mpr
    exact Finset.mem_image.mpr ⟨q, hqS, rfl⟩
  exact (Finset.disjoint_left.mp hfree) hvq hvMiddle

/-- Every triangle in the final, actually contracted quotient obeys the
fractional odd-set threshold. -/
theorem subtwoFinalQuotient_triangle_bound
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (htri : S.card = 3) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S ≤ subtwoKappa := by
  let r := ∑ q ∈ S, G.subtwoFinalRank cost q
  have hcases : r = 0 ∨ r = 1 ∨ 2 ≤ r := by omega
  rcases hcases with hzero | hone | hhigh
  · exact G.subtwoFinalQuotient_zero_rank_triangle cost
      hcost hpair hdegree S htri hzero
  · exact G.subtwoFinalQuotient_rank_one_triangle cost
      hcost hpair hdegree S htri hone
  · exact (G.subtwoFinalQuotient_triangle_high_rank cost
      hcost hpair hdegree S htri hhigh).le

theorem subtwoFinalQuotient_five_bound
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM)
    (S : Finset (G.SubtwoFinalQuotient cost))
    (hfive : S.card = 5) :
    (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
      (fun e => cost e.1) S ≤ 2 * subtwoKappa := by
  let r := ∑ q ∈ S, G.subtwoFinalRank cost q
  by_cases hzero : r = 0
  · exact G.subtwoFinalQuotient_zero_rank_five cost
      hcost hpair hdegree S hfive hzero
  · exact (G.subtwoFinalQuotient_five_with_block cost
      hcost hpair hdegree S hfive (by omega)).le

/-- The constructed final quotient obeys every odd-set inequality. -/
theorem subtwoFinalQuotient_all_odd_sets
    (cost : G.E → ℝ)
    (hcost : ∀ e, 0 ≤ cost e)
    (hpair : ∀ C : Finset G.V, C.card = 2 →
      G.subtwoInternalCost cost C ≤ 1)
    (hdegree : ∀ v, G.subtwoVertexCost cost v ≤ subtwoM) :
    ∀ S : Finset (G.SubtwoFinalQuotient cost),
      Odd S.card → 3 ≤ S.card →
        (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwoInternalCost
          (fun e => cost e.1) S ≤
            subtwoKappa * ((S.card : ℝ) - 1) / 2 := by
  apply (G.subtwoQuotient (G.subtwoFinalBlock cost)).subtwo_all_odd_sets_of_small_sets
    (fun e => cost e.1) subtwoM subtwoKappa
  · intro e
    exact hcost e.1
  · exact subtwo_constant_inequalities.1
  · exact G.subtwoFinalQuotient_degree_le cost hcost hpair hdegree
  · exact subtwo_constant_inequalities.2.2.1
  · intro S htri
    exact G.subtwoFinalQuotient_triangle_bound cost
      hcost hpair hdegree S htri
  · intro S hfive
    exact G.subtwoFinalQuotient_five_bound cost
      hcost hpair hdegree S hfive

end WeightedEdgeColoring.WeightedMultigraph
