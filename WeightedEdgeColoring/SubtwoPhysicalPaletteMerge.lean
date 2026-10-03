import WeightedEdgeColoring.SubtwoPhysicalPatternRestoration

/-!
# Restoring internal patterns in an existing boundary palette

At a given block and color, the boundary uses one original endpoint label.
An internal pattern reserved for that color avoids the label. Thus their
loads never add at one original vertex, and the same colors can be reused.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo
noncomputable section
universe u v

/-- Merge two physical partial colorings whose colors are separated at
all shared original vertices. -/
theorem feasibleOn_merge_of_vertex_color_separation
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {q : ℕ}
    (F R : Finset G.E) (hdisj : Disjoint F R)
    (base internal : G.E → Fin q)
    (hbase : G.IsFeasibleOn F base) (hinternal : G.IsFeasibleOn R internal)
    (hseparate : ∀ e ∈ F, ∀ f ∈ R, ∀ v,
      G.Inc v e → G.Inc v f → base e ≠ internal f) :
    G.IsFeasibleOn (F ∪ R) (fun e => if e ∈ F then base e else internal e) := by
  classical
  intro v c
  have hload :
      G.colorLoadOn (F ∪ R) (fun e => if e ∈ F then base e else internal e) v c =
        G.colorLoadOn F base v c + G.colorLoadOn R internal v c := by
    unfold WeightedEdgeColoring.WeightedMultigraph.colorLoadOn
    rw [Finset.sum_union hdisj]
    congr 1
    · apply Finset.sum_congr rfl
      intro e he
      simp [he]
    · apply Finset.sum_congr rfl
      intro e he
      have hn : e ∉ F := fun h => Finset.disjoint_left.mp hdisj h he
      simp [hn]
  rw [hload]
  by_cases hused : ∃ e ∈ F, G.Inc v e ∧ base e = c
  · obtain ⟨e, he, hev, hec⟩ := hused
    have hz : G.colorLoadOn R internal v c = 0 := by
      unfold WeightedEdgeColoring.WeightedMultigraph.colorLoadOn
      apply Finset.sum_eq_zero
      intro f hf
      by_cases hfv : G.Inc v f
      · have hne : internal f ≠ c := by
          intro hfc
          exact hseparate e he f hf v hev hfv (hec.trans hfc.symm)
        simp [hne]
      · simp [hfv]
    rw [hz, add_zero]
    exact hbase v c
  · have hz : G.colorLoadOn F base v c = 0 := by
      unfold WeightedEdgeColoring.WeightedMultigraph.colorLoadOn
      apply Finset.sum_eq_zero
      intro e he
      have hn : ¬ (G.Inc v e ∧ base e = c) := fun h => hused ⟨e, he, h⟩
      simp [hn]
    rw [hz, zero_add]
    exact hinternal v c

/-- The actual endpoint label on each boundary color is sufficient for
merging a filled internal pattern. The original boundary coloring stays
unchanged on every boundary edge. -/
theorem feasibleOn_restore_reserved_type_slots
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}}
    {I : Type v} [Fintype I] [DecidableEq I]
    {B : Type*} {q : ℕ}
    (F R : Finset G.E) (hdisj : Disjoint F R)
    (base internal : G.E → Fin q)
    (hbase : G.IsFeasibleOn F base) (hinternal : G.IsFeasibleOn R internal)
    (block : G.V → B) (boundaryLabel : B → Fin q → Option G.V)
    (hboundary : ∀ e ∈ F, ∀ v, G.Inc v e →
      boundaryLabel (block v) (base e) = some v)
    (typeOf : G.E → I) (typeInc : G.V → I → Prop)
    (hinc : ∀ e ∈ R, ∀ v, G.Inc v e → typeInc v (typeOf e))
    (slots : Fin q → I → ℕ)
    (hcount : ∀ c i,
      (R.filter fun e => typeOf e = i ∧ internal e = c).card ≤ slots c i)
    (havoid : ∀ v c i, typeInc v i →
      boundaryLabel (block v) c = some v → slots c i = 0) :
    G.IsFeasibleOn (F ∪ R) (fun e => if e ∈ F then base e else internal e) := by
  apply feasibleOn_merge_of_vertex_color_separation F R hdisj base internal
    hbase hinternal
  intro e he f hf v hev hfv hc
  have hp : 0 < slots (internal f) (typeOf f) :=
    positive_slot_of_colored R typeOf internal slots hcount hf
  have hz := havoid v (internal f) (typeOf f) (hinc f hf v hfv)
    (hc ▸ hboundary e he v hev)
  omega

/-- A bounded shortage of reserved type slots can be restored in the old
palette. The only omitted internal edges are the explicitly bounded
leftovers of each type. -/
theorem exists_reserved_physical_restoration
    {G : WeightedEdgeColoring.WeightedMultigraph.{u}}
    {I : Type v} [Fintype I] [DecidableEq I]
    {B : Type*} (q : ℕ) (hq : 0 < q)
    (F R : Finset G.E) (hdisj : Disjoint F R)
    (base : G.E → Fin q) (hbase : G.IsFeasibleOn F base)
    (block : G.V → B) (boundaryLabel : B → Fin q → Option G.V)
    (hboundary : ∀ e ∈ F, ∀ v, G.Inc v e →
      boundaryLabel (block v) (base e) = some v)
    (typeOf : G.E → I) (typeInc : G.V → I → Prop) [DecidableRel typeInc]
    (typeWeight : I → ℝ) (hweight0 : ∀ i, 0 ≤ typeWeight i)
    (hinc : ∀ e ∈ R, ∀ v, G.Inc v e → typeInc v (typeOf e))
    (hweight : ∀ e ∈ R, G.weight e ≤ typeWeight (typeOf e))
    (slots : Fin q → I → ℕ) (error : I → ℕ)
    (hslots : ∀ i,
      (R.filter fun e => typeOf e = i).card ≤ (∑ c, slots c i) + error i)
    (hcapacity : ∀ v c,
      (∑ i, if typeInc v i then (slots c i : ℝ) * typeWeight i else 0) ≤ 1)
    (havoid : ∀ v c i, typeInc v i →
      boundaryLabel (block v) c = some v → slots c i = 0) :
    ∃ P ⊆ R, ∃ color : G.E → Fin q,
      G.IsFeasibleOn (F ∪ P) color ∧
      (∀ e ∈ F, color e = base e) ∧
      (∀ i, ((R \ P).filter fun e => typeOf e = i).card ≤ error i) ∧
      ∀ v, (∑ e ∈ R \ P, if G.Inc v e then G.weight e else 0) ≤
        ∑ i, if typeInc v i then (error i : ℝ) * typeWeight i else 0 := by
  classical
  obtain ⟨P, hPR, internal, hfeasible, hcount, herror⟩ :=
    exists_partialColoring_of_type_slots R typeOf q hq typeInc typeWeight hweight0
      slots error hinc hweight hslots hcapacity
  have hFP : Disjoint F P := hdisj.mono_right hPR
  refine ⟨P, hPR, (fun e => if e ∈ F then base e else internal e), ?_,
    (fun e he => by simp [he]), herror, ?_⟩
  · exact feasibleOn_restore_reserved_type_slots F P hFP base internal hbase hfeasible
      block boundaryLabel hboundary typeOf typeInc (fun e he => hinc e (hPR he))
      slots hcount havoid
  · exact residualStarWeight_le_type_error R P typeOf typeInc typeWeight hweight0
      error hinc hweight herror

end
end WeightedEdgeColoring.Subtwo
