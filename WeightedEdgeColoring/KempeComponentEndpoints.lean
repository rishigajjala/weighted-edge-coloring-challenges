import WeightedEdgeColoring.KempeComponentSwitch
import WeightedEdgeColoring.SimpleGraphDegreeTwoEndpoints

/-!
# The two active ends of a Kempe component

For two colors in a proper edge coloring, every connected component has at
most two vertices at which exactly one of the colors is missing.  These are
the only vertices whose missing-color indicators can change when the
component is switched.

The proof deliberately avoids classifying components as paths or cycles.
Properness injects the neighbors of any vertex into two labels, so the
two-color graph has maximum degree two.  An active vertex has degree one.
The endpoint count then follows from the elementary handshaking lemma in
`SimpleGraphDegreeTwoEndpoints`.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})

/- The file states degree bounds directly, so adjacency and component
membership must be decidable while theorem statements are elaborated (a
`classical` inside the proof would be too late).  The ordinary subtype
`Fintype` instances then give a coherent finite structure throughout. -/
noncomputable local instance decidableSimpleGraphAdj (H : SimpleGraph G.V) :
    DecidableRel H.Adj :=
  Classical.decRel _

noncomputable local instance decidableSetMembership (s : Set G.V) :
    DecidablePred (fun v : G.V ↦ v ∈ s) :=
  Classical.decPred _

noncomputable local instance finiteSetSubtype (s : Set G.V) : Fintype s :=
  @Subtype.fintype G.V (fun v ↦ v ∈ s) (decidableSetMembership G s)
    G.instFintypeV

noncomputable local instance finiteConnectedComponentSupport
    (H : SimpleGraph G.V) (C : H.ConnectedComponent) : Fintype C :=
  @Subtype.fintype G.V (fun v ↦ v ∈ C.supp)
    (decidableSetMembership G C.supp) G.instFintypeV

/-- The endpoint of an indexed edge opposite `v`, when the edge is incident
with `v`. -/
def kempeOtherEndpoint (v : G.V) (e : G.E) : G.V :=
  if G.fst e = v then G.snd e else G.fst e

theorem kempeOtherEndpoint_eq_of_incident {v w : G.V} {e : G.E}
    (hv : G.Inc v e) (hw : G.Inc w e) (hvw : v ≠ w) :
    G.kempeOtherEndpoint v e = w := by
  rcases hv with hfv | hsv
  · rcases hw with hfw | hsw
    · exact False.elim (hvw (hfv.symm.trans hfw))
    · simpa [kempeOtherEndpoint, hfv] using hsw
  · have hnotfst : G.fst e ≠ v := by
      intro hfv
      exact G.noLoop e (hfv.trans hsv.symm)
    rcases hw with hfw | hsw
    · simpa [kempeOtherEndpoint, hnotfst] using hfw
    · exact False.elim (hvw (hsv.symm.trans hsw))

/-- Adjacency in the simple two-color graph is witnessed by an original
selected edge carrying one of the two colors. -/
theorem exists_twoColorWitnessEdge {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    {v w : G.V} (hvw : (G.twoColorGraph F color a b).Adj v w) :
    ∃ e, e ∈ F ∧ G.Inc v e ∧ G.Inc w e ∧
      (color e = a ∨ color e = b) := by
  rcases hvw with ⟨hne, hrel | hrel⟩
  · rcases hrel with ⟨e, heF, hfst, hsnd, hcolor⟩
    exact ⟨e, heF, Or.inl hfst, Or.inr hsnd, hcolor⟩
  · rcases hrel with ⟨e, heF, hfst, hsnd, hcolor⟩
    exact ⟨e, heF, Or.inr hsnd, Or.inl hfst, hcolor⟩

/-- A fixed original edge witnessing one neighbor in the two-color graph. -/
noncomputable def twoColorNeighborEdge {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (v : G.V)
    (w : (G.twoColorGraph F color a b).neighborSet v) : G.E :=
  Classical.choose
    (G.exists_twoColorWitnessEdge F color a b w.property)

theorem twoColorNeighborEdge_spec {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (v : G.V)
    (w : (G.twoColorGraph F color a b).neighborSet v) :
    G.twoColorNeighborEdge F color a b v w ∈ F ∧
      G.Inc v (G.twoColorNeighborEdge F color a b v w) ∧
      G.Inc w.1 (G.twoColorNeighborEdge F color a b v w) ∧
      (color (G.twoColorNeighborEdge F color a b v w) = a ∨
        color (G.twoColorNeighborEdge F color a b v w) = b) := by
  exact Classical.choose_spec
    (G.exists_twoColorWitnessEdge F color a b w.property)

/-- Encode a neighbor by the color of its fixed witness edge.  The two
possible colors are represented by the two Boolean values. -/
noncomputable def twoColorNeighborBit {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q) (v : G.V)
    (w : (G.twoColorGraph F color a b).neighborSet v) : Bool :=
  if color (G.twoColorNeighborEdge F color a b v w) = a then false else true

theorem twoColorNeighborBit_injective_of_isProperOn {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q) (v : G.V) :
    Function.Injective (G.twoColorNeighborBit F color a b v) := by
  classical
  intro x y hbit
  let ex := G.twoColorNeighborEdge F color a b v x
  let ey := G.twoColorNeighborEdge F color a b v y
  have hx := G.twoColorNeighborEdge_spec F color a b v x
  have hy := G.twoColorNeighborEdge_spec F color a b v y
  have hcolor : color ex = color ey := by
    by_cases hxa : color ex = a
    · by_cases hya : color ey = a
      · exact hxa.trans hya.symm
      · simp [twoColorNeighborBit, ex, ey, hxa, hya] at hbit
    · by_cases hya : color ey = a
      · simp [twoColorNeighborBit, ex, ey, hxa, hya] at hbit
      · exact (hx.2.2.2.resolve_left hxa).trans
          (hy.2.2.2.resolve_left hya).symm
  have hex : ex ∈ (F.filter (G.Inc v) : Set G.E) := by
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hx.1, hx.2.1⟩)
  have hey : ey ∈ (F.filter (G.Inc v) : Set G.E) := by
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hy.1, hy.2.1⟩)
  have hedge : ex = ey := hproper v hex hey hcolor
  apply Subtype.ext
  have hxadj : (G.twoColorGraph F color a b).Adj v x.1 := by
    exact ((G.twoColorGraph F color a b).mem_neighborSet v x.1).mp x.property
  have hyadj : (G.twoColorGraph F color a b).Adj v y.1 := by
    exact ((G.twoColorGraph F color a b).mem_neighborSet v y.1).mp y.property
  have hxother : G.kempeOtherEndpoint v ex = x.1 :=
    G.kempeOtherEndpoint_eq_of_incident hx.2.1 hx.2.2.1 hxadj.ne
  have hyother : G.kempeOtherEndpoint v ey = y.1 :=
    G.kempeOtherEndpoint_eq_of_incident hy.2.1 hy.2.2.1 hyadj.ne
  calc
    x.1 = G.kempeOtherEndpoint v ex := hxother.symm
    _ = G.kempeOtherEndpoint v ey := by rw [hedge]
    _ = y.1 := hyother

/-- Properness forces maximum degree two in the simple two-color graph. -/
theorem twoColorGraph_degree_le_two_of_isProperOn {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q) (v : G.V) :
    (G.twoColorGraph F color a b).degree v ≤ 2 := by
  classical
  rw [← (G.twoColorGraph F color a b).card_neighborSet_eq_degree]
  simpa using Fintype.card_le_of_injective
    (G.twoColorNeighborBit F color a b v)
    (G.twoColorNeighborBit_injective_of_isProperOn F color hproper a b v)

/-- A color is used at `v` precisely when it is not in the missing-color
set.  This direction extracts a concrete selected edge. -/
theorem exists_usedEdge_of_not_mem_missingColorsAt {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) (c : Fin q)
    (hc : c ∉ G.missingColorsAt F color v) :
    ∃ e, e ∈ F ∧ G.Inc v e ∧ color e = c := by
  classical
  have himage : c ∈ (F.filter (G.Inc v)).image color := by
    simpa only [missingColorsAt, Finset.mem_sdiff, Finset.mem_univ,
      true_and, not_not] using hc
  rcases Finset.mem_image.mp himage with ⟨e, he, hecolor⟩
  have heData := Finset.mem_filter.mp he
  exact ⟨e, heData.1, heData.2, hecolor⟩

/-- A color declared missing cannot occur on a selected incident edge. -/
theorem color_ne_of_mem_missingColorsAt {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (v : G.V) (c : Fin q)
    (hc : c ∈ G.missingColorsAt F color v)
    {e : G.E} (heF : e ∈ F) (heInc : G.Inc v e) :
    color e ≠ c := by
  intro heq
  have hnot := G.not_mem_missingColorsAt_of_used
    (base := color) heF heInc
  exact hnot (by simpa [heq] using hc)

/-- If one of the two colors is used at `v`, then `v` has a neighbor in the
two-color graph. -/
theorem twoColorGraph_degree_pos_of_not_mem_missingColorsAt {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b c : Fin q)
    (hcPair : c = a ∨ c = b) (v : G.V)
    (hc : c ∉ G.missingColorsAt F color v) :
    0 < (G.twoColorGraph F color a b).degree v := by
  classical
  rcases G.exists_usedEdge_of_not_mem_missingColorsAt F color v c hc with
    ⟨e, heF, heInc, heColor⟩
  have hePair : color e = a ∨ color e = b := by
    rcases hcPair with rfl | rfl
    · exact Or.inl heColor
    · exact Or.inr heColor
  rw [(G.twoColorGraph F color a b).degree_pos_iff_exists_adj]
  rcases heInc with hfst | hsnd
  · exact ⟨G.snd e,
      by simpa [hfst] using
        G.twoColorGraph_adj_fst_snd F color a b heF hePair⟩
  · exact ⟨G.fst e,
      by simpa [hsnd] using
        (G.twoColorGraph_adj_fst_snd F color a b heF hePair).symm⟩

/-- Exactly one of the paired colors is missing at `v`. -/
def IsTwoColorActive {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (a b : Fin q) (v : G.V) : Prop :=
  (a ∈ G.missingColorsAt F color v ∧
      b ∉ G.missingColorsAt F color v) ∨
    (b ∈ G.missingColorsAt F color v ∧
      a ∉ G.missingColorsAt F color v)

noncomputable local instance decidableTwoColorActive {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (C : G.TwoColorComponent F color a b) :
    DecidablePred (fun v : C ↦ G.IsTwoColorActive F color a b v.1) :=
  Classical.decPred _

/-- At an active vertex, all two-color neighbor witnesses carry the same
one of `a,b`. -/
theorem twoColorNeighborEdge_color_eq_of_active {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (a b : Fin q) (v : G.V) (hactive : G.IsTwoColorActive F color a b v)
    (x y : (G.twoColorGraph F color a b).neighborSet v) :
    color (G.twoColorNeighborEdge F color a b v x) =
      color (G.twoColorNeighborEdge F color a b v y) := by
  classical
  have hx := G.twoColorNeighborEdge_spec F color a b v x
  have hy := G.twoColorNeighborEdge_spec F color a b v y
  rcases hactive with ⟨ha, _hb⟩ | ⟨hb, _ha⟩
  · have hxne :
        color (G.twoColorNeighborEdge F color a b v x) ≠ a :=
      G.color_ne_of_mem_missingColorsAt F color v a ha hx.1 hx.2.1
    have hyne :
        color (G.twoColorNeighborEdge F color a b v y) ≠ a :=
      G.color_ne_of_mem_missingColorsAt F color v a ha hy.1 hy.2.1
    exact (hx.2.2.2.resolve_left hxne).trans
      (hy.2.2.2.resolve_left hyne).symm
  · have hxne :
        color (G.twoColorNeighborEdge F color a b v x) ≠ b :=
      G.color_ne_of_mem_missingColorsAt F color v b hb hx.1 hx.2.1
    have hyne :
        color (G.twoColorNeighborEdge F color a b v y) ≠ b :=
      G.color_ne_of_mem_missingColorsAt F color v b hb hy.1 hy.2.1
    exact (hx.2.2.2.resolve_right hxne).trans
      (hy.2.2.2.resolve_right hyne).symm

/-- An active vertex has at most one neighbor in the two-color graph. -/
theorem twoColorGraph_degree_le_one_of_active {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q) (v : G.V)
    (hactive : G.IsTwoColorActive F color a b v) :
    (G.twoColorGraph F color a b).degree v ≤ 1 := by
  classical
  rw [← (G.twoColorGraph F color a b).card_neighborSet_eq_degree,
    Fintype.card_le_one_iff]
  intro x y
  have hx := G.twoColorNeighborEdge_spec F color a b v x
  have hy := G.twoColorNeighborEdge_spec F color a b v y
  have hcolor := G.twoColorNeighborEdge_color_eq_of_active
    F color a b v hactive x y
  have hex : G.twoColorNeighborEdge F color a b v x ∈
      (F.filter (G.Inc v) : Set G.E) := by
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hx.1, hx.2.1⟩)
  have hey : G.twoColorNeighborEdge F color a b v y ∈
      (F.filter (G.Inc v) : Set G.E) := by
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hy.1, hy.2.1⟩)
  have hedge := hproper v hex hey hcolor
  apply Subtype.ext
  have hxadj : (G.twoColorGraph F color a b).Adj v x.1 := by
    exact ((G.twoColorGraph F color a b).mem_neighborSet v x.1).mp x.property
  have hyadj : (G.twoColorGraph F color a b).Adj v y.1 := by
    exact ((G.twoColorGraph F color a b).mem_neighborSet v y.1).mp y.property
  have hxother :
      G.kempeOtherEndpoint v
          (G.twoColorNeighborEdge F color a b v x) = x.1 :=
    G.kempeOtherEndpoint_eq_of_incident hx.2.1 hx.2.2.1 hxadj.ne
  have hyother :
      G.kempeOtherEndpoint v
          (G.twoColorNeighborEdge F color a b v y) = y.1 :=
    G.kempeOtherEndpoint_eq_of_incident hy.2.1 hy.2.2.1 hyadj.ne
  calc
    x.1 = G.kempeOtherEndpoint v
        (G.twoColorNeighborEdge F color a b v x) := hxother.symm
    _ = G.kempeOtherEndpoint v
        (G.twoColorNeighborEdge F color a b v y) := by rw [hedge]
    _ = y.1 := hyother

/-- In fact an active vertex has degree exactly one. -/
theorem twoColorGraph_degree_eq_one_of_active {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q) (v : G.V)
    (hactive : G.IsTwoColorActive F color a b v) :
    (G.twoColorGraph F color a b).degree v = 1 := by
  classical
  have hpos : 0 < (G.twoColorGraph F color a b).degree v := by
    rcases hactive with ⟨_ha, hb⟩ | ⟨_hb, ha⟩
    · exact G.twoColorGraph_degree_pos_of_not_mem_missingColorsAt
        F color a b b (Or.inr rfl) v hb
    · exact G.twoColorGraph_degree_pos_of_not_mem_missingColorsAt
        F color a b a (Or.inl rfl) v ha
  have hle := G.twoColorGraph_degree_le_one_of_active
    F color hproper a b v hactive
  omega

set_option maxHeartbeats 800000 in
/-- Every component has at most two active vertices.  This is the exact
bounded-influence fact needed for a component coin. -/
theorem card_activeVertices_twoColorComponent_le_two {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (C : G.TwoColorComponent F color a b) :
    ((Finset.univ : Finset C).filter fun (v : C) ↦
      G.IsTwoColorActive F color a b v.1).card ≤ 2 := by
  classical
  let H := G.twoColorGraph F color a b
  have hcomponentNeighborSubset (v : C) : H.neighborSet v.1 ⊆ C.supp := by
    intro w hw
    exact (C.mem_supp_congr_adj hw).mp v.2
  have hcomponentDegree (v : C) :
      C.toSimpleGraph.degree v = H.degree v.1 := by
    change (H.induce C.supp).degree v = H.degree v.1
    exact H.degree_induce_of_neighborSet_subset (hcomponentNeighborSubset v)
  have hcomponentMax (v : C) : C.toSimpleGraph.degree v ≤ 2 := by
    rw [hcomponentDegree v]
    exact G.twoColorGraph_degree_le_two_of_isProperOn
      F color hproper a b v.1
  have hends :
      ((Finset.univ : Finset C).filter fun v ↦
        C.toSimpleGraph.degree v = 1).card ≤ 2 :=
    WeightedEdgeColoring.SimpleGraph.card_degreeOne_le_two_of_connected_of_degree_le_two
      C.toSimpleGraph C.connected_toSimpleGraph hcomponentMax
  apply le_trans (Finset.card_le_card ?_) hends
  intro v hv
  have hvActive : G.IsTwoColorActive F color a b v.1 := by
    simpa using (Finset.mem_filter.mp hv).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hcomponentDegree v]
  exact G.twoColorGraph_degree_eq_one_of_active
    F color hproper a b v.1 hvActive

end WeightedMultigraph
end WeightedEdgeColoring
