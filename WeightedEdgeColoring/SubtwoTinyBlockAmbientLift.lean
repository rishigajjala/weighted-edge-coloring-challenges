import WeightedEdgeColoring.SubtwoUniformTinyBlockRestoration
import WeightedEdgeColoring.SubtwoVertexEmbeddingColorLifting

/-! Lift a retained induced-block partial coloring to the ambient mixed
object graph, preserving the actual ambient endpoint labels. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
noncomputable section
universe u
variable {G : WeightedEdgeColoring.WeightedMultigraph.{u}} {tau : ℝ}
  (P : G.GeneralTinyThresholdPacketization tau)

theorem exists_ambient_lift_of_retainedBlock_color
    (T : Finset G.V)
    (R : Finset (P.mixedObjectGraph.vertexRestriction T).E)
    (A : Finset ((P.mixedObjectGraph.vertexRestriction T).edgeRestriction R).E)
    (K : ℕ) (hK : 0 < K)
    (color : ((P.mixedObjectGraph.vertexRestriction T).edgeRestriction R).E → Fin K)
    (hfeasible : ((P.mixedObjectGraph.vertexRestriction T).edgeRestriction R).IsFeasibleOn
      A color)
    (boundaryLabel : Fin K → Option (P.mixedObjectGraph.vertexRestriction T).V)
    (havoid : ∀ e ∈ A, ∀ v,
      ((P.mixedObjectGraph.vertexRestriction T).edgeRestriction R).Inc v e →
        boundaryLabel (color e) ≠ some v) :
    let H := P.mixedObjectGraph
    let J := (H.vertexRestriction T).edgeRestriction R
    let edge : J.E → H.E := fun e => e.val.val
    ∃ ambient : H.E → Fin K,
      H.IsFeasibleOn (A.image edge) ambient ∧
      (∀ e ∈ A, ambient (edge e) = color e) ∧
      (∀ e ∈ A.image edge, ∀ v, H.Inc v e →
        (boundaryLabel (ambient e)).map Subtype.val ≠ some v) ∧
      ∀ v : J.V,
        (∑ e ∈ (Finset.univ.image edge) \ (A.image edge),
          if H.Inc v.val e then H.weight e else 0) =
        ∑ e ∈ Finset.univ \ A, if J.Inc v e then J.weight e else 0 := by
  dsimp only
  let H := P.mixedObjectGraph
  let J := (H.vertexRestriction T).edgeRestriction R
  let vertex : J.V ↪ H.V := ⟨Subtype.val, Subtype.val_injective⟩
  let edge : J.E → H.E := fun e => e.val.val
  have hinj : Function.Injective edge := by
    intro e f h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hfst : ∀ e, H.fst (edge e) = vertex (J.fst e) := by intro e; rfl
  have hsnd : ∀ e, H.snd (edge e) = vertex (J.snd e) := by intro e; rfl
  have hweight : ∀ e, J.weight e = H.weight (edge e) := by intro e; rfl
  obtain ⟨ambient,hfeas,hsame,hleft⟩ :=
    H.exists_lift_vertexEmbedded_partialColor J vertex edge
      hinj hfst hsnd hweight A K hK color hfeasible
  refine ⟨ambient,hfeas,hsame,?_,hleft⟩
  intro f hf v hv
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf
  have hvlocal : v = vertex (J.fst e) ∨ v = vertex (J.snd e) := by
    rcases hv with h | h
    · exact Or.inl (hfst e |>.symm.trans h).symm
    · exact Or.inr (hsnd e |>.symm.trans h).symm
  rcases hvlocal with hvlocal | hvlocal
  · subst v
    have hi : J.Inc (J.fst e) e := Or.inl rfl
    have ha := havoid e he (J.fst e) hi
    rw [hsame e he]
    intro hbad
    cases hlabel : boundaryLabel (color e) with
    | none => simp [hlabel] at hbad
    | some w =>
      have heq : w = J.fst e :=
        Subtype.val_injective (by simpa [hlabel, vertex] using hbad)
      exact ha (by simp [hlabel, heq])
  · subst v
    have hi : J.Inc (J.snd e) e := Or.inr rfl
    have ha := havoid e he (J.snd e) hi
    rw [hsame e he]
    intro hbad
    cases hlabel : boundaryLabel (color e) with
    | none => simp [hlabel] at hbad
    | some w =>
      have heq : w = J.snd e :=
        Subtype.val_injective (by simpa [hlabel, vertex] using hbad)
      exact ha (by simp [hlabel, heq])

end
end WeightedEdgeColoring.WeightedMultigraph.GeneralTinyThresholdPacketization
