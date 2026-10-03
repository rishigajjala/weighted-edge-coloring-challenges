import WeightedEdgeColoring.SubtwoContraction

/-! A uniform six-symbol alphabet encodes every original endpoint inside a five-vertex block. -/

namespace WeightedEdgeColoring.WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [DecidableEq Q]

noncomputable section

def subtwoLocalSixLabel (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    (q : Q) (v : G.V) : Fin 6 :=
  if hv : v ∈ G.subtwoFiber block q then
    Fin.castLE
      (by rw [Fintype.card_coe]; exact (hfiber q).trans (by omega : 5 ≤ 6))
      ((Fintype.equivFin (G.subtwoFiber block q)).toFun ⟨v, hv⟩)
  else ⟨5, by omega⟩

theorem subtwoLocalSixLabel_injective_on_fiber
    (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    (q : Q) {v w : G.V}
    (hv : v ∈ G.subtwoFiber block q)
    (hw : w ∈ G.subtwoFiber block q)
    (hlabel : G.subtwoLocalSixLabel block hfiber q v =
      G.subtwoLocalSixLabel block hfiber q w) : v = w := by
  simp only [subtwoLocalSixLabel, dif_pos hv, dif_pos hw] at hlabel
  have hcode :
      (Fintype.equivFin (G.subtwoFiber block q)).toFun ⟨v, hv⟩ =
        (Fintype.equivFin (G.subtwoFiber block q)).toFun ⟨w, hw⟩ := by
    exact Fin.castLE_injective _ hlabel
  have hsub := (Fintype.equivFin (G.subtwoFiber block q)).injective hcode
  exact congrArg Subtype.val hsub

variable [Fintype Q]

def subtwoQuotientOriginalEndpoint (block : G.V → Q)
    (q : Q) (e : (G.subtwoQuotient block).StarEdge q) : G.V :=
  if block (G.fst e.1.1) = q then G.fst e.1.1 else G.snd e.1.1

theorem subtwoQuotientOriginalEndpoint_mem_fiber (block : G.V → Q)
    (q : Q) (e : (G.subtwoQuotient block).StarEdge q) :
    G.subtwoQuotientOriginalEndpoint block q e ∈ G.subtwoFiber block q := by
  have hinc : block (G.fst e.1.1) = q ∨ block (G.snd e.1.1) = q := e.2
  unfold subtwoQuotientOriginalEndpoint
  split_ifs with hf
  · exact (G.mem_subtwoFiber block q _).mpr hf
  · exact (G.mem_subtwoFiber block q _).mpr (hinc.resolve_left hf)

def subtwoQuotientEdgeLabel (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    (q : Q) (e : (G.subtwoQuotient block).StarEdge q) : Fin 6 :=
  G.subtwoLocalSixLabel block hfiber q
    (G.subtwoQuotientOriginalEndpoint block q e)

theorem subtwoQuotientEdgeLabel_eq_iff_endpoint_eq (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    (q : Q) (e f : (G.subtwoQuotient block).StarEdge q) :
    G.subtwoQuotientEdgeLabel block hfiber q e =
      G.subtwoQuotientEdgeLabel block hfiber q f ↔
    G.subtwoQuotientOriginalEndpoint block q e =
      G.subtwoQuotientOriginalEndpoint block q f := by
  constructor
  · intro h
    exact G.subtwoLocalSixLabel_injective_on_fiber block hfiber q
      (G.subtwoQuotientOriginalEndpoint_mem_fiber block q e)
      (G.subtwoQuotientOriginalEndpoint_mem_fiber block q f) h
  · intro h
    simp [subtwoQuotientEdgeLabel, h]

end

end WeightedEdgeColoring.WeightedMultigraph
