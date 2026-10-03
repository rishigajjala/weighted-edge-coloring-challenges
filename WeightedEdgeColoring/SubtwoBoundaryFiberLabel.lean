import WeightedEdgeColoring.SubtwoOriginalEndpointLabelCharge
import WeightedEdgeColoring.SubtwoVertexRestriction

/-! Decode the six-symbol boundary labels into actual vertices of each block. -/

namespace WeightedEdgeColoring
noncomputable section

def inverseOptionLabel {A L : Type*} (encode : A → L) (label : Option L) : Option A := by
  classical
  exact if h : ∃ a, label = some (encode a) then some (Classical.choose h) else none

theorem inverseOptionLabel_eq_some_iff {A L : Type*}
    (encode : A → L) (hinj : Function.Injective encode) (label : Option L) (a : A) :
    inverseOptionLabel encode label = some a ↔ label = some (encode a) := by
  classical
  unfold inverseOptionLabel
  by_cases h : ∃ a, label = some (encode a)
  · simp only [dif_pos h, Option.some.injEq]
    constructor
    · intro ha
      simpa [ha] using Classical.choose_spec h
    · intro ha
      apply hinj
      exact Option.some.inj ((Classical.choose_spec h).symm.trans ha)
  · simp only [dif_neg h]
    constructor
    · intro ha
      cases ha
    · intro ha
      exact (h ⟨a,ha⟩).elim

theorem inverseOptionLabel_class_card {A L Color : Type*} [Fintype Color]
    [DecidableEq A] [DecidableEq L]
    (encode : A → L) (hinj : Function.Injective encode)
    (label : Color → Option L) (a : A) :
    Fintype.card {c : Color // inverseOptionLabel encode (label c) = some a} =
      Fintype.card {c : Color // label c = some (encode a)} := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun c => ⟨c.1,(inverseOptionLabel_eq_some_iff encode hinj (label c.1) a).1 c.2⟩
    invFun := fun c => ⟨c.1,(inverseOptionLabel_eq_some_iff encode hinj (label c.1) a).2 c.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

namespace WeightedMultigraph
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

def subtwoFiberVertexLabel (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5) (q : Q)
    (v : (G.vertexRestriction (G.subtwoFiber block q)).V) : Fin 6 :=
  G.subtwoLocalSixLabel block hfiber q v.1

theorem subtwoFiberVertexLabel_injective (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5) (q : Q) :
    Function.Injective (G.subtwoFiberVertexLabel block hfiber q) := by
  intro v w h
  exact Subtype.ext (G.subtwoLocalSixLabel_injective_on_fiber
    block hfiber q v.2 w.2 h)

def subtwoBoundaryFiberLabel (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (selectedLabel : Q → Fin K → Option (Fin 6))
    (q : Q) (c : Fin K) : Option (G.vertexRestriction (G.subtwoFiber block q)).V :=
  inverseOptionLabel (G.subtwoFiberVertexLabel block hfiber q) (selectedLabel q c)

theorem subtwoBoundaryFiberLabel_eq_some_iff (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (selectedLabel : Q → Fin K → Option (Fin 6))
    (q : Q) (c : Fin K) (v : (G.vertexRestriction (G.subtwoFiber block q)).V) :
    G.subtwoBoundaryFiberLabel block hfiber selectedLabel q c = some v ↔
      selectedLabel q c = some (G.subtwoLocalSixLabel block hfiber q v.1) :=
  inverseOptionLabel_eq_some_iff _
    (G.subtwoFiberVertexLabel_injective block hfiber q) _ _

theorem subtwoBoundaryFiberLabel_support (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (selectedLabel : Q → Fin K → Option (Fin 6))
    (v : G.V) (c : Fin K)
    (hlabel : selectedLabel (block v) c =
      some (G.subtwoLocalSixLabel block hfiber (block v) v)) :
    (G.subtwoBoundaryFiberLabel block hfiber selectedLabel (block v) c).map
      Subtype.val = some v := by
  let v' : (G.vertexRestriction (G.subtwoFiber block (block v))).V :=
    ⟨v, (G.mem_subtwoFiber block (block v) v).2 rfl⟩
  have h := (G.subtwoBoundaryFiberLabel_eq_some_iff
    block hfiber selectedLabel (block v) c v').2 hlabel
  rw [h]
  rfl

theorem subtwoBoundaryFiberLabel_class_card (block : G.V → Q)
    (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K : ℕ} (selectedLabel : Q → Fin K → Option (Fin 6))
    (q : Q) (v : (G.vertexRestriction (G.subtwoFiber block q)).V) :
    Fintype.card {c : Fin K //
      G.subtwoBoundaryFiberLabel block hfiber selectedLabel q c = some v} =
    Fintype.card {c : Fin K //
      selectedLabel q c = some (G.subtwoLocalSixLabel block hfiber q v.1)} :=
  inverseOptionLabel_class_card _
    (G.subtwoFiberVertexLabel_injective block hfiber q) _ v

end WeightedMultigraph
end
end WeightedEdgeColoring
