import WeightedEdgeColoring.RankThreeResidualNibble
import WeightedEdgeColoring.RankThreeExchange

/-!
# Lifting a matching from a residual option system

This is the type-changing bridge needed to iterate nibble rounds.  A matching
chosen in the subtype of options compatible with an existing matching lifts
to original options, and its union with the existing matching is again a
partial matching.
-/

namespace WeightedEdgeColoring.RankThreeOptionSystem

universe u v w

variable {Job : Type u} {Slot : Type v} {Option : Type w}
  [Fintype Job] [Fintype Slot] [Fintype Option]
  [DecidableEq Job] [DecidableEq Slot] [DecidableEq Option]
  (H : RankThreeOptionSystem Job Slot Option)

/-- Forget the residual-membership proof on a finite set of residual options. -/
def liftResidualSet (M : Finset Option)
    (A : Finset (H.ResidualOption M)) : Finset Option :=
  A.map ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_liftResidualSet {M : Finset Option}
    {A : Finset (H.ResidualOption M)} {o : Option} :
    o ∈ H.liftResidualSet M A ↔ ∃ q ∈ A, q.1 = o := by
  simp [liftResidualSet]

/-- A residual partial matching remains a partial matching after forgetting
the subtype proofs. -/
theorem liftResidualSet_isPartialMatching
    {M : Finset Option} {A : Finset (H.ResidualOption M)}
    (hA : (H.residualSystem M).IsPartialMatching A) :
    H.IsPartialMatching (H.liftResidualSet M A) := by
  constructor
  · intro o ho p hp hop
    rcases H.mem_liftResidualSet.mp ho with ⟨qo, hqo, rfl⟩
    rcases H.mem_liftResidualSet.mp hp with ⟨qp, hqp, rfl⟩
    have hne : qo ≠ qp := by
      intro h
      exact hop (congrArg Subtype.val h)
    exact hA.1 hqo hqp hne
  · intro o ho p hp heq
    rcases H.mem_liftResidualSet.mp ho with ⟨qo, hqo, rfl⟩
    rcases H.mem_liftResidualSet.mp hp with ⟨qp, hqp, rfl⟩
    have hsubeq : qo = qp := hA.2 hqo hqp heq
    exact congrArg Subtype.val hsubeq

/-- Every lifted residual option is compatible with, and has a different
owner from, every option in the old matching. -/
theorem liftResidualSet_cross
    {M : Finset Option} {A : Finset (H.ResidualOption M)}
    {p q : Option} (hp : p ∈ M) (hq : q ∈ H.liftResidualSet M A) :
    H.owner p ≠ H.owner q ∧ H.Compatible p q := by
  rcases H.mem_liftResidualSet.mp hq with ⟨rq, _hrqA, rfl⟩
  have hres := H.mem_residualOptions.mp rq.2 p hp
  exact ⟨Ne.symm hres.1, H.compatible_symm.mpr hres.2⟩

/-- A residual matching can be added to the old matching in the original
option system. -/
theorem IsPartialMatching.union_liftResidualSet
    {M : Finset Option} (hM : H.IsPartialMatching M)
    {A : Finset (H.ResidualOption M)}
    (hA : (H.residualSystem M).IsPartialMatching A) :
    H.IsPartialMatching (M ∪ H.liftResidualSet M A) := by
  have hlift := H.liftResidualSet_isPartialMatching hA
  apply hM.union_of_cross H hlift
  · intro p hp q hq
    exact (H.liftResidualSet_cross hp hq).2
  · intro p hp q hq
    exact (H.liftResidualSet_cross hp hq).1

end WeightedEdgeColoring.RankThreeOptionSystem
