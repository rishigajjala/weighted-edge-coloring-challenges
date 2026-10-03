import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.BigOperators

/-!
# Reindexing a finite vertex sum by connected components

The supports of the connected components of a finite simple graph partition
its vertex set.  The equivalence and sum identity below expose that elementary
fact in the form used by the Kempe-component moment calculation.
-/

namespace WeightedEdgeColoring.SimpleGraph

open scoped BigOperators

noncomputable section

universe u w

variable {V : Type u} [Fintype V]

/-- Canonical finite enumeration of the connected components of a finite
graph.  This uses the quotient's `Finite` instance and does not require a
decidable adjacency relation. -/
noncomputable instance instFintypeConnectedComponent (H : SimpleGraph V) :
    Fintype H.ConnectedComponent :=
  Fintype.ofFinite _

noncomputable instance instFintypeConnectedComponentSupport
    (H : SimpleGraph V) (C : H.ConnectedComponent) : Fintype C :=
  Fintype.ofFinite _

/-- A vertex together with its connected component is just a vertex. -/
def componentVertexEquiv (H : SimpleGraph V) :
    (Σ C : H.ConnectedComponent, C) ≃ V where
  toFun x := x.2.1
  invFun v := ⟨H.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨C, v, hv⟩
    subst C
    rfl
  right_inv v := rfl

/-- Sum first over components and then over the vertices in their supports. -/
theorem sum_components_vertices (H : SimpleGraph V)
    {A : Type w} [AddCommMonoid A] (f : V → A) :
    (∑ C : H.ConnectedComponent, ∑ v : C, f v.1) = ∑ v : V, f v := by
  calc
    _ = ∑ x : (Σ C : H.ConnectedComponent, C), f x.2.1 :=
      (Fintype.sum_sigma (fun x : (Σ C : H.ConnectedComponent, C) ↦
        f x.2.1)).symm
    _ = _ := Equiv.sum_comp (componentVertexEquiv H) f

/-- Filtered form of `sum_components_vertices`. -/
theorem sum_components_vertices_filter (H : SimpleGraph V)
    {A : Type w} [AddCommMonoid A] (P : V → Prop) [DecidablePred P]
    (f : V → A) :
    (∑ C : H.ConnectedComponent, ∑ v : C, if P v.1 then f v.1 else 0) =
      ∑ v : V, if P v then f v else 0 := by
  exact sum_components_vertices H (fun v ↦ if P v then f v else 0)

end

end WeightedEdgeColoring.SimpleGraph
