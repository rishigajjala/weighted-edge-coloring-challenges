import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

/-!
# Endpoints in a graph of maximum degree two

This is the small graph-theoretic counting fact behind the bounded influence
of one Kempe-component coin.  In a finite connected graph of maximum degree
two, at most two vertices have degree one.

The proof uses only the handshaking identity and the fact that a connected
graph on `n` vertices has at least `n - 1` edges.  Keeping it separate avoids
building a path/cycle classification merely to obtain the endpoint bound.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

namespace SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite connected simple graph of maximum degree two has at most two
degree-one vertices. -/
theorem card_degreeOne_le_two_of_connected_of_degree_le_two
    (H : _root_.SimpleGraph V) [DecidableRel H.Adj]
    (hconnected : H.Connected) (hdegree : ∀ v, H.degree v ≤ 2) :
    ((Finset.univ : Finset V).filter fun v ↦ H.degree v = 1).card ≤ 2 := by
  classical
  let ends : Finset V :=
    (Finset.univ : Finset V).filter fun v ↦ H.degree v = 1
  have hpoint (v : V) :
      H.degree v + (if H.degree v = 1 then 1 else 0) ≤ 2 := by
    split_ifs with h
    · omega
    · simpa [h] using hdegree v
  have hsum :
      (∑ v : V, H.degree v) + ends.card ≤
        2 * Fintype.card V := by
    calc
      (∑ v : V, H.degree v) + ends.card =
          ∑ v : V, (H.degree v + if H.degree v = 1 then 1 else 0) := by
        simp [ends, Finset.sum_add_distrib]
      _ ≤ ∑ _v : V, 2 := Finset.sum_le_sum fun v _hv ↦ hpoint v
      _ = 2 * Fintype.card V := by simp [Nat.mul_comm]
  have hsum' :
      2 * H.edgeFinset.card + ends.card ≤
        2 * Fintype.card V := by
    simpa [H.sum_degrees_eq_twice_card_edges] using hsum
  have hconnectedCard :
      Fintype.card V ≤ H.edgeFinset.card + 1 := by
    have h := hconnected.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← H.edgeFinset_card] at h
    exact h
  have htwice :
      2 * Fintype.card V ≤ 2 * H.edgeFinset.card + 2 := by
    omega
  have : ends.card ≤ 2 := by omega
  simpa [ends] using this

end SimpleGraph
end WeightedEdgeColoring
