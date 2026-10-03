import WeightedEdgeColoring.SimpleGraphDegreeTwoEndpoints

/-!
# A connected graph of maximum degree two with two ends is a tree

This small counting lemma turns the Kempe component into a path-like tree.
It avoids a separate cycle classification: the two degree-one vertices
remove exactly two from the maximum possible degree sum, and connectedness
then forces exactly `|V|-1` edges.
-/

namespace WeightedEdgeColoring
namespace SimpleGraph

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem isTree_of_connected_of_degree_le_two_of_two_degree_one
    (H : _root_.SimpleGraph V) [DecidableRel H.Adj]
    (hconnected : H.Connected) (hdegree : ∀ v, H.degree v ≤ 2)
    {x y : V} (hxy : x ≠ y)
    (hx : H.degree x = 1) (hy : H.degree y = 1) :
    H.IsTree := by
  classical
  let ends : Finset V :=
    (Finset.univ : Finset V).filter fun v ↦ H.degree v = 1
  have hpair : ({x, y} : Finset V) ⊆ ends := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  have hpairCard : ({x, y} : Finset V).card = 2 := by
    simp [hxy]
  have hendsGe : 2 ≤ ends.card := by
    rw [← hpairCard]
    exact Finset.card_le_card hpair
  have hendsLe : ends.card ≤ 2 := by
    simpa [ends] using
      card_degreeOne_le_two_of_connected_of_degree_le_two
        H hconnected hdegree
  have hendsCard : ends.card = 2 := by omega
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
          ∑ v : V,
            (H.degree v + if H.degree v = 1 then 1 else 0) := by
        simp [ends, Finset.sum_add_distrib]
      _ ≤ ∑ _v : V, 2 := Finset.sum_le_sum fun v _hv ↦ hpoint v
      _ = 2 * Fintype.card V := by simp [Nat.mul_comm]
  have hedgeUpper : H.edgeFinset.card + 1 ≤ Fintype.card V := by
    have htwice :
        2 * H.edgeFinset.card + 2 ≤ 2 * Fintype.card V := by
      simpa [hendsCard, H.sum_degrees_eq_twice_card_edges] using hsum
    omega
  have hedgeLower : Fintype.card V ≤ H.edgeFinset.card + 1 := by
    have h := hconnected.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← H.edgeFinset_card] at h
    exact h
  apply H.isTree_iff_connected_and_card.mpr
  refine ⟨hconnected, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← H.edgeFinset_card]
  omega

end SimpleGraph
end WeightedEdgeColoring
