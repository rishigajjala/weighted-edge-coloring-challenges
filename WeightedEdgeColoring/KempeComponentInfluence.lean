import WeightedEdgeColoring.KempeComponentEndpoints
import WeightedEdgeColoring.KempeComponentSwitchAverage

/-!
# Column influence of one Kempe component coin

One component coin changes missing indicators only at active vertices of its
two-color component, and there are at most two such vertices.  The generic
finite-sum theorem below converts any per-vertex cap budget into the column
budget needed by `WeightedMomentTwoSidedSelection`.
-/

namespace WeightedEdgeColoring
namespace WeightedMultigraph

open scoped BigOperators

universe u w

variable (G : WeightedMultigraph.{u})
variable {Row : Type w} [Fintype Row] [DecidableEq Row]

noncomputable local instance decidableSetMembershipInfluence (s : Set G.V) :
    DecidablePred (fun v : G.V ↦ v ∈ s) :=
  Classical.decPred _

noncomputable local instance finiteConnectedComponentSupportInfluence
    (H : SimpleGraph G.V) (C : H.ConnectedComponent) : Fintype C :=
  @Subtype.fintype G.V (fun v ↦ v ∈ C.supp)
    (decidableSetMembershipInfluence G C.supp) G.instFintypeV

noncomputable local instance decidableTwoColorActiveInfluence {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (C : G.TwoColorComponent F color a b) :
    DecidablePred (fun v : C ↦ G.IsTwoColorActive F color a b v.1) :=
  Classical.decPred _

/-- Active vertices of one fixed two-color component. -/
noncomputable def activeVerticesInComponent {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (C : G.TwoColorComponent F color a b) : Finset C :=
  (Finset.univ : Finset C).filter fun v ↦
    G.IsTwoColorActive F color a b v.1

theorem card_activeVerticesInComponent_le_two {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (C : G.TwoColorComponent F color a b) :
    (G.activeVerticesInComponent F color a b C).card ≤ 2 := by
  exact G.card_activeVertices_twoColorComponent_le_two
    F color hproper a b C

/-- Cap charged by one component coin to one statistic row. -/
noncomputable def componentInfluenceCap {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (vertexCap : G.V → Row → ℝ)
    (C : G.TwoColorComponent F color a b) (row : Row) : ℝ :=
  ∑ v ∈ G.activeVerticesInComponent F color a b C, vertexCap v.1 row

theorem componentInfluenceCap_nonneg {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q) (a b : Fin q)
    (vertexCap : G.V → Row → ℝ)
    (hcap0 : ∀ v row, 0 ≤ vertexCap v row)
    (C : G.TwoColorComponent F color a b) (row : Row) :
    0 ≤ G.componentInfluenceCap F color a b vertexCap C row := by
  unfold componentInfluenceCap
  apply Finset.sum_nonneg
  intro v _hv
  exact hcap0 v.1 row

/-- A per-vertex row-sum budget `B` becomes a per-component column budget
`2B`.  This is the exact use of the fact that a path component has two ends;
the number of graph vertices and the length of the path never enter. -/
theorem sum_componentInfluenceCap_le_two_mul {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (vertexCap : G.V → Row → ℝ)
    (hcap0 : ∀ v row, 0 ≤ vertexCap v row)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hvertex : ∀ v, ∑ row : Row, vertexCap v row ≤ B)
    (C : G.TwoColorComponent F color a b) :
    ∑ row : Row,
        G.componentInfluenceCap F color a b vertexCap C row ≤ 2 * B := by
  let active := G.activeVerticesInComponent F color a b C
  have hcard : active.card ≤ 2 :=
    G.card_activeVerticesInComponent_le_two F color hproper a b C
  calc
    (∑ row : Row,
      G.componentInfluenceCap F color a b vertexCap C row) =
        ∑ v ∈ active, ∑ row : Row, vertexCap v.1 row := by
      unfold componentInfluenceCap
      rw [Finset.sum_comm]
    _ ≤ ∑ _v ∈ active, B := by
      exact Finset.sum_le_sum fun v _hv ↦ hvertex v.1
    _ = (active.card : ℝ) * B := by simp
    _ ≤ 2 * B := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB0

/-- If each active vertex can affect at most `m` rows, each by at most `A`,
then one component coin has total column cap at most `2mA`.  This cardinal
form is useful for the two current colors and the `K` possible partner
colors in the first/second moment rows. -/
theorem sum_componentInfluenceCap_le_two_mul_card_mul {q : ℕ}
    (F : Finset G.E) (color : G.E → Fin q)
    (hproper : G.IsProperOn F color) (a b : Fin q)
    (vertexCap : G.V → Row → ℝ)
    (hcap0 : ∀ v row, 0 ≤ vertexCap v row)
    (A : ℝ) (hA0 : 0 ≤ A)
    (hcapA : ∀ v row, vertexCap v row ≤ A)
    (C : G.TwoColorComponent F color a b) :
    ∑ row : Row,
        G.componentInfluenceCap F color a b vertexCap C row ≤
      2 * (Fintype.card Row : ℝ) * A := by
  rw [mul_assoc]
  apply G.sum_componentInfluenceCap_le_two_mul
    F color hproper a b vertexCap hcap0
    ((Fintype.card Row : ℝ) * A) (mul_nonneg (by positivity) hA0)
    (fun v ↦ ?_) C
  calc
    (∑ row : Row, vertexCap v row) ≤ ∑ _row : Row, A :=
      Finset.sum_le_sum fun row _hrow ↦ hcapA v row
    _ = (Fintype.card Row : ℝ) * A := by simp

end WeightedMultigraph
end WeightedEdgeColoring
