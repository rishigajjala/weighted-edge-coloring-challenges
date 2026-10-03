import WeightedEdgeColoring.BinPacking
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean

/-!
# Finiteness of one-bin patterns

For a finite bin-packing instance with strictly positive item weights, every
coordinate of a feasible integer pattern is bounded.  Hence the type of all
one-bin patterns is finite.  This is the first compactness input needed to
choose minimum-cost finite fractional pattern covers without adding an
attainment assumption.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable (B : BinPackingInstance.{u})

namespace Pattern

/-- The contribution of one coordinate is bounded by the total pattern
load. -/
theorem coordinate_load_le (p : B.Pattern) (i : B.Item) :
    (p.multiplicity i : ℝ) * B.weight i ≤ 1 := by
  calc
    (p.multiplicity i : ℝ) * B.weight i ≤
        ∑ j : B.Item, (p.multiplicity j : ℝ) * B.weight j := by
      exact Finset.single_le_sum
        (fun j _hj ↦ mul_nonneg (Nat.cast_nonneg _) (B.weight_nonneg j))
        (Finset.mem_univ i)
    _ ≤ 1 := p.capacity

/-- A feasible pattern uses at most `floor (1 / weight i)` copies of item
type `i`. -/
theorem multiplicity_le_floor (p : B.Pattern) (i : B.Item) :
    p.multiplicity i ≤ Nat.floor (1 / B.weight i) := by
  apply Nat.le_floor
  apply (le_div_iff₀ (B.weight_pos i)).2
  simpa using coordinate_load_le B p i

/-- Encode a pattern by bounded coordinates. -/
def finiteCode (p : B.Pattern) :
    ∀ i : B.Item, Fin (Nat.floor (1 / B.weight i) + 1) :=
  fun i ↦ ⟨p.multiplicity i,
    Nat.lt_succ_of_le (multiplicity_le_floor B p i)⟩

theorem finiteCode_injective : Function.Injective (finiteCode B) := by
  intro p q h
  cases p with
  | mk pmult pcap =>
    cases q with
    | mk qmult qcap =>
      congr
      funext i
      have hi := congrFun h i
      exact congrArg Fin.val hi

noncomputable instance instFintype : Fintype B.Pattern :=
  Fintype.ofInjective (finiteCode B) (finiteCode_injective B)

noncomputable instance instDecidableEq : DecidableEq B.Pattern :=
  Classical.decEq B.Pattern

end Pattern

end

end BinPackingInstance
end WeightedEdgeColoring
