import WeightedEdgeColoring.FiniteExactDemandPatternCover
import WeightedEdgeColoring.FiniteFractionalPatternCoverOfPacking

/-!
# Exact unit-demand covers from ordinary packings

When the item type already indexes the physical objects, every object has
demand one.  An ordinary labelled packing therefore gives an exact-demand
packing certificate: the pattern of a bin contains precisely the items sent
to that bin.  This bridge lets the two-bag minimum-cost argument be applied
directly to physical indexed edges, which is the convenient starting point
for linear grouping.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable {B : BinPackingInstance.{u}} {n : ℕ}

namespace PackingCertificate

/-- The patterns of an ordinary packing cover every indexed physical item
exactly once. -/
def toUnitDemandExactPackingCertificate
    (P : B.PackingCertificate n) :
    ExactDemandPatternCover.PackingCertificate
      (B := B) (fun _ ↦ 1) n where
  pattern := P.binPattern
  covers_exact := by
    intro i
    simp [PackingCertificate.binPattern]

@[simp] theorem toUnitDemandExactPackingCertificate_pattern
    (P : B.PackingCertificate n) (j : Fin n) :
    (P.toUnitDemandExactPackingCertificate.pattern j) = P.binPattern j := rfl

end PackingCertificate

/-- An ordinary packing is also an exact packing of the unit-demand vector. -/
theorem unitDemand_packsInto_of_packsInto
    (h : B.PacksInto n) :
    ExactDemandPatternCover.PacksInto (B := B) (fun _ ↦ 1) n := by
  rcases h with ⟨P⟩
  exact ⟨P.toUnitDemandExactPackingCertificate⟩

/-- Hence an ordinary `n`-bin packing supplies an exact unit-demand cover of
cost exactly `n`. -/
theorem exists_unitDemandExactPatternCover_cost_eq_of_packsInto
    (h : B.PacksInto n) :
    ∃ C : B.ExactDemandPatternCover (fun _ ↦ 1), C.cost = n := by
  exact ExactDemandPatternCover.exists_cost_eq_of_packsInto
    (unitDemand_packsInto_of_packsInto h)

end

end BinPackingInstance
end WeightedEdgeColoring

#print axioms WeightedEdgeColoring.BinPackingInstance.unitDemand_packsInto_of_packsInto
#print axioms WeightedEdgeColoring.BinPackingInstance.exists_unitDemandExactPatternCover_cost_eq_of_packsInto
