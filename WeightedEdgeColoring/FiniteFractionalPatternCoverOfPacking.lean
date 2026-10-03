import WeightedEdgeColoring.FiniteFractionalPatternCover

/-!
# Fractional covers from integral bin packings

An integral packing into `n` labelled bins gives a fractional pattern cover
of cost exactly `n`: use the contents of each labelled bin as one pattern of
mass one.  This elementary bridge is useful when a local star packing must be
fed into the finite two-bag extraction.
-/

open scoped BigOperators

namespace WeightedEdgeColoring
namespace BinPackingInstance

noncomputable section

universe u

variable {B : BinPackingInstance.{u}} {n : ℕ}

namespace PackingCertificate

/-- The one-bin pattern formed by the items assigned to bin `j`. -/
def binPattern (P : B.PackingCertificate n) (j : Fin n) : B.Pattern where
  multiplicity := fun i ↦ if P.bin i = j then 1 else 0
  capacity := by
    simpa [BinPackingInstance.binLoad] using P.load_le_one j

@[simp] theorem binPattern_multiplicity
    (P : B.PackingCertificate n) (j : Fin n) (i : B.Item) :
    (P.binPattern j).multiplicity i = if P.bin i = j then 1 else 0 := rfl

/-- Regard every labelled bin of an integral packing as a unit-mass
configuration. -/
def toFractionalPatternCover (P : B.PackingCertificate n) :
    B.FractionalPatternCover :=
  BinPackingInstance.FractionalPatternCover.ofFinitePatterns
    P.binPattern (fun _ : Fin n ↦ (1 : ℝ))
    (by intro j; norm_num)
    (by
      intro i
      simp [PackingCertificate.binPattern])

theorem toFractionalPatternCover_cost (P : B.PackingCertificate n) :
    P.toFractionalPatternCover.cost = n := by
  rw [PackingCertificate.toFractionalPatternCover]
  rw [BinPackingInstance.FractionalPatternCover.ofFinitePatterns_cost]
  simp

end PackingCertificate

/-- Any integral packing into `n` bins supplies a fractional pattern cover
of cost exactly `n`. -/
theorem exists_fractionalPatternCover_cost_eq_of_packsInto
    (h : B.PacksInto n) :
    ∃ C : B.FractionalPatternCover, C.cost = n := by
  rcases h with ⟨P⟩
  exact ⟨P.toFractionalPatternCover, P.toFractionalPatternCover_cost⟩

end


end BinPackingInstance
end WeightedEdgeColoring
