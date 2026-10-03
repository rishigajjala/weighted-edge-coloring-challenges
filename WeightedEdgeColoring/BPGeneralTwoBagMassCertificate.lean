import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite mass certificates for the general triangle packet bound

This file isolates the algebraic core of the manuscript lemma `Packing two
collections`.  It deliberately takes the output of the bin-by-bin pairing as
explicit finite witness data.  Thus no existence theorem for an optimum
configuration LP, and no choice of an infinite pattern space, is hidden in
the result.

For an oriented pair of collections, `ell`, `m`, and `z` are the masses of
first-heavy, second-heavy, and remaining bins after the heavy sides have been
named so that the first-heavy mass is the larger one.  The mass `p` is the
part of the paired heavy mass on which the first-side packets are combined.
The two displayed bounds are exactly the separate fractional packing costs
constructed in the manuscript proof.
-/

namespace WeightedEdgeColoring

/-- Explicit algebraic output of pairing the heavy bins in a fractional
packing of two collections.  The parameters `a` and `b` are any lower costs
dominated by the two separate packings constructed from the witness, and
`T` is the mass of the original joint packing.

The hypothesis `m ≤ ell`, needed when constructing this data from bins, is
retained in the structure even though the final arithmetic only needs
`p ≤ m`. -/
structure OrientedTwoBagMassCertificate (a b T : ℝ) where
  ell : ℝ
  m : ℝ
  z : ℝ
  p : ℝ
  ell_nonneg : 0 ≤ ell
  m_nonneg : 0 ≤ m
  z_nonneg : 0 ≤ z
  p_nonneg : 0 ≤ p
  m_le_ell : m ≤ ell
  p_le_m : p ≤ m
  total : T = ell + m + z
  first_cost_le :
    a ≤ ell + m / 2 - p / 2 + z / 2
  second_cost_le :
    b ≤ ell / 2 + m / 2 + p / 2 + z / 2

namespace OrientedTwoBagMassCertificate

/-- The exact oriented half-cost inequality obtained from the four masses. -/
theorem half_first_add_second_le {a b T : ℝ}
    (C : OrientedTwoBagMassCertificate a b T) :
    a / 2 + b ≤ T := by
  rw [C.total]
  nlinarith [C.first_cost_le, C.second_cost_le, C.p_le_m, C.z_nonneg]

end OrientedTwoBagMassCertificate

/-- The bin pairing may produce either orientation.  This is the finite
certificate form of
`min (a / 2 + b) (a + b / 2) ≤ T`. -/
def TwoBagMassCertificate (a b T : ℝ) : Prop :=
  Nonempty (OrientedTwoBagMassCertificate a b T) ∨
    Nonempty (OrientedTwoBagMassCertificate b a T)

/-- An explicit two-bag certificate implies the symmetric minimum bound from
the manuscript. -/
theorem min_half_add_le_of_twoBagMassCertificate {a b T : ℝ}
    (C : TwoBagMassCertificate a b T) :
    min (a / 2 + b) (a + b / 2) ≤ T := by
  rcases C with ⟨⟨C⟩⟩ | ⟨⟨C⟩⟩
  · exact (min_le_left _ _).trans C.half_first_add_second_le
  · exact (min_le_right _ _).trans (by
      simpa [add_comm] using C.half_first_add_second_le)

/-- The symmetric numerical relation supplied by a two-collection packing. -/
def TwoBagBound (a b T : ℝ) : Prop :=
  min (a / 2 + b) (a + b / 2) ≤ T

theorem TwoBagBound.symm {a b T : ℝ} (h : TwoBagBound a b T) :
    TwoBagBound b a T := by
  unfold TwoBagBound at h ⊢
  calc
    min (b / 2 + a) (b + a / 2) =
        min (a + b / 2) (a / 2 + b) := by congr 1 <;> ring
    _ = min (a / 2 + b) (a + b / 2) := min_comm _ _
    _ ≤ T := h

/-- If `a` is the larger of two costs and `c` is no larger than the second,
the two-bag bound for `a,b` controls half of the three-cost sum. -/
theorem three_cost_le_two_mul_of_ordered_twoBagBound
    {a b c n : ℝ} (hba : b ≤ a) (hcb : c ≤ b)
    (hab : TwoBagBound a b n) :
    a + b + c ≤ 2 * n := by
  unfold TwoBagBound at hab
  have hmin : min (a / 2 + b) (a + b / 2) = a / 2 + b := by
    apply min_eq_left
    linarith
  rw [hmin] at hab
  linarith

/-- Three pairwise local two-bag bounds imply the exact triangle coefficient
two.  No nonnegativity assumptions are needed for this algebraic statement. -/
theorem three_cost_le_two_mul_of_pairwise_twoBagBound
    {a b c n : ℝ}
    (hab : TwoBagBound a b n)
    (hac : TwoBagBound a c n)
    (hbc : TwoBagBound b c n) :
    a + b + c ≤ 2 * n := by
  unfold TwoBagBound at hab hac hbc
  simp only [min_le_iff] at hab hac hbc
  rcases hab with hab | hab <;>
    rcases hac with hac | hac <;>
    rcases hbc with hbc | hbc <;>
    linarith

/-- Certificate-level version of the preceding theorem, ready to consume the
finite witnesses extracted independently from the three pairwise local
packings. -/
theorem three_cost_le_two_mul_of_pairwise_massCertificates
    {a b c n Tab Tac Tbc : ℝ}
    (Cab : TwoBagMassCertificate a b Tab) (hTab : Tab ≤ n)
    (Cac : TwoBagMassCertificate a c Tac) (hTac : Tac ≤ n)
    (Cbc : TwoBagMassCertificate b c Tbc) (hTbc : Tbc ≤ n) :
    a + b + c ≤ 2 * n := by
  apply three_cost_le_two_mul_of_pairwise_twoBagBound
  · exact (min_half_add_le_of_twoBagMassCertificate Cab).trans hTab
  · exact (min_half_add_le_of_twoBagMassCertificate Cac).trans hTac
  · exact (min_half_add_le_of_twoBagMassCertificate Cbc).trans hTbc

/-- Natural packet counts bounded by the three fractional bundle costs also
obey the required triangle edge-count estimate. -/
theorem three_packetCounts_le_two_mul_of_pairwise_massCertificates
    (pA pB pC : ℕ) {a b c n Tab Tac Tbc : ℝ}
    (hpA : (pA : ℝ) ≤ a) (hpB : (pB : ℝ) ≤ b)
    (hpC : (pC : ℝ) ≤ c)
    (Cab : TwoBagMassCertificate a b Tab) (hTab : Tab ≤ n)
    (Cac : TwoBagMassCertificate a c Tac) (hTac : Tac ≤ n)
    (Cbc : TwoBagMassCertificate b c Tbc) (hTbc : Tbc ≤ n) :
    ((pA + pB + pC : ℕ) : ℝ) ≤ 2 * n := by
  have hcost := three_cost_le_two_mul_of_pairwise_massCertificates
    Cab hTab Cac hTac Cbc hTbc
  push_cast
  linarith

end WeightedEdgeColoring
