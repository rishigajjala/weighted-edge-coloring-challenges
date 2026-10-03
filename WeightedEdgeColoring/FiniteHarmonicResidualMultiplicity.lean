import WeightedEdgeColoring.FiniteHarmonicClassEncoding
import WeightedEdgeColoring.BoundedMultiplicityWholeEdgeRounding

/-!
# The explicit multiplicity of a finite harmonic residual

After grouping class `r` in blocks of `r`, fewer than `r` edges remain in
each endpoint fibre.  Summing over the first `T` harmonic classes gives the
fixed bound `T * (T - 1) / 2`.  This file records that elementary conversion
in the form used by coordinated multigraph rounding.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

universe u

/-- The sum of the zero-based indices of `Fin T`. -/
theorem sum_fin_val (T : ℕ) :
    (∑ a : Fin T, a.1) = T * (T - 1) / 2 := by
  calc
    (∑ a : Fin T, a.1) = ∑ i ∈ Finset.range T, i :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i) T
    _ = T * (T - 1) / 2 := Finset.sum_range_id T

namespace WeightedMultigraph

variable {G : WeightedMultigraph.{u}} {T K : ℕ}
variable {b : G.Bipartition} {classOf : G.E → Fin T}

/-- The residual of a finite harmonic packet certificate has a graph-size
independent parallel-edge bound. -/
theorem FiniteHarmonicPacketColoringCertificate.residualGraph_orientedPairCell_card_le
    (C : G.FiniteHarmonicPacketColoringCertificate b classOf K)
    (k : G.V × G.V) :
    (C.residualBipartition.orientedPairCell k).card ≤
      T * (T - 1) / 2 := by
  rw [← sum_fin_val T]
  exact C.residualSimpleLayering.orientedPairCell_card_le k

/-- The same residual bound in the unordered endpoint-pair form used by the
rank-three option system. -/
theorem FiniteHarmonicPacketColoringCertificate.residualGraph_pairMultiplicityAtMost
    (C : G.FiniteHarmonicPacketColoringCertificate b classOf K) :
    C.residualGraph.PairMultiplicityAtMost (T * (T - 1) / 2) :=
  C.residualBipartition.pairMultiplicityAtMost_of_orientedPair
    C.residualGraph_orientedPairCell_card_le

end WeightedMultigraph

end


end WeightedEdgeColoring
