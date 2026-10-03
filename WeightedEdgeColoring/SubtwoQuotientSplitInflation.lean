import WeightedEdgeColoring.SubtwoQuotientFiniteTinyLabelFactory
import WeightedEdgeColoring.SubtwoQuotientHybridCharge
import WeightedEdgeColoring.SubtwoFiniteTinyActualInflation

/-! The generic finite/tiny quotient charge exceeds harmonic charge only by
the total tiny weight times the usual slack factor. -/

namespace WeightedEdgeColoring.WeightedMultigraph

open scoped BigOperators
noncomputable section
universe u
namespace GeneralColoredPacketBase
variable {G : WeightedMultigraph.{u}} {K : ℕ}
variable (C : G.GeneralColoredPacketBase K)

def quotientTinyStarWeight (finite : Finset C.residualGraph.E)
    (v : G.V) : ℝ :=
  ∑ e : C.residualGraph.StarEdge v,
    if e.1 ∈ finite then 0 else C.residualGraph.weight e.1

/-- Exact charge comparison; the finite edge part has no inflation. -/
theorem quotientSplitStarCharge_le_harmonic_add_tinyWeight
    (finite : Finset C.residualGraph.E) (tau : ℝ)
    (htau0 : 0 ≤ tau) (htau1 : tau < 1) (v : G.V) :
    (∑ e : C.residualGraph.StarEdge v,
      C.quotientSplitCharge finite tau e.1) ≤
    C.residualGraph.starCharge harmonicCharge v +
      tau / (1 - tau) * C.quotientTinyStarWeight finite v := by
  unfold quotientTinyStarWeight starCharge
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  by_cases he : e.1 ∈ finite
  · simp [quotientSplitCharge, he]
  · simp only [quotientSplitCharge, he, if_false]
    exact tinyInflatedWeight_le_harmonic_add htau0 htau1
      (C.residualGraph.weight_pos e.1)
      (C.residualGraph.weight_le_one e.1)

/-- If the tiny subset has total load at most `n`, its artificial inflation
costs at most `2 tau n` for tau≤1/2. -/
theorem quotientSplitStarCharge_le_harmonic_add_twoTau
    (finite : Finset C.residualGraph.E) (tau n : ℝ)
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2)
    (hn : 0 ≤ n)
    (htiny : ∀ v, C.quotientTinyStarWeight finite v ≤ n)
    (v : G.V) :
    C.quotientSplitStarCharge finite tau v ≤
      C.residualGraph.starCharge harmonicCharge v + 2 * tau * n := by
  have htau1 : tau < 1 := by linarith
  have hratio : tau / (1 - tau) ≤ 2 * tau := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - tau)).2
    nlinarith [mul_nonneg htau0 (sub_nonneg.mpr htauHalf)]
  have htiny0 : 0 ≤ C.quotientTinyStarWeight finite v := by
    unfold quotientTinyStarWeight
    apply Finset.sum_nonneg
    intro e _
    split
    · exact le_rfl
    · exact C.residualGraph.weight_nonneg e.1
  have hmul : tau / (1 - tau) * C.quotientTinyStarWeight finite v ≤
      2 * tau * n := by
    calc
      _ ≤ 2 * tau * C.quotientTinyStarWeight finite v :=
        mul_le_mul_of_nonneg_right hratio htiny0
      _ ≤ 2 * tau * n :=
        mul_le_mul_of_nonneg_left (htiny v) (by positivity)
  have hbase := C.quotientSplitStarCharge_le_harmonic_add_tinyWeight
    finite tau htau0 htau1 v
  exact hbase.trans (add_le_add_right hmul _)

end GeneralColoredPacketBase
end
end WeightedEdgeColoring.WeightedMultigraph
