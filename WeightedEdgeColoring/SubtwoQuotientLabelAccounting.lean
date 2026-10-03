import WeightedEdgeColoring.SubtwoQuotientHybridCharge
import WeightedEdgeColoring.SubtwoFiniteTinyActualInflation

/-! Sum the local label-law bounds before returning to original vertices. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
universe u

namespace GeneralColoredPacketBase
variable {G : WeightedMultigraph.{u}} {K : ℕ}
variable (C : G.GeneralColoredPacketBase K)

/-- The finite/tiny class formula is the split-charge row with one label retained. -/
theorem quotientSplitLabelLoad_eq_classes
    {T : ℕ} (finite : Finset C.residualGraph.E)
    (classOf : C.residualGraph.E → Fin T) (tau : ℝ)
    {Label : Type*} [DecidableEq Label]
    (v : G.V) (edgeLabel : C.residualGraph.StarEdge v → Label)
    (label : Label) (x : C.residualGraph.StarEdge v → ℝ)
    (hcharge : ∀ e ∈ finite, harmonicCharge (C.residualGraph.weight e) =
      (1 : ℝ) / finiteClassSize (classOf e)) :
    (∑ e : C.residualGraph.StarEdge v,
      if edgeLabel e = label then C.quotientSplitCharge finite tau e.1 * x e else 0) =
    (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∈ finite},
      if edgeLabel e.1 = label then x e.1 / (finiteClassSize (classOf e.1.1) : ℝ)
        else 0) +
    (∑ e : {e : C.residualGraph.StarEdge v // e.1 ∉ finite},
      if edgeLabel e.1 = label then C.residualGraph.weight e.1.1 * x e.1 else 0) /
        (1 - tau) := by
  simpa only [mul_ite, mul_zero, ite_div, zero_div] using
    C.quotientSplitChargeLoad_eq_classes finite classOf tau
      (fun e => if edgeLabel e = label then x e else 0) hcharge

/-- Summing a label law over colors costs at most one split charge per edge,
plus its explicit per-color overhead. -/
theorem sum_labelMass_le_splitLabelCharge
    (finite : Finset C.residualGraph.E) (tau : ℝ) (htau : tau < 1)
    {Color : Type*} [Fintype Color]
    {Label : Type*} [DecidableEq Label]
    (v : G.V) (edgeLabel : C.residualGraph.StarEdge v → Label)
    (label : Label) (x : C.residualGraph.E → Color → ℝ)
    (labelMass : Color → ℝ) (overhead : ℝ)
    (hmass : ∀ e, ∑ c, x e c ≤ 1)
    (hlabel : ∀ c, labelMass c ≤
      (∑ e : C.residualGraph.StarEdge v,
        if edgeLabel e = label then
          C.quotientSplitCharge finite tau e.1 * x e.1 c else 0) + overhead) :
    (∑ c, labelMass c) ≤
      (∑ e : C.residualGraph.StarEdge v,
        if edgeLabel e = label then C.quotientSplitCharge finite tau e.1 else 0) +
        Fintype.card Color * overhead := by
  classical
  calc
    (∑ c, labelMass c) ≤ ∑ c,
        ((∑ e : C.residualGraph.StarEdge v,
          if edgeLabel e = label then
            C.quotientSplitCharge finite tau e.1 * x e.1 c else 0) + overhead) :=
      Finset.sum_le_sum (fun c _ => hlabel c)
    _ = (∑ e : C.residualGraph.StarEdge v,
        if edgeLabel e = label then
          C.quotientSplitCharge finite tau e.1 * (∑ c, x e.1 c) else 0) +
          Fintype.card Color * overhead := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : edgeLabel e = label <;> simp [he, Finset.mul_sum]
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply Finset.sum_le_sum
      intro e _
      by_cases he : edgeLabel e = label
      · simp only [he, if_true]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hmass e.1)
          (C.quotientSplitCharge_nonneg finite tau htau e.1)
      · simp [he]

/-- At a fixed original endpoint, only the tiny weight carrying that endpoint
label pays the inflation. There is no block-size factor in this estimate. -/
theorem splitLabelCharge_le_harmonic_add_twoTau
    (finite : Finset C.residualGraph.E) (tau n : ℝ)
    (htau0 : 0 ≤ tau) (htauHalf : tau ≤ (1 : ℝ) / 2) (hn : 0 ≤ n)
    {Label : Type*} [DecidableEq Label]
    (v : G.V) (edgeLabel : C.residualGraph.StarEdge v → Label) (label : Label)
    (htiny : (∑ e : C.residualGraph.StarEdge v,
      if edgeLabel e = label ∧ e.1 ∉ finite then C.residualGraph.weight e.1 else 0) ≤ n) :
    (∑ e : C.residualGraph.StarEdge v,
      if edgeLabel e = label then C.quotientSplitCharge finite tau e.1 else 0) ≤
    (∑ e : C.residualGraph.StarEdge v,
      if edgeLabel e = label then harmonicCharge (C.residualGraph.weight e.1) else 0) +
      2 * tau * n := by
  classical
  have htau1 : tau < 1 := by linarith
  have hcoef0 : 0 ≤ tau / (1 - tau) := div_nonneg htau0 (by linarith)
  have hcoef : tau / (1 - tau) ≤ 2 * tau := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - tau)).2
    nlinarith [mul_nonneg htau0 (sub_nonneg.mpr htauHalf)]
  have hpoint : ∀ e : C.residualGraph.StarEdge v,
      (if edgeLabel e = label then C.quotientSplitCharge finite tau e.1 else 0) ≤
      (if edgeLabel e = label then harmonicCharge (C.residualGraph.weight e.1) else 0) +
      tau / (1 - tau) *
        (if edgeLabel e = label ∧ e.1 ∉ finite then C.residualGraph.weight e.1 else 0) := by
    intro e
    by_cases hl : edgeLabel e = label
    · by_cases he : e.1 ∈ finite
      · simp [hl, he, quotientSplitCharge]
      · simp only [hl, he, not_false_eq_true, true_and, if_true,
          quotientSplitCharge, if_false]
        exact tinyInflatedWeight_le_harmonic_add htau0 htau1
          (C.residualGraph.weight_pos e.1) (C.residualGraph.weight_le_one e.1)
    · simp [hl]
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ :
    Finset (C.residualGraph.StarEdge v))) => hpoint e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact hsum.trans (add_le_add le_rfl
    ((mul_le_mul_of_nonneg_left htiny hcoef0).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef hn)))

end GeneralColoredPacketBase
end
end WeightedEdgeColoring.WeightedMultigraph
