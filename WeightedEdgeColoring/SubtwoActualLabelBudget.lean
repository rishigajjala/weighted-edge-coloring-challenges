import WeightedEdgeColoring.SubtwoOriginalEndpointLabelCharge
import WeightedEdgeColoring.SubtwoQuotientFiniteThresholdClass

/-! Uniform original-vertex label budgets for the actual threshold law. -/

namespace WeightedEdgeColoring.WeightedMultigraph
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1500000
universe u
variable (G : WeightedMultigraph.{u})
variable {Q : Type u} [Fintype Q] [DecidableEq Q]

theorem sum_quotientThresholdLabelMass_le_original
    (block : G.V → Q) (hfiber : ∀ q, (G.subtwoFiber block q).card ≤ 5)
    {K n : ℕ} (C : (G.subtwoQuotient block).GeneralColoredPacketBase K)
    (F : Finset G.E) (hfull : C.fullEdges = G.subtwoQuotientSelectedEdges block F)
    (T : ℕ) (hT : 160 ≤ T) (hn : 0 < n)
    (q : Q) (v : G.V) (hv : block v = q) (hlocal : G.LocallyPacksInto n)
    {Color : Type*} [Fintype Color]
    (hcolors : (Fintype.card Color : ℝ) ≤ 4 * n)
    (x : C.residualGraph.E → Color → ℝ)
    (labelMass : Color → ℝ)
    (hmass : ∀ e, ∑ c, x e c ≤ 1)
    (hlabel : ∀ c, labelMass c ≤
      (∑ e : {e : C.residualGraph.StarEdge q // e.1 ∈ C.quotientFiniteEdges T},
        if G.subtwoQuotientResidualEdgeLabel block hfiber C q e.1 =
            G.subtwoLocalSixLabel block hfiber q v then
          x e.1.1 c / (finiteClassSize (C.quotientThresholdClass T (by omega) e.1.1) : ℝ)
        else 0) +
      (∑ e : {e : C.residualGraph.StarEdge q // e.1 ∉ C.quotientFiniteEdges T},
        if G.subtwoQuotientResidualEdgeLabel block hfiber C q e.1 =
            G.subtwoLocalSixLabel block hfiber q v then
          C.residualGraph.weight e.1.1 * x e.1.1 c else 0) /
            (1 - (1 : ℝ) / T) + (T + 1 : ℝ) * (100 / n)) :
    (∑ c, labelMass c) ≤
      G.chargeOn harmonicCharge
        (G.subtwoCrossingSelectedEdges block Finset.univ \ F) v +
          2 * ((1 : ℝ) / T) * n + 400 * (T + 1 : ℝ) := by
  have hTpos : 0 < T := by omega
  have hTR : (160 : ℝ) ≤ T := by exact_mod_cast hT
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htauHalf : (1 : ℝ) / T ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < T)).2
    linarith
  have hcharge : ∀ e ∈ C.quotientFiniteEdges T,
      harmonicCharge (C.residualGraph.weight e) =
        (1 : ℝ) / finiteClassSize (C.quotientThresholdClass T hTpos e) := by
    intro e he
    exact C.quotientThresholdClass_charge T hTpos e he
  have hraw := G.sum_quotientLabelMass_le_originalResidualCharge
    block hfiber C F hfull (C.quotientFiniteEdges T) ((1 : ℝ) / T)
    (by positivity) htauHalf q v hv hlocal x labelMass
    ((T + 1 : ℝ) * (100 / n)) hmass (by
      intro c
      rw [C.quotientSplitLabelLoad_eq_classes (C.quotientFiniteEdges T)
        (C.quotientThresholdClass T hTpos) ((1 : ℝ) / T)
        q (G.subtwoQuotientResidualEdgeLabel block hfiber C q)
        (G.subtwoLocalSixLabel block hfiber q v)
        (fun e => x e.1 c) hcharge]
      exact hlabel c)
  have herror : (Fintype.card Color : ℝ) * ((T + 1 : ℝ) * (100 / n)) ≤
      400 * (T + 1 : ℝ) := by
    calc
      _ ≤ (4 * n) * ((T + 1 : ℝ) * (100 / n)) :=
        mul_le_mul_of_nonneg_right hcolors (by positivity)
      _ = _ := by field_simp; ring
  exact hraw.trans (add_le_add le_rfl herror)

/-- Add packet colors and selected residual labels at one original vertex.
The decoder uses the fourfold scale `4 n`. -/
theorem selectedLabelCount_le_originalResidualBudget
    {n K T : ℕ} {tau eta residual mass selected : ℝ}
    (htau : 0 ≤ tau) (hK : (K : ℝ) ≤ 4 * n)
    (hmass : mass ≤ residual + 2 * ((1 : ℝ) / T) * n + 400 * (T + 1 : ℝ))
    (hselected : selected ≤ mass + K * tau + eta * (4 * n)) :
    selected ≤ residual + (2 * ((1 : ℝ) / T) + 4 * tau + 4 * eta) * n +
      400 * (T + 1 : ℝ) := by
  have hpadding := mul_le_mul_of_nonneg_right hK htau
  nlinarith

 /-- Add the packet part of the original-vertex charge budget. -/
theorem boundaryLabelCount_le_originalBudget
    {n K T : ℕ} {tau eta base residual exterior selected total : ℝ}
    (htau : 0 ≤ tau) (hK : (K : ℝ) ≤ 4 * n)
    (hbase : base + residual ≤ exterior)
    (hselected : selected ≤ residual + 2 * ((1 : ℝ) / T) * n +
      400 * (T + 1 : ℝ) + K * tau + eta * (4 * n))
    (htotal : total ≤ base + selected) :
    total ≤ exterior + (2 * ((1 : ℝ) / T) + 4 * tau + 4 * eta) * n +
      400 * (T + 1 : ℝ) := by
  have hpadding := mul_le_mul_of_nonneg_right hK htau
  nlinarith

end
end WeightedEdgeColoring.WeightedMultigraph
