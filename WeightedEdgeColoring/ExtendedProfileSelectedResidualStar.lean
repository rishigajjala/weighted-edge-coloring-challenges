import WeightedEdgeColoring.ExtendedProfileSelectedDyadicInitialBounds
import WeightedEdgeColoring.ExtendedProfileBlockCapacityVarianceSelection
import WeightedEdgeColoring.WeightedMomentProposal
import WeightedEdgeColoring.LargeEdgeExtraCapture

/-!
# Weighted residual left by a selected profile

The private residual option has mass `1 - min 1 total`.  If the target total
mass is `rho*s <= 1`, this is bounded by the deterministic target deficit
`1-rho*s` plus the absolute error from the selected total mass.  Weighted
Cauchy--Schwarz then converts the already proved quadratic profile estimate
into a star-wise residual bound.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Pointwise clipping inequality behind the outer loss estimate. -/
theorem selectedBlockResidualOptionMass_le_target_add_abs
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hrs : rho * s ≤ 1) (e : G.E) :
    G.selectedBlockResidualOptionMass R0 rho omega choice e ≤
      (1 - rho * s) +
        |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s| := by
  unfold selectedBlockResidualOptionMass
  by_cases htotal : 1 ≤
      G.selectedBlockAllOptionMass R0 rho omega choice e
  · rw [min_eq_left htotal]
    have hgap : 0 ≤ 1 - rho * s := sub_nonneg.mpr hrs
    nlinarith [abs_nonneg
      (G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s)]
  · have htotal' : G.selectedBlockAllOptionMass R0 rho omega choice e ≤ 1 :=
      le_of_not_ge htotal
    rw [min_eq_right htotal']
    have habs : rho * s -
        G.selectedBlockAllOptionMass R0 rho omega choice e ≤
      |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s| := by
      rw [← neg_sub]
      exact neg_le_abs _
    linarith

/-- The masked large-edge residual is bounded by target deficit plus the
absolute selected-profile error. -/
theorem weightedResidualStar_selectedBlockLargeResidual_le_abs
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hrs : rho * s ≤ 1) (v : G.V) :
    G.weightedResidualStar
        (G.selectedBlockLargeResidual R0 omega rho choice) v ≤
      (1 - rho * s) * G.starWeight v +
        ∑ e : G.StarEdge v, G.weight e.1 *
          |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| := by
  classical
  unfold weightedResidualStar
  have hpoint (e : G.E) :
      (if G.Inc v e then
          G.selectedBlockLargeResidual R0 omega rho choice e * G.weight e
        else 0) ≤
      (if G.Inc v e then
          ((1 - rho * s) +
            |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s|) *
              G.weight e
        else 0) := by
    by_cases hinc : G.Inc v e
    · simp only [if_pos hinc]
      apply mul_le_mul_of_nonneg_right _ (G.weight_nonneg e)
      by_cases hlarge : β ≤ G.weight e
      · rw [G.selectedBlockLargeResidual_eq_of_large R0 omega rho choice hlarge]
        exact G.selectedBlockResidualOptionMass_le_target_add_abs
          R0 rho omega choice hrs e
      · simp [selectedBlockLargeResidual, hlarge]
        have hgap : 0 ≤ 1 - rho * s := sub_nonneg.mpr hrs
        positivity
    · simp [hinc]
  calc
    (∑ e, if G.Inc v e then
        G.selectedBlockLargeResidual R0 omega rho choice e * G.weight e else 0) ≤
      ∑ e, if G.Inc v e then
        ((1 - rho * s) +
          |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s|) *
            G.weight e else 0 :=
      Finset.sum_le_sum fun e _ ↦ hpoint e
    _ = (1 - rho * s) * G.starWeight v +
        ∑ e : G.StarEdge v, G.weight e.1 *
          |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| := by
      let I : Finset G.E := Finset.univ.filter (G.Inc v)
      have hmem : ∀ e : G.E, e ∈ I ↔ G.Inc v e := by simp [I]
      have hweight : (∑ e ∈ I, G.weight e) = G.starWeight v := by
        unfold starWeight
        exact Finset.sum_subtype I hmem (fun e ↦ G.weight e)
      have habs :
          (∑ e ∈ I,
            |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s| *
              G.weight e) =
            ∑ e : G.StarEdge v, G.weight e.1 *
              |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| := by
        calc
          _ = ∑ e : G.StarEdge v,
              |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| *
                G.weight e.1 :=
            Finset.sum_subtype I hmem _
          _ = _ := by simp only [mul_comm]
      calc
        _ = ∑ e ∈ I,
            ((1 - rho * s) +
              |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s|) *
                G.weight e := by
          dsimp [I]
          exact (Finset.sum_filter (s := Finset.univ) (G.Inc v)
            (fun e ↦ ((1 - rho * s) +
              |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s|) *
                G.weight e)).symm
        _ = _ := by
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hweight, habs]

/-- The same estimate before masking to large edges. -/
theorem weightedResidualStar_selectedBlockResidual_le_abs
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hrs : rho * s ≤ 1) (v : G.V) :
    G.weightedResidualStar
        (G.selectedBlockResidualOptionMass R0 rho omega choice) v ≤
      (1 - rho * s) * G.starWeight v +
        ∑ e : G.StarEdge v, G.weight e.1 *
          |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| := by
  classical
  unfold weightedResidualStar
  calc
    (∑ e, if G.Inc v e then
        G.selectedBlockResidualOptionMass R0 rho omega choice e * G.weight e
      else 0) ≤
      ∑ e, if G.Inc v e then
        ((1 - rho * s) +
          |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s|) *
            G.weight e else 0 := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hinc : G.Inc v e
      · simp only [if_pos hinc]
        exact mul_le_mul_of_nonneg_right
          (G.selectedBlockResidualOptionMass_le_target_add_abs
            R0 rho omega choice hrs e) (G.weight_nonneg e)
      · simp [hinc]
    _ = (1 - rho * s) * G.starWeight v +
        ∑ e : G.StarEdge v, G.weight e.1 *
          |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| := by
      let I : Finset G.E := Finset.univ.filter (G.Inc v)
      have hmem : ∀ e : G.E, e ∈ I ↔ G.Inc v e := by simp [I]
      have hweight : (∑ e ∈ I, G.weight e) = G.starWeight v := by
        unfold starWeight
        exact Finset.sum_subtype I hmem (fun e ↦ G.weight e)
      have habs :
          (∑ e ∈ I,
            |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s| *
              G.weight e) =
            ∑ e : G.StarEdge v, G.weight e.1 *
              |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| := by
        calc
          _ = ∑ e : G.StarEdge v,
              |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s| *
                G.weight e.1 :=
            Finset.sum_subtype I hmem _
          _ = _ := by simp only [mul_comm]
      calc
        _ = ∑ e ∈ I,
            ((1 - rho * s) +
              |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s|) *
                G.weight e := by
          dsimp [I]
          exact (Finset.sum_filter (s := Finset.univ) (G.Inc v)
            (fun e ↦ ((1 - rho * s) +
              |G.selectedBlockAllOptionMass R0 rho omega choice e - rho * s|) *
                G.weight e)).symm
        _ = _ := by
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hweight, habs]

/-- Weighted absolute profile error is at most the square root of star mass
times the weighted quadratic error. -/
theorem selectedBlockAbsoluteError_le_sqrt
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (v : G.V) (sigma : ℝ) (hsigma0 : 0 ≤ sigma)
    (hquad :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s) ^ 2) ≤
          sigma) :
    (∑ e : G.StarEdge v, G.weight e.1 *
      |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s|) ≤
        Real.sqrt (G.starWeight v * sigma) := by
  let S : Finset (G.StarEdge v) := Finset.univ
  have hcs := WeightedMultigraph.weighted_abs_error_sq_le S
    (fun e : G.StarEdge v ↦ G.weight e.1)
    (fun e : G.StarEdge v ↦
      G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s)
    (fun e _ ↦ G.weight_nonneg e.1)
  apply Real.le_sqrt_of_sq_le
  calc
    (∑ e : G.StarEdge v, G.weight e.1 *
      |G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s|) ^ 2 ≤
        G.starWeight v *
          ∑ e : G.StarEdge v, G.weight e.1 *
            (G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s) ^ 2 := by
      simpa [S, starWeight] using hcs
    _ ≤ G.starWeight v * sigma := by
      apply mul_le_mul_of_nonneg_left hquad
      unfold starWeight
      exact Finset.sum_nonneg fun e _ ↦ G.weight_nonneg e.1

/-- Final residual-star estimate from the selected quadratic bound. -/
theorem weightedResidualStar_selectedBlockLargeResidual_le_sqrt
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hrs : rho * s ≤ 1) (v : G.V) (sigma : ℝ) (hsigma0 : 0 ≤ sigma)
    (hquad :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedExtendedProfileTotalOptionMass
          R0 rho omega choice e.1 - rho * s) ^ 2) ≤ sigma) :
    G.weightedResidualStar
        (G.selectedBlockLargeResidual R0 omega rho choice) v ≤
      (1 - rho * s) * G.starWeight v +
        Real.sqrt (G.starWeight v * sigma) := by
  have hbase := G.weightedResidualStar_selectedBlockLargeResidual_le_abs
    R0 rho omega choice hrs v
  have hquad' :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s) ^ 2) ≤
          sigma := by
    simpa only [G.selectedBlockAllOptionMass_eq_total R0 choice rho omega] using hquad
  have habs := G.selectedBlockAbsoluteError_le_sqrt
    R0 rho omega choice v sigma hsigma0 hquad'
  exact hbase.trans (add_le_add le_rfl habs)

/-- Unmasked selected residual, in the same square-root form. -/
theorem weightedResidualStar_selectedBlockResidual_le_sqrt
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hrs : rho * s ≤ 1) (v : G.V) (sigma : ℝ) (hsigma0 : 0 ≤ sigma)
    (hquad :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedExtendedProfileTotalOptionMass
          R0 rho omega choice e.1 - rho * s) ^ 2) ≤ sigma) :
    G.weightedResidualStar
        (G.selectedBlockResidualOptionMass R0 rho omega choice) v ≤
      (1 - rho * s) * G.starWeight v +
        Real.sqrt (G.starWeight v * sigma) := by
  have hbase := G.weightedResidualStar_selectedBlockResidual_le_abs
    R0 rho omega choice hrs v
  have hquad' :
      (∑ e : G.StarEdge v, G.weight e.1 *
        (G.selectedBlockAllOptionMass R0 rho omega choice e.1 - rho * s) ^ 2) ≤
          sigma := by
    simpa only [G.selectedBlockAllOptionMass_eq_total R0 choice rho omega] using hquad
  have habs := G.selectedBlockAbsoluteError_le_sqrt
    R0 rho omega choice v sigma hsigma0 hquad'
  exact hbase.trans (add_le_add le_rfl habs)

/-- Restricting the unmasked residual to tiny edges only decreases its
weighted star load. -/
theorem tinyResidualLossLoad_selectedBlockResidual_le_weightedResidualStar
    (rho omega : ℝ)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1) (hrho : 0 ≤ rho)
    (v : G.V) :
    G.tinyResidualLossLoad (G.selectedBlockTinyEdges β)
        (fun e ↦ G.selectedBlockResidualOptionMass
          R0 rho omega choice e.1) v ≤
      G.weightedResidualStar
        (G.selectedBlockResidualOptionMass R0 rho omega choice) v := by
  classical
  unfold tinyResidualLossLoad weightedResidualStar
  have hsub := Finset.sum_subtype
    (p := fun e : G.E ↦ e ∈ G.selectedBlockTinyEdges β)
    (F := Finset.Subtype.fintype (G.selectedBlockTinyEdges β))
    (G.selectedBlockTinyEdges β) (by intro e; simp)
    (fun e ↦ if G.Inc v e then
      G.selectedBlockResidualOptionMass R0 rho omega choice e * G.weight e else 0)
  rw [← hsub]
  apply Finset.sum_le_univ_sum_of_nonneg
  intro e
  by_cases hinc : G.Inc v e
  · simp only [if_pos hinc]
    exact mul_nonneg
      (G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice e)
      (G.weight_nonneg e)
  · simp [hinc]

end WeightedSimpleGraph

end

end WeightedEdgeColoring
