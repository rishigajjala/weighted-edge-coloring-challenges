import WeightedEdgeColoring.DyadicWeightUpperBounds
import WeightedEdgeColoring.LargeEdgeExtraCapture
import WeightedEdgeColoring.ProfileLargeEdgePackage

/-!
# Dyadic extra-edge capture

This file specializes the abstract extra-slot capacity estimate to the
least dyadic bucket map.  The shared dyadic upper-weight arithmetic lives in
`DyadicWeightUpperBounds`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedSimpleGraph

universe u w₁

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} [Fintype Color] [DecidableEq Color]

/-- Dyadic specialization of the extra-capture estimate.  The selected
leave-uncolored weight is bounded by twice the fractional residual weight,
plus an explicit geometric-series reserve. -/
theorem selectedExtraEdges_starWeight_le_dyadic
    (K N : ℕ) (beta : ℝ) (L : ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K
      (dyadicBucket beta L G.weight)
      (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
      x residual)))
    (hM : ((G.largeEdgeOptionSystem K (dyadicBucket beta L G.weight)
      (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)).quantized N
      (G.largeEdgeMass K (dyadicBucket beta L G.weight)
        (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
        x residual)).IsPartialMatching M)
    (hbeta : 0 < beta) (hcover : 1 ≤ dyadicScale beta L)
    (hlower : ∀ e, beta ≤ G.weight e)
    (hr0 : ∀ e, 0 ≤ residual e) (hgamma1 : gamma < 1)
    (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges K N (dyadicBucket beta L G.weight)
        (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
        x residual M).filter (G.Inc v), G.weight e) ≤
      2 * G.weightedResidualStar residual v / (1 - gamma) +
        (1 + (t : ℝ)) * (beta * ((2 : ℝ) ^ (L + 1) - 1)) := by
  have hbase := G.selectedExtraEdges_starWeight_le_weightedResidual
    K N (dyadicBucket beta L G.weight) x residual gamma 2 t M hM
    hr0 hgamma1 (dyadicUpper beta)
    (fun h ↦ dyadicUpper_nonneg hbeta.le h)
    (fun e ↦ weight_le_dyadicUpper_bucket beta L G.weight hcover
      (fun e _ ↦ G.weight_le_one e) (Finset.mem_univ e))
    (fun e ↦ dyadicUpper_bucket_le_two_mul beta L G.weight hbeta hcover
      (fun e _ ↦ hlower e) (fun e _ ↦ G.weight_le_one e)
      (Finset.mem_univ e)) v
  simpa [sum_dyadicUpper_eq] using hbase

/-- A version exposing only the top dyadic scale in the additive reserve. -/
theorem selectedExtraEdges_starWeight_le_dyadic_top
    (K N : ℕ) (beta : ℝ) (L : ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K
      (dyadicBucket beta L G.weight)
      (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
      x residual)))
    (hM : ((G.largeEdgeOptionSystem K (dyadicBucket beta L G.weight)
      (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)).quantized N
      (G.largeEdgeMass K (dyadicBucket beta L G.weight)
        (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
        x residual)).IsPartialMatching M)
    (hbeta : 0 < beta) (hcover : 1 ≤ dyadicScale beta L)
    (hlower : ∀ e, beta ≤ G.weight e)
    (hr0 : ∀ e, 0 ≤ residual e) (hgamma1 : gamma < 1)
    (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges K N (dyadicBucket beta L G.weight)
        (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
        x residual M).filter (G.Inc v), G.weight e) ≤
      2 * G.weightedResidualStar residual v / (1 - gamma) +
        2 * (1 + (t : ℝ)) * dyadicScale beta L := by
  have hbase := G.selectedExtraEdges_starWeight_le_dyadic
    K N beta L x residual gamma t M hM hbeta hcover hlower hr0 hgamma1 v
  have hsum := sum_dyadicUpper_le_two_mul_top hbeta.le L
  rw [sum_dyadicUpper_eq] at hsum
  exact hbase.trans (add_le_add le_rfl (by
    have ht : 0 ≤ 1 + (t : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hsum ht
    nlinarith))

/-- If the chosen top scale is below two, the entire reserve is at most
`4(1+t)`. -/
theorem selectedExtraEdges_starWeight_le_dyadic_fourReserve
    (K N : ℕ) (beta : ℝ) (L : ℕ)
    (x : G.E → Color → Fin K → Fin K → ℝ) (residual : G.E → ℝ)
    (gamma : ℝ) (t : ℕ)
    (M : Finset (QuantizedCopy N (G.largeEdgeMass K
      (dyadicBucket beta L G.weight)
      (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
      x residual)))
    (hM : ((G.largeEdgeOptionSystem K (dyadicBucket beta L G.weight)
      (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)).quantized N
      (G.largeEdgeMass K (dyadicBucket beta L G.weight)
        (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
        x residual)).IsPartialMatching M)
    (hbeta : 0 < beta) (hcover : 1 ≤ dyadicScale beta L)
    (htop : dyadicScale beta L ≤ 2)
    (hlower : ∀ e, beta ≤ G.weight e)
    (hr0 : ∀ e, 0 ≤ residual e) (hgamma1 : gamma < 1)
    (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges K N (dyadicBucket beta L G.weight)
        (G.graphExtraSlotCount (dyadicBucket beta L G.weight) residual gamma t)
        x residual M).filter (G.Inc v), G.weight e) ≤
      2 * G.weightedResidualStar residual v / (1 - gamma) +
        4 * (1 + (t : ℝ)) := by
  have hbase := G.selectedExtraEdges_starWeight_le_dyadic_top
    K N beta L x residual gamma t M hM hbeta hcover hlower hr0 hgamma1 v
  have ht : 0 ≤ 1 + (t : ℝ) := by positivity
  exact hbase.trans (add_le_add le_rfl (by nlinarith))

/-! ## The concrete profile residual -/

universe w₂

variable {Class : Type w₂} [Fintype Class] [DecidableEq Class]
variable {s beta q r : ℝ} {hbetaProfile : 0 < beta} {hr : 0 < r}
variable (proposal : G.E → Color → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s beta q r hbetaProfile hr)

/-- The same dyadic estimate with the residual and ordinary option masses
from the concrete profile construction substituted in. -/
theorem selectedProfileExtraEdges_starWeight_le_dyadic_fourReserve
    (L N : ℕ) (gamma : ℝ) (t : ℕ)
    (M : Finset (QuantizedCopy N
      (G.profileLargeEdgeMass proposal R (dyadicBucket beta L G.weight)
        gamma t)))
    (hM : ((G.profileLargeEdgeOptionSystem proposal
      (dyadicBucket beta L G.weight) gamma t).quantized N
      (G.profileLargeEdgeMass proposal R (dyadicBucket beta L G.weight)
        gamma t)).IsPartialMatching M)
    (hcover : 1 ≤ dyadicScale beta L)
    (htop : dyadicScale beta L ≤ 2)
    (hlower : ∀ e, beta ≤ G.weight e)
    (hretained : ∀ e,
      (∑ c, G.profileRetainedMass s beta proposal e c) ≤ 1)
    (hgamma1 : gamma < 1) (v : G.V) :
    (∑ e ∈ (G.selectedExtraEdges (explicitLargeSlotBound beta q r) N
        (dyadicBucket beta L G.weight)
        (G.graphExtraSlotCount (dyadicBucket beta L G.weight)
          (G.profileResidual s beta proposal) gamma t)
        (G.profileOrdinaryMass proposal R)
        (G.profileResidual s beta proposal) M).filter (G.Inc v),
          G.weight e) ≤
      2 * G.weightedResidualStar (G.profileResidual s beta proposal) v /
          (1 - gamma) +
        4 * (1 + (t : ℝ)) := by
  apply G.selectedExtraEdges_starWeight_le_dyadic_fourReserve
    (explicitLargeSlotBound beta q r) N beta L
    (G.profileOrdinaryMass proposal R) (G.profileResidual s beta proposal)
    gamma t M hM hbetaProfile hcover htop hlower
    (G.profileResidual_nonneg proposal hretained) hgamma1 v

end WeightedSimpleGraph

end

end WeightedEdgeColoring
