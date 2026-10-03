import WeightedEdgeColoring.GraphExtraSlotBudget
import WeightedEdgeColoring.LargeEdgeOptions
import WeightedEdgeColoring.ProfileOptionBridge

namespace WeightedEdgeColoring

/-!
# Numerical bounds for graph-indexed large-edge options

This file inserts the graph-indexed extra-slot count into the combined
ordinary/extra large-edge option family.  It records the three numerical
bounds used by the matching step: extra-slot degree slack, small extra
job--slot codegree, and small combined pair codegree.
-/

noncomputable section

universe u w₁ w₂

namespace WeightedSimpleGraph

variable (G : WeightedSimpleGraph.{u})
variable {Color : Type w₁} {Class : Type w₂}
  [Fintype Color] [DecidableEq Color]
  [Fintype Class] [DecidableEq Class]

/-- In the combined family, every graph-indexed extra slot keeps the fixed
`gamma` fraction of degree slack. -/
theorem largeEdge_graphExtra_slotDegree_inr_le
    (K : ℕ) (bucket : G.E → Class) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hr : ∀ e, 0 ≤ residual e)
    (gamma : ℝ) (t N : ℕ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (ht : 0 < t)
    (s : ExtraSlot G.V Class
      (G.graphExtraSlotCount bucket residual gamma t)) :
    ((((G.largeEdgeOptionSystem K bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (G.largeEdgeMass K bucket
        (G.graphExtraSlotCount bucket residual gamma t) x residual)).slotDegree
          (Sum.inr s) : ℕ) : ℝ) ≤
      (1 - gamma) * N := by
  unfold largeEdgeOptionSystem largeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_slotDegree_inr]
  exact G.quantized_graphExtraSlotDegree_le bucket residual hr gamma t N
    hgamma0 hgamma1 ht s

/-- In the combined family, every edge--extra-slot codegree is at most
`N/t`. -/
theorem largeEdge_graphExtra_jobSlotCodegree_inr_le
    (K : ℕ) (bucket : G.E → Class) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t) (N : ℕ)
    (e : G.E)
    (s : ExtraSlot G.V Class
      (G.graphExtraSlotCount bucket residual gamma t)) :
    (((G.largeEdgeOptionSystem K bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (G.largeEdgeMass K bucket
        (G.graphExtraSlotCount bucket residual gamma t) x residual)).jobSlotCodegree
          e (Sum.inr s) : ℝ) ≤
      (N : ℝ) * (1 / (t : ℝ)) := by
  unfold largeEdgeOptionSystem largeEdgeMass
  rw [RankThreeOptionSystem.separatedSum_quantized_jobSlotCodegree_inr]
  exact G.quantized_graphExtraJobSlotCodegree_le bucket residual hr0 hr1
    gamma ht N e s

/-- If every ordinary base option also has mass at most `1/t^2`, then every
pair of distinct slots in the combined graph-indexed family has copied
codegree at most `N/t^2`. -/
theorem largeEdge_graphExtra_slotPairCodegree_le
    (K : ℕ) (bucket : G.E → Class) (residual : G.E → ℝ)
    (x : G.E → Color → Fin K → Fin K → ℝ)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (hx0 : ∀ e c i j, 0 ≤ x e c i j)
    (hxsmall : ∀ e c i j, x e c i j ≤ 1 / (t : ℝ) ^ 2)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (N : ℕ)
    {s r : G.LargeEdgeSlot (Color := Color) K
      (G.graphExtraSlotCount bucket residual gamma t)} (hsr : s ≠ r) :
    ((((G.largeEdgeOptionSystem K bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (G.largeEdgeMass K bucket
        (G.graphExtraSlotCount bucket residual gamma t) x residual)).slotPairCodegree
          s r : ℕ) : ℝ) ≤
      (N : ℝ) * (1 / (t : ℝ) ^ 2) := by
  apply G.largeEdge_quantized_slotPairCodegree_le K bucket
    (G.graphExtraSlotCount bucket residual gamma t) x residual
    (1 / (t : ℝ) ^ 2)
  · positivity
  · exact hx0
  · exact hxsmall
  · exact hr0
  · intro e
    exact residual_div_mul_counts_le_inv_reserve_sq (residual e)
      (hr1 e) ht
      (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
        (G.fst e) (bucket e))
      (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
        (G.snd e) (bucket e))
  · exact hsr

/-- Fully unconditional pair-codegree bound for the profile-derived ordinary
array.  The extra-slot grid contributes `1/t^2`; the aggregated ordinary
profiles contribute `s * max q 1`.  The latter term need not vanish because
one rounded profile is allowed to have probability one. -/
theorem largeEdge_profile_graphExtra_slotPairCodegree_parameter_le
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (proposal : G.E → Color → ℝ)
    (R : ∀ v c, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (N : ℕ)
    {a b : G.LargeEdgeSlot (Color := Color)
      (explicitLargeSlotBound β q r)
      (G.graphExtraSlotCount bucket residual gamma t)} (hab : a ≠ b) :
    ((((G.largeEdgeOptionSystem (explicitLargeSlotBound β q r) bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket
        (G.graphExtraSlotCount bucket residual gamma t)
        (G.profileOrdinaryMass proposal R) residual)).slotPairCodegree
          a b : ℕ) : ℝ) ≤
      (N : ℝ) * max (s * max q 1) (1 / (t : ℝ) ^ 2) := by
  apply G.largeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β q r) bucket
    (G.graphExtraSlotCount bucket residual gamma t)
    (G.profileOrdinaryMass proposal R) residual
    (max (s * max q 1) (1 / (t : ℝ) ^ 2))
  · exact (mul_nonneg hs (zero_le_one.trans (le_max_right q 1))).trans
      (le_max_left _ _)
  · intro e c i j
    exact G.profileOrdinaryMass_nonneg proposal R hs hp e c i j
  · intro e c i j
    exact (G.profileOrdinaryMass_le_parameter proposal R hs hp e c i j).trans
      (le_max_left _ _)
  · exact hr0
  · intro e
    exact (residual_div_mul_counts_le_inv_reserve_sq (residual e)
      (hr1 e) ht
      (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
        (G.fst e) (bucket e))
      (G.graphExtraSlotCount_ge_reserve bucket residual gamma t
        (G.snd e) (bucket e))).trans (le_max_right _ _)
  · exact hab

/-- Insert the profile-derived ordinary array into the graph-indexed pair
codegree theorem.  The additional numerical hypothesis is exactly what the
current bounded-profile interface can supply: its parameter-only pointwise
bound is `s * max q 1`. -/
theorem largeEdge_profile_graphExtra_slotPairCodegree_le
    {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
    (proposal : G.E → Color → ℝ)
    (R : ∀ v c, G.BoundedProfileRealization
      (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (gamma : ℝ) {t : ℕ} (ht : 0 < t)
    (hs : 0 ≤ s) (hp : ∀ e c, 0 ≤ proposal e c)
    (hsmall : s * max q 1 ≤ 1 / (t : ℝ) ^ 2)
    (hr0 : ∀ e, 0 ≤ residual e) (hr1 : ∀ e, residual e ≤ 1)
    (N : ℕ)
    {a b : G.LargeEdgeSlot (Color := Color)
      (explicitLargeSlotBound β q r)
      (G.graphExtraSlotCount bucket residual gamma t)} (hab : a ≠ b) :
    ((((G.largeEdgeOptionSystem (explicitLargeSlotBound β q r) bucket
        (G.graphExtraSlotCount bucket residual gamma t)).quantized N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket
        (G.graphExtraSlotCount bucket residual gamma t)
        (G.profileOrdinaryMass proposal R) residual)).slotPairCodegree
          a b : ℕ) : ℝ) ≤
      (N : ℝ) * (1 / (t : ℝ) ^ 2) := by
  apply G.largeEdge_graphExtra_slotPairCodegree_le
    (explicitLargeSlotBound β q r) bucket residual
    (G.profileOrdinaryMass proposal R) gamma ht
  · intro e c i j
    exact G.profileOrdinaryMass_nonneg proposal R hs hp e c i j
  · intro e c i j
    exact (G.profileOrdinaryMass_le_parameter proposal R hs hp e c i j).trans
      hsmall
  · exact hr0
  · exact hr1
  · exact hab

end WeightedSimpleGraph

end

end WeightedEdgeColoring
