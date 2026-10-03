import WeightedEdgeColoring.ExtendedProfileSelectedCyclicQuantizedBridge
import WeightedEdgeColoring.DyadicLargeEdgeOptions

/-!
# Selected normalized profiles with local dyadic extra options

This is the quantitative interface consumed by the variable-slack isolated
iteration.  Ordinary rows are unchanged.  Local dyadic coupling supplies
the extra slot cap automatically and replaces the Cartesian floor loss by
the maximum of the two local counts.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N reserve : ℕ}
variable {s β q r gamma : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

theorem selectedBlockDyadic_quantizedOrdinarySlotDegree_lt
    (hn : 0 < B * k) (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r) (hN : 0 < N)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (D : ℝ)
    (hcapacity : ∀ row : G.ExtendedProfileLargeRow
        (n := B * k) (β := β) (q := q) (r := r),
      G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl row) /
          extendedProfileCandidateCapacityScale rho s omega β q r <
        ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) + D)
    (slot : OrdinarySlot G.V (Fin (B * k))
      (explicitLargeSlotBound β q r)) :
    ((((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (Class := Class)
        (explicitLargeSlotBound β q r) bucket gamma reserve
        (G.selectedBlockResidualOptionMass R0 rho omega choice)).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))).slotDegree
          (Sum.inl slot) : ℕ) : ℝ) <
      (N : ℝ) *
        (rho / extendedProfileSmoothingKappa omega β q r +
          extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) * D) := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho.le choice
  have hdegree := G.dyadicLargeEdge_quantized_slotDegree_inl_le
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) hx0 N slot
  have hload := G.selectedBlockNormalizedLargeSlotLoad_lt_ratio_add R0
    hn hs hspos hq hr0 hleft omega homega0 homega1 rho hrho choice D
    hcapacity (slot.vertex, slot.color, slot.place)
  exact hdegree.trans_lt (mul_lt_mul_of_pos_left hload (by exact_mod_cast hN))

theorem selectedBlockDyadic_quantizedExtraSlotDegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hreserve : 0 < reserve)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (slot : ExtraSlot G.V Class
      (G.graphDyadicExtraSlotCount bucket
        (G.selectedBlockResidualOptionMass R0 rho omega choice)
        gamma reserve)) :
    ((((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))).slotDegree
          (Sum.inr slot) : ℕ) : ℝ) ≤ (1 - gamma) * N := by
  exact G.dyadicLargeEdge_quantized_slotDegree_inr_le
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice)
    hreserve hgamma0 hgamma1 N slot

theorem selectedBlockDyadic_quantizedOrdinaryJobSlotCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (e : G.E)
    (slot : OrdinarySlot G.V (Fin (B * k))
      (explicitLargeSlotBound β q r)) :
    (((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))).jobSlotCodegree e
          (Sum.inl slot) : ℝ) ≤
      (N : ℝ) * ((explicitLargeSlotBound β q r : ℝ) *
        extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ)) := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho choice
  have hbase := G.dyadicLargeEdge_quantized_jobSlotCodegree_inl_le
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) hx0 N e slot
  have hmass := G.n_mul_sum_selectedBlockNormalizedLargeOptionMass_color_le
    R0 hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice e slot.color
  have hnR : (0 : ℝ) < (B * k : ℕ) := by exact_mod_cast hn
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (le_div_iff₀ hnR).2 (by
    convert hmass using 1 <;> push_cast <;> ring)

theorem selectedBlockDyadic_quantizedExtraJobSlotCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hreserve : 0 < reserve) (e : G.E)
    (slot : ExtraSlot G.V Class
      (G.graphDyadicExtraSlotCount bucket
        (G.selectedBlockResidualOptionMass R0 rho omega choice)
        gamma reserve)) :
    (((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))).jobSlotCodegree e
          (Sum.inr slot) : ℝ) ≤ (N : ℝ) / reserve := by
  have hres0 := G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice
  have hres1 : ∀ f,
      G.selectedBlockResidualOptionMass R0 rho omega choice f ≤ 1 := by
    intro f
    unfold selectedBlockResidualOptionMass
    exact sub_le_self _ (le_min zero_le_one
      (G.selectedBlockAllOptionMass_nonneg R0 hn hs hq hr0 hleft
        homega0 homega1 hrho choice f))
  exact G.dyadicLargeEdge_quantized_jobSlotCodegree_inr_le
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    hres0 hres1 hreserve N e slot

theorem selectedBlockDyadic_quantizedSlotPairCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (hreserve : 0 < reserve)
    (hordinary :
      extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ) ≤ 1 / (reserve : ℝ))
    {left right : G.DyadicLargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
      reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)}
    (hne : left ≠ right) :
    ((((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)).quantized N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice))).slotPairCodegree
          left right : ℕ) : ℝ) ≤ (N : ℝ) / reserve := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho choice
  have hx : ∀ e c i j,
      G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice e c i j ≤
        1 / (reserve : ℝ) := by
    intro e c i j
    exact (G.selectedBlockNormalizedLargeOptionMass_le_scale_div R0 hn hs hq
      hr0 hleft omega homega0 homega1 rho hrho choice e c i j).trans hordinary
  have hres0 := G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice
  have hres1 : ∀ e,
      G.selectedBlockResidualOptionMass R0 rho omega choice e ≤ 1 := by
    intro e
    unfold selectedBlockResidualOptionMass
    exact sub_le_self _ (le_min zero_le_one
      (G.selectedBlockAllOptionMass_nonneg R0 hn hs hq hr0 hleft
        homega0 homega1 hrho choice e))
  exact G.dyadicLargeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    hx0 hx hres0 hres1 hreserve N hne

theorem selectedBlockDyadic_quantizedJobDegree_lower_nat
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (C : ℕ) (hCN : C ≤ N)
    (hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.graphDyadicExtraSlotCount bucket
            (G.selectedBlockResidualOptionMass R0 rho omega choice)
            gamma reserve) e ≤ C)
    (e : G.E) (heLarge : β ≤ G.weight e) :
    N - C ≤
      (G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)).quantizedJobDegree N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)) e := by
  have hbase := G.dyadicLargeEdge_quantizedJobDegree_lower
    (explicitLargeSlotBound β q r) bucket gamma reserve
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice) N e
  have hmass := G.sum_selectedBlockNormalizedLarge_add_residual_of_large R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e heLarge
  rw [hmass, mul_one] at hbase
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul] at hbase
  have hchoiceR :
      (((B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        DivisibleLocalExtraChoice.supportCount G.fst G.snd bucket
          (G.graphDyadicExtraSlotCount bucket
            (G.selectedBlockResidualOptionMass R0 rho omega choice)
            gamma reserve) e : ℕ) : ℝ) ≤ C := by
    exact_mod_cast hchoices e
  push_cast at hchoiceR
  have hreal : ((N - C : ℕ) : ℝ) ≤
      ((G.dyadicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)).quantizedJobDegree N
      (G.dyadicLargeEdgeMass (explicitLargeSlotBound β q r) bucket gamma
        reserve (G.selectedBlockResidualOptionMass R0 rho omega choice)
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)) e : ℝ) := by
    rw [Nat.cast_sub hCN]
    exact (sub_le_sub_left hchoiceR N).trans hbase
  exact_mod_cast hreal

end WeightedSimpleGraph

end

end WeightedEdgeColoring
