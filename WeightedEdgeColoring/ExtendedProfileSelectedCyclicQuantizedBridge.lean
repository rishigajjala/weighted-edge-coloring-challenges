import WeightedEdgeColoring.ExtendedProfileSelectedQuantizedBridge
import WeightedEdgeColoring.CyclicLargeEdgeOptions

/-!
# Selected normalized profiles with coupled extra options

This file replaces only the Cartesian residual grid in the selected-profile
bridge.  The ordinary array is unchanged.  The resulting base-option loss is
`palette * places^2 + t`, and every extra job--slot or slot-pair codegree is
at most `N/t`.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N t : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- A residual bounded by one has at most the weighted star size divided by
the common lower edge weight in every class.  No property of `bucket` is
needed. -/
theorem classResidual_mul_lowerWeight_le_starWeight
    (bucket : G.E → Class) (residual : G.E → ℝ)
    (hres0 : ∀ e, 0 ≤ residual e) (hres1 : ∀ e, residual e ≤ 1)
    {b : ℝ} (hb0 : 0 ≤ b) (hlower : ∀ e, b ≤ G.weight e)
    (v : G.V) (h : Class) :
    G.classResidual bucket residual v h * b ≤ G.starWeight v := by
  unfold classResidual
  rw [Finset.sum_mul]
  calc
    (∑ e,
      ((if (G.fst e, bucket e) = (v, h) then residual e else 0) +
        (if (G.snd e, bucket e) = (v, h) then residual e else 0)) * b) ≤
      ∑ e, if G.Inc v e then G.weight e else 0 := by
        apply Finset.sum_le_sum
        intro e _
        by_cases hf : (G.fst e, bucket e) = (v, h)
        · have hfv : G.fst e = v := congrArg Prod.fst hf
          have hs : (G.snd e, bucket e) ≠ (v, h) := by
            intro heq
            exact G.noLoop e (hfv.trans (congrArg Prod.fst heq).symm)
          have hinc : G.Inc v e := Or.inl hfv
          rw [if_pos hf, if_neg hs, add_zero, if_pos hinc]
          exact (mul_le_mul_of_nonneg_right (hres1 e) hb0).trans
            (by simpa using hlower e)
        · by_cases hs : (G.snd e, bucket e) = (v, h)
          · have hsv : G.snd e = v := congrArg Prod.fst hs
            have hinc : G.Inc v e := Or.inr hsv
            rw [if_neg hf, if_pos hs, zero_add, if_pos hinc]
            exact (mul_le_mul_of_nonneg_right (hres1 e) hb0).trans
              (by simpa using hlower e)
          · by_cases hinc : G.Inc v e
            · simp [hf, hs, hinc, G.weight_nonneg]
            · simp [hf, hs, hinc]
    _ = G.starWeight v := by
      unfold starWeight
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        ((Finset.univ : Finset G.E).filter (G.Inc v)) (by simp)
        G.weight

/-- Under an `n`-bin local packing, choosing `t` with
`n/b ≤ (1-gamma)t` supplies all cyclic extra-slot caps at once. -/
theorem selectedBlockResidual_classCap_of_localPacking
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) {palette : ℕ}
    (hpack : G.LocallyPacksInto palette)
    {b gamma : ℝ} (hb : 0 < b) (hlower : ∀ e, b ≤ G.weight e)
    (hscale : (palette : ℝ) / b ≤ (1 - gamma) * t) :
    ∀ v h,
      G.classResidual bucket
          (G.selectedBlockResidualOptionMass R0 rho omega choice) v h ≤
        (1 - gamma) * t := by
  have hres0 := G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice
  have hres1 : ∀ e,
      G.selectedBlockResidualOptionMass R0 rho omega choice e ≤ 1 := by
    intro e
    unfold selectedBlockResidualOptionMass
    exact sub_le_self _ (le_min zero_le_one
      (G.selectedBlockAllOptionMass_nonneg R0 hn hs hq hr0 hleft
        homega0 homega1 hrho choice e))
  intro v h
  have hweighted := G.classResidual_mul_lowerWeight_le_starWeight
    bucket (G.selectedBlockResidualOptionMass R0 rho omega choice)
    hres0 hres1 hb.le hlower v h
  have hstar := G.starWeight_le_of_locallyPacksInto hpack v
  have hdiv : G.classResidual bucket
      (G.selectedBlockResidualOptionMass R0 rho omega choice) v h ≤
      (palette : ℝ) / b := by
    rw [le_div_iff₀ hb]
    exact hweighted.trans hstar
  exact hdiv.trans hscale

/-- Ordinary selected-profile slot degrees are unchanged when the cyclic
extra family replaces the Cartesian one. -/
theorem selectedBlockCyclic_quantizedOrdinarySlotDegree_lt
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
    ((((G.cyclicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (Class := Class)
        (explicitLargeSlotBound β q r) t bucket).quantized N
      (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).slotDegree
          (Sum.inl slot) : ℕ) : ℝ) <
      (N : ℝ) *
        (rho / extendedProfileSmoothingKappa omega β q r +
          extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) * D) := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho.le choice
  have hdegree := G.cyclicLargeEdge_quantized_slotDegree_inl_le
    (explicitLargeSlotBound β q r) t bucket
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice) hx0 N slot
  have hload := G.selectedBlockNormalizedLargeSlotLoad_lt_ratio_add R0
    hn hs hspos hq hr0 hleft omega homega0 homega1 rho hrho choice D
    hcapacity (slot.vertex, slot.color, slot.place)
  exact hdegree.trans_lt (mul_lt_mul_of_pos_left hload (by exact_mod_cast hN))

/-- A residual-star cap implies the
cyclic extra-slot degree bound. -/
theorem selectedBlockCyclic_quantizedExtraSlotDegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) {gamma : ℝ} (ht : 0 < t)
    (hclass : ∀ v h,
      G.classResidual bucket
          (G.selectedBlockResidualOptionMass R0 rho omega choice) v h ≤
        (1 - gamma) * t)
    (slot : CyclicExtraSlot G.V Class t) :
    ((((G.cyclicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) t bucket).quantized N
      (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).slotDegree
          (Sum.inr slot) : ℕ) : ℝ) ≤ (1 - gamma) * N := by
  have hres0 := G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice
  exact G.cyclicLargeEdge_quantized_slotDegree_inr_le
    (explicitLargeSlotBound β q r) t bucket
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    hres0 ht hclass N slot

/-- Copied ordinary job--slot codegrees retain the selected-profile `N/n`
bound. -/
theorem selectedBlockCyclic_quantizedOrdinaryJobSlotCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (e : G.E)
    (slot : OrdinarySlot G.V (Fin (B * k))
      (explicitLargeSlotBound β q r)) :
    (((G.cyclicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (Class := Class)
        (explicitLargeSlotBound β q r) t bucket).quantized N
      (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).jobSlotCodegree
          e (Sum.inl slot) : ℝ) ≤
      (N : ℝ) *
        ((explicitLargeSlotBound β q r : ℝ) *
          extendedProfileCandidateCapacityScale rho s omega β q r /
            (B * k : ℕ)) := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho choice
  have hbase := G.cyclicLargeEdge_quantized_jobSlotCodegree_inl_le
    (explicitLargeSlotBound β q r) t bucket
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice) hx0 N e slot
  have hmass := G.n_mul_sum_selectedBlockNormalizedLargeOptionMass_color_le
    R0 hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice e slot.color
  have hnR : (0 : ℝ) < (B * k : ℕ) := by exact_mod_cast hn
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (le_div_iff₀ hnR).2 (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmass)

/-- The cyclic residual part has both job--slot and pair scale `N/t`. -/
theorem selectedBlockCyclic_quantizedExtraJobSlotCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (ht : 0 < t) (e : G.E)
    (slot : CyclicExtraSlot G.V Class t) :
    (((G.cyclicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) t bucket).quantized N
      (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).jobSlotCodegree
          e (Sum.inr slot) : ℝ) ≤ (N : ℝ) / t := by
  have hres0 := G.selectedBlockResidualOptionMass_nonneg R0 rho omega choice
  have hres1 : ∀ e,
      G.selectedBlockResidualOptionMass R0 rho omega choice e ≤ 1 := by
    intro f
    unfold selectedBlockResidualOptionMass
    exact sub_le_self _ (le_min zero_le_one
      (G.selectedBlockAllOptionMass_nonneg R0 hn hs hq hr0 hleft
        homega0 homega1 hrho choice f))
  exact G.cyclicLargeEdge_quantized_jobSlotCodegree_inr_le
    (explicitLargeSlotBound β q r) t bucket
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    hres0 hres1 ht N e slot

/-- Full pair-codegree bound for selected ordinary plus cyclic residual
options. -/
theorem selectedBlockCyclic_quantizedSlotPairCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (ht : 0 < t)
    (hordinary :
      extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ) ≤ 1 / (t : ℝ))
    {left right : G.CyclicLargeEdgeSlot
      (Color := Fin (B * k)) (Class := Class)
      (explicitLargeSlotBound β q r) t}
    (hne : left ≠ right) :
    ((((G.cyclicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r) t bucket).quantized N
      (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).slotPairCodegree
          left right : ℕ) : ℝ) ≤ (N : ℝ) / t := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho choice
  have hx : ∀ e c i j,
      G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice e c i j ≤
        1 / (t : ℝ) := by
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
  exact G.cyclicLargeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β q r) t bucket
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    hx0 hx hres0 hres1 ht N hne

/-- Exact job mass and the linear cyclic fibre give the desired floor-loss
bound. -/
theorem selectedBlockCyclic_quantizedJobDegree_lower_nat
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (ht : 0 < t)
    (C : ℕ) (hCN : C ≤ N)
    (hchoices :
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r + t ≤ C)
    (e : G.E) (heLarge : β ≤ G.weight e) :
    N - C ≤
      (G.cyclicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (Class := Class)
        (explicitLargeSlotBound β q r) t bucket).quantizedJobDegree N
      (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice)) e := by
  have hbase := G.cyclicLargeEdge_quantizedJobDegree_lower
    (explicitLargeSlotBound β q r) t bucket
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice) ht N e
  have hmass := G.sum_selectedBlockNormalizedLarge_add_residual_of_large R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e heLarge
  rw [hmass, mul_one] at hbase
  have hchoiceR :
      (((B * k) * explicitLargeSlotBound β q r *
        explicitLargeSlotBound β q r + t : ℕ) : ℝ) ≤ C := by
    exact_mod_cast hchoices
  have hreal : ((N - C : ℕ) : ℝ) ≤
      ((G.cyclicLargeEdgeOptionSystem
        (Color := Fin (B * k)) (Class := Class)
        (explicitLargeSlotBound β q r) t bucket).quantizedJobDegree N
      (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice)) e : ℝ) := by
    rw [Nat.cast_sub hCN]
    have hbase' :
        (N : ℝ) -
            (((B * k) * explicitLargeSlotBound β q r *
              explicitLargeSlotBound β q r + t : ℕ) : ℝ) ≤
          ((G.cyclicLargeEdgeOptionSystem
            (Color := Fin (B * k)) (Class := Class)
            (explicitLargeSlotBound β q r) t bucket).quantizedJobDegree N
          (G.cyclicLargeEdgeMass (explicitLargeSlotBound β q r) t
            (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
            (G.selectedBlockResidualOptionMass R0 rho omega choice)) e : ℝ) := by
      convert hbase using 1 <;> norm_num [Fintype.card_fin] <;> ring
    exact (sub_le_sub_left hchoiceR (N : ℝ)).trans hbase'
  exact_mod_cast hreal

end WeightedSimpleGraph

end

end WeightedEdgeColoring
