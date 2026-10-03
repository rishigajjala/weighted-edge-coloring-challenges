import WeightedEdgeColoring.ExtendedProfileBlockJointFeasibility
import WeightedEdgeColoring.ProfileLargeEdgeResidualBridge

/-!
# Quantitative bridge from selected profiles to quantized options

The block selector controls `selectedBlockCapacityLoad`, whereas the
rank-three iteration consumes copied slot degrees.  This file records the
direct conversion, including the edgewise clipping step.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u w

variable (G : WeightedSimpleGraph.{u})
variable {Class : Type w} [Fintype Class] [DecidableEq Class]
variable {B k N : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- A selected large capacity row bounds the clipped ordinary fractional
slot load.  This is the exact ratio used to choose the iteration slack. -/
theorem selectedBlockNormalizedLargeSlotLoad_lt_ratio_add
    (hn : 0 < B * k) (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (D : ℝ)
    (hcapacity : ∀ row : G.ExtendedProfileLargeRow
        (n := B * k) (β := β) (q := q) (r := r),
      G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl row) /
          extendedProfileCandidateCapacityScale rho s omega β q r <
        ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) + D)
    (row : G.ExtendedProfileLargeRow
      (n := B * k) (β := β) (q := q) (r := r)) :
    G.selectedBlockNormalizedLargeSlotLoad R0 rho omega choice row <
      rho / extendedProfileSmoothingKappa omega β q r +
        extendedProfileCandidateCapacityScale rho s omega β q r /
          ((B * k : ℕ) : ℝ) * D := by
  let scale := extendedProfileCandidateCapacityScale rho s omega β q r
  let kappa := extendedProfileSmoothingKappa omega β q r
  let n : ℝ := (B * k : ℕ)
  have hnR : 0 < n := by
    dsimp [n]
    exact_mod_cast hn
  have hscale : 0 < scale :=
    extendedProfileCandidateCapacityScale_pos hrho hspos homega0
  have hkappa : 0 < kappa :=
    extendedProfileSmoothingKappa_pos homega0 homega1
  dsimp [scale, kappa, n] at hscale hkappa hnR
  have hraw := hcapacity row
  rw [G.selectedBlockCapacityLoad_large_eq R0 rho omega choice row] at hraw
  have hraw' :
      G.selectedBlockLargeSlotLoad R0 rho omega choice row <
        rho / kappa + scale / n * D := by
    dsimp [scale, kappa, n] at hraw ⊢
    calc
      G.selectedBlockLargeSlotLoad R0 rho omega choice row =
          (((B * k : ℕ) : ℝ) *
            G.selectedBlockLargeSlotLoad R0 rho omega choice row) /
              ((B * k : ℕ) : ℝ) := by field_simp
      _ < (((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) + D) *
            extendedProfileCandidateCapacityScale rho s omega β q r /
              ((B * k : ℕ) : ℝ) := by
          apply div_lt_div_of_pos_right _ hnR
          exact (div_lt_iff₀ hscale).mp hraw
      _ = rho / extendedProfileSmoothingKappa omega β q r +
          extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) * D := by
        field_simp [hscale.ne', hkappa.ne', hnR.ne']
  exact (G.selectedBlockNormalizedLargeSlotLoad_le R0 hn hs hq hr0
    hleft homega0 homega1 hrho.le choice row).trans_lt hraw'

/-- The preceding fractional estimate converts directly to copied ordinary
slot degree. -/
theorem selectedBlock_quantizedOrdinarySlotDegree_lt
    (hn : 0 < B * k) (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hN : 0 < N)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (D : ℝ)
    (hcapacity : ∀ row : G.ExtendedProfileLargeRow
        (n := B * k) (β := β) (q := q) (r := r),
      G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl row) /
          extendedProfileCandidateCapacityScale rho s omega β q r <
        ((B * k : ℕ) : ℝ) * rho /
            (extendedProfileCandidateCapacityScale rho s omega β q r *
              extendedProfileSmoothingKappa omega β q r) + D)
    (slot : OrdinarySlot G.V (Fin (B * k))
      (explicitLargeSlotBound β q r)) :
    ((((G.largeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
        bucket extraCount).quantized N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).slotDegree
          (Sum.inl slot) : ℕ) : ℝ) <
      (N : ℝ) *
        (rho / extendedProfileSmoothingKappa omega β q r +
          extendedProfileCandidateCapacityScale rho s omega β q r /
            ((B * k : ℕ) : ℝ) * D) := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho.le choice
  have hdegree := G.largeEdge_quantized_slotDegree_inl_le
    (explicitLargeSlotBound β q r) bucket extraCount
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice) hx0 N slot
  have hload := G.selectedBlockNormalizedLargeSlotLoad_lt_ratio_add R0
    hn hs hspos hq hr0 hleft omega homega0 homega1 rho hrho choice D
    hcapacity (slot.vertex, slot.color, slot.place)
  exact hdegree.trans_lt (mul_lt_mul_of_pos_left hload (by
    exact_mod_cast hN))

/-! ## Pointwise and codegree bounds -/

/-- A fixed selected color and endpoint place has total raw option mass at
most `scale/n`.  This is the candidate-edge estimate specialized to the
full word decoded from the selected block codes. -/
theorem n_mul_sum_selectedBlockLargeOptionMass_le_scale_left
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i : Fin (explicitLargeSlotBound β q r)) :
    ((B * k : ℕ) : ℝ) *
        (∑ j, G.selectedBlockLargeOptionMass R0 rho omega choice e c i j) ≤
      extendedProfileCandidateCapacityScale rho s omega β q r := by
  let word := G.decodedExtendedProfileBlockSelection R0 choice
  let code : ExtendedProfilePackedWordState (B * k) β q r :=
    FiniteDependentWordPadding.encodePackedWord
      (fun v ↦ G.ExtendedProfileState R0 v) (Color := Fin (B * k))
      (G.extendedProfileStateEncoding R0) (G.snd e) (word (G.snd e))
  let row : G.ExtendedProfileLargeCandidateRow R0
      (n := B * k) (β := β) (q := q) (r := r) :=
    ⟨G.fst e, c, word (G.fst e) c, i⟩
  have h := G.packedExtendedProfileLargeCandidateEdgeUse_le_scale R0
    hn hs hq hr0 hleft homega0 homega1 hrho
      (G.snd e) code e row
  simpa [code, row, word, packedExtendedProfileLargeCandidateEdgeUse,
    selectedBlockLargeOptionMass, decodedExtendedProfileBlockSelection]
    using h

/-- Clipping preserves the preceding oriented bound. -/
theorem n_mul_sum_selectedBlockNormalizedLargeOptionMass_le_scale_left
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i : Fin (explicitLargeSlotBound β q r)) :
    ((B * k : ℕ) : ℝ) *
        (∑ j, G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j) ≤
      extendedProfileCandidateCapacityScale rho s omega β q r := by
  have hsum :
      (∑ j, G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j) ≤
        ∑ j, G.selectedBlockLargeOptionMass R0 rho omega choice e c i j := by
    apply Finset.sum_le_sum
    intro j hj
    exact G.selectedBlockNormalizedLargeOptionMass_le R0 hn hs hq hr0
      hleft homega0 homega1 hrho choice e c i j
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    (G.n_mul_sum_selectedBlockLargeOptionMass_le_scale_left R0 hn hs hq
      hr0 hleft omega homega0 homega1 rho hrho choice e c i)

/-- Consequently one edge/color contributes at most `L*scale/n`, where
`L` is the fixed number of padded places. -/
theorem n_mul_sum_selectedBlockNormalizedLargeOptionMass_color_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k)) :
    ((B * k : ℕ) : ℝ) *
        (∑ i, ∑ j, G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j) ≤
      (explicitLargeSlotBound β q r : ℝ) *
        extendedProfileCandidateCapacityScale rho s omega β q r := by
  rw [Finset.mul_sum]
  calc
    (∑ i, ((B * k : ℕ) : ℝ) *
        ∑ j, G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j) ≤
      ∑ _i : Fin (explicitLargeSlotBound β q r),
        extendedProfileCandidateCapacityScale rho s omega β q r := by
          apply Finset.sum_le_sum
          intro i hi
          exact G.n_mul_sum_selectedBlockNormalizedLargeOptionMass_le_scale_left
            R0 hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice e c i
    _ = (explicitLargeSlotBound β q r : ℝ) *
        extendedProfileCandidateCapacityScale rho s omega β q r := by simp

/-- Copied ordinary job--slot codegrees inherit the preceding
`N/n` bound. -/
theorem selectedBlock_quantizedOrdinaryJobSlotCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (e : G.E)
    (slot : OrdinarySlot G.V (Fin (B * k))
      (explicitLargeSlotBound β q r)) :
    (((G.largeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
        bucket extraCount).quantized N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).jobSlotCodegree
          e (Sum.inl slot) : ℝ) ≤
      (N : ℝ) *
        ((explicitLargeSlotBound β q r : ℝ) *
          extendedProfileCandidateCapacityScale rho s omega β q r /
            (B * k : ℕ)) := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho choice
  have hbase := G.largeEdge_quantized_jobSlotCodegree_inl_le
    (explicitLargeSlotBound β q r) bucket extraCount
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice) hx0 N e slot
  have hmass := G.n_mul_sum_selectedBlockNormalizedLargeOptionMass_color_le
    R0 hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice e slot.color
  have hnR : (0 : ℝ) < (B * k : ℕ) := by exact_mod_cast hn
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (le_div_iff₀ hnR).2 (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmass)

/-- Pointwise ordinary mass has the sharper `scale/n` bound needed for
slot-pair codegrees. -/
theorem selectedBlockNormalizedLargeOptionMass_le_scale_div
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (e : G.E) (c : Fin (B * k))
    (i j : Fin (explicitLargeSlotBound β q r)) :
    G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice e c i j ≤
      extendedProfileCandidateCapacityScale rho s omega β q r /
        (B * k : ℕ) := by
  have hx0 := G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq
    hr0 hleft homega0 homega1 hrho choice e c i j
  have hsingle :
      G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice e c i j ≤
        ∑ j', G.selectedBlockNormalizedLargeOptionMass
          R0 rho omega choice e c i j' := by
    exact Finset.single_le_sum
      (fun j' hj' ↦ G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs
        hq hr0 hleft homega0 homega1 hrho choice e c i j')
      (Finset.mem_univ j)
  have hrow := G.n_mul_sum_selectedBlockNormalizedLargeOptionMass_le_scale_left
    R0 hn hs hq hr0 hleft omega homega0 homega1 rho hrho choice e c i
  have hnR : (0 : ℝ) < (B * k : ℕ) := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).2
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_left hsingle hnR.le).trans hrow

/-- Combined slot-pair codegree bound.  The second displayed hypothesis is
the corresponding bound for the graph-indexed extra grid. -/
theorem selectedBlock_quantizedSlotPairCodegree_le
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (tau : ℝ) (htau0 : 0 ≤ tau)
    (hordinary :
      extendedProfileCandidateCapacityScale rho s omega β q r /
          (B * k : ℕ) ≤ tau)
    (hresidual0 : ∀ e,
      0 ≤ G.selectedBlockResidualOptionMass R0 rho omega choice e)
    (hextra : ∀ e,
      G.selectedBlockResidualOptionMass R0 rho omega choice e /
          ((extraCount (G.fst e) (bucket e) : ℕ) *
            extraCount (G.snd e) (bucket e) : ℕ) ≤ tau)
    {left right : G.LargeEdgeSlot
      (Color := Fin (B * k)) (explicitLargeSlotBound β q r) extraCount}
    (hne : left ≠ right) :
    ((((G.largeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
        bucket extraCount).quantized N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice))).slotPairCodegree
          left right : ℕ) : ℝ) ≤ (N : ℝ) * tau := by
  apply G.largeEdge_quantized_slotPairCodegree_le
    (explicitLargeSlotBound β q r) bucket extraCount
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    tau htau0
  · exact G.selectedBlockNormalizedLargeOptionMass_nonneg R0 hn hs hq hr0
      hleft homega0 homega1 hrho choice
  · intro e c i j
    exact (G.selectedBlockNormalizedLargeOptionMass_le_scale_div R0 hn hs hq
      hr0 hleft omega homega0 homega1 rho hrho choice e c i j).trans hordinary
  · exact hresidual0
  · exact hextra
  · exact hne

/-- On a large edge, normalized ordinary mass plus its private residual is
exactly one.  Thus the copied job loses only the number of base choices. -/
theorem selectedBlock_quantizedJobDegree_lower_nat
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r)
    (bucket : G.E → Class) (extraCount : G.V → Class → ℕ)
    (hleftCount : ∀ e, 0 < extraCount (G.fst e) (bucket e))
    (hrightCount : ∀ e, 0 < extraCount (G.snd e) (bucket e))
    (C : ℕ) (hCN : C ≤ N)
    (hchoices : ∀ e,
      (B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        extraCount (G.fst e) (bucket e) *
          extraCount (G.snd e) (bucket e) ≤ C)
    (e : G.E) (heLarge : β ≤ G.weight e) :
    N - C ≤
      (G.largeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
        bucket extraCount).quantizedJobDegree N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice)) e := by
  have hbase := G.largeEdge_quantizedJobDegree_lower
    (explicitLargeSlotBound β q r) bucket extraCount
    (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
    (G.selectedBlockResidualOptionMass R0 rho omega choice)
    hleftCount hrightCount N e
  have hmass := G.sum_selectedBlockNormalizedLarge_add_residual_of_large R0
    hn hs hq hr0 hleft homega0 homega1 hrho choice e heLarge
  rw [hmass, mul_one] at hbase
  have hchoiceR :
      (((B * k) * explicitLargeSlotBound β q r *
          explicitLargeSlotBound β q r +
        extraCount (G.fst e) (bucket e) *
          extraCount (G.snd e) (bucket e) : ℕ) : ℝ) ≤ C := by
    exact_mod_cast hchoices e
  have hreal : ((N - C : ℕ) : ℝ) ≤
      ((G.largeEdgeOptionSystem
        (Color := Fin (B * k)) (explicitLargeSlotBound β q r)
        bucket extraCount).quantizedJobDegree N
      (G.largeEdgeMass (explicitLargeSlotBound β q r) bucket extraCount
        (G.selectedBlockNormalizedLargeOptionMass R0 rho omega choice)
        (G.selectedBlockResidualOptionMass R0 rho omega choice)) e : ℝ) := by
    rw [Nat.cast_sub hCN]
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul] at hbase hchoiceR
    exact (sub_le_sub_left hchoiceR N).trans hbase
  exact_mod_cast hreal

/-- Rounding loss in the copied job fibres can be absorbed into the same
slot/job gap.  This is the elementary inequality used with `d=N-C`. -/
theorem quantized_initial_gap_of_fractional
    {gamma mu : ℝ} {N C S : ℕ}
    (hgamma0 : 0 ≤ gamma) (hgammaHalf : gamma ≤ 1 / 2)
    (hmu : mu ≤ 1 - 2 * gamma)
    (hCN : C ≤ N)
    (hrounding : (C : ℝ) ≤ gamma * N / 2)
    (hslot : (S : ℝ) ≤ (N : ℝ) * mu) :
    (S : ℝ) ≤ (1 - gamma) * (N - C : ℕ) := by
  rw [Nat.cast_sub hCN]
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hleft := mul_le_mul_of_nonneg_left hmu hN0
  nlinarith [mul_nonneg hgamma0 (sub_nonneg.mpr hgammaHalf)]

end WeightedSimpleGraph

end

end WeightedEdgeColoring
