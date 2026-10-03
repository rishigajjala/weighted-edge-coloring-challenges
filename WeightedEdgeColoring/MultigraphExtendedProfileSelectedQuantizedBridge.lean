import WeightedEdgeColoring.MultigraphExtendedProfileSelectedNormalizedOptions
import WeightedEdgeColoring.MultigraphExtendedProfileBlockCandidateCapacityRows

/-!
# Quantitative bridge from selected profiles to quantized options

The block selector controls `selectedBlockCapacityLoad`, whereas the
rank-three iteration consumes copied slot degrees.  This file records the
direct conversion, including the edgewise clipping step.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u w

variable (G : WeightedMultigraph.{u})
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

end WeightedMultigraph

end

end WeightedEdgeColoring
