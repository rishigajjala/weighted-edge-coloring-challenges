import WeightedEdgeColoring.ExtendedProfileSelectedDyadicSelection

/-!
# Canonical padding data for the selected-profile block selector

The packing selector asks for an auxiliary probability law on the common
padded state space and an integer mean bound.  Both choices are canonical:
use the uniform law and one plus the ceiling of the displayed mean.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

/-- Uniform padding law on the common packed block state. -/
def extendedProfileCanonicalDummyProb
    (k : ℕ) (beta q r : ℝ)
    (_a : WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r) : ℝ :=
  1 / Fintype.card
    (WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r)

theorem extendedProfilePackedBlockState_nonempty
    (k : ℕ) (beta q r : ℝ) :
    Nonempty
      (WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r) := by
  unfold WeightedSimpleGraph.ExtendedProfilePackedBlockState
  apply Fin.pos_iff_nonempty.mp
  apply Fintype.card_pos_iff.mpr
  let atom : Fin (WeightedSimpleGraph.extendedProfileStateBound beta q r) :=
    ⟨0, by unfold WeightedSimpleGraph.extendedProfileStateBound; omega⟩
  exact ⟨fun _ ↦ atom⟩

theorem extendedProfileCanonicalDummyProb_nonneg
    (k : ℕ) (beta q r : ℝ) :
    ∀ a, 0 ≤ extendedProfileCanonicalDummyProb k beta q r a := by
  intro a
  unfold extendedProfileCanonicalDummyProb
  positivity

theorem sum_extendedProfileCanonicalDummyProb
    (k : ℕ) (beta q r : ℝ) :
    ∑ a, extendedProfileCanonicalDummyProb k beta q r a = 1 := by
  letI : Nonempty
      (WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r) :=
    extendedProfilePackedBlockState_nonempty k beta q r
  have hcard :
      (Fintype.card
        (WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r) : ℝ) ≠
        0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card
        (WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r) ≠ 0)
  unfold extendedProfileCanonicalDummyProb
  rw [Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_mul]
  change
    (Fintype.card
        (WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r) : ℝ) *
        (1 / (Fintype.card
          (WeightedSimpleGraph.ExtendedProfilePackedBlockState k beta q r) : ℝ)) =
      1
  rw [one_div]
  exact mul_inv_cancel₀ hcard

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s beta q r : ℝ} {hbeta : 0 < beta} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s beta q r hbeta hr)

/-- The selected-profile data theorem with all artificial padding inputs
eliminated. -/
theorem exists_selectedBlockData_for_dyadicIteration_canonical
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k)) :
    ∃ choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k beta q r,
      (∀ v b, 0 < G.extendedProfileBlockMass R0 omega v
        (G.decodeExtendedProfileBlock R0 v (choice (v, b)))) ∧
      (∀ large : G.ExtendedProfileLargeRow
          (n := B * k) (β := beta) (q := q) (r := r),
        G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl large) /
            extendedProfileCandidateCapacityScale rho s omega beta q r <
          ((B * k : ℕ) : ℝ) * rho /
              (extendedProfileCandidateCapacityScale rho s omega beta q r *
                extendedProfileSmoothingKappa omega beta q r) +
            extendedProfileBlockCombinedDeviation
              rho s omega beta q r B k) ∧
      (∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.selectedExtendedProfileTotalOptionMass
            R0 rho omega choice e.1 - rho * s) ^ 2) ≤
          extendedProfileBlockQuadraticBound rho s omega beta q r B k) ∧
      ∀ v c,
        G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
          (rho / extendedProfileSmoothingKappa omega beta q r) *
              G.extendedProfileReservoirSize R0 v
                (G.decodedExtendedProfileBlockSelection R0 choice v c) +
            extendedProfileCandidateCapacityScale rho s omega beta q r /
                ((B * k : ℕ) : ℝ) *
              extendedProfileBlockCombinedDeviation
                rho s omega beta q r B k := by
  let mean := extendedProfileBlockCombinedMeanBound
    rho s omega beta q r B k
  let offset : ℕ := Nat.ceil mean + 1
  have hoffset : 0 < offset := by dsimp [offset]; omega
  have hmean : mean ≤ (offset : ℝ) := by
    dsimp [offset]
    exact (Nat.le_ceil mean).trans (by norm_num)
  exact G.exists_selectedBlockData_for_dyadicIteration R0 hB hk hn hs hspos
    hq hr0 hleft omega homega0 homega1 rho hrho hpack offset hoffset hmean
    (extendedProfileCanonicalDummyProb k beta q r)
    (extendedProfileCanonicalDummyProb_nonneg k beta q r)
    (sum_extendedProfileCanonicalDummyProb k beta q r)

end WeightedSimpleGraph
end
end WeightedEdgeColoring
