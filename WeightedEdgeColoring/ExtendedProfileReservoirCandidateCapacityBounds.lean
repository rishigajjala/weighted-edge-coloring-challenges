import WeightedEdgeColoring.ExtendedProfileBlockCandidateCapacityRows

/-!
# Reservoir-sensitive candidate capacity means

The packed-word tiny-row estimate retains the reservoir size of the fixed
center state.  This file transports that estimate first to atom sources and
then, without loss, to exact `B * k` block sources.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}

section Atom

variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / n) s β q r hβ hr)

/-- The reservoir-sensitive normalized mean is unchanged by replacing a
packed word source with one atom source for every vertex and colour. -/
theorem rowMean_scaledAtomTinyCandidateCapacityUse_le_reservoir
    (hn : 0 < n) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := n) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileStateProbability R0 omega source.1 a)
        (G.scaledAtomExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r))
        (Sum.inr row) ≤
      ((n : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate) /
        (extendedProfileCandidateCapacityScale rho s omega β q r *
          extendedProfileSmoothingKappa omega β q r) := by
  rw [G.rowMean_scaledAtomCandidateCapacityUse_eq_packedWord R0]
  exact G.rowMean_scaledTinyCandidateCapacityUse_le_reservoir R0
    hn hs hq hr0 hleft homega0 homega1 hrho hspos row

end Atom

section Block

variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Exact `B * k` block marginals preserve the same reservoir-sensitive
normalized tiny-row mean. -/
theorem rowMean_scaledBlockTinyCandidateCapacityUse_le_reservoir
    (hn : 0 < B * k) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hspos : 0 < s)
    (row : G.ExtendedProfileTinyCandidateRow R0
      (n := B * k) (β := β) (q := q) (r := r)) :
    FiniteCategoricalSelection.rowMean
        (fun source a ↦
          G.paddedExtendedProfileBlockProbability R0 omega source.1 a)
        (G.scaledBlockExtendedProfileCandidateCapacityUse R0 rho omega
          (extendedProfileCandidateCapacityScale rho s omega β q r))
        (Sum.inr row) ≤
      (((B * k : ℕ) : ℝ) * rho *
          G.extendedProfileReservoirSize R0 row.center row.candidate) /
        (extendedProfileCandidateCapacityScale rho s omega β q r *
          extendedProfileSmoothingKappa omega β q r) := by
  rw [G.rowMean_scaledBlockCandidateCapacityUse_eq_atom R0]
  exact G.rowMean_scaledAtomTinyCandidateCapacityUse_le_reservoir R0
    hn hs hq hr0 hleft homega0 homega1 hrho hspos row

end Block

end WeightedSimpleGraph

end

end WeightedEdgeColoring
