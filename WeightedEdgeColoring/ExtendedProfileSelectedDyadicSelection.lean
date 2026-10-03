import WeightedEdgeColoring.ExtendedProfileBlockReservoirCapacitySelection
import WeightedEdgeColoring.ExtendedProfileSelectedDyadicDecoder

/-!
# Selected-profile data used by the local-dyadic iteration

One simultaneous profile selection supplies all three deterministic inputs
needed later: ordinary slot-capacity rows, tiny reservoir rows, and the
quadratic residual estimate.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedSimpleGraph

universe u

variable (G : WeightedSimpleGraph.{u})
variable {B k : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (R0 : ∀ v, G.BoundedProfileRealization
  (fun _e : G.StarEdge v ↦ (1 : ℝ) / ((B * k : ℕ) : ℝ))
    s β q r hβ hr)

/-- Simultaneous selector in exactly the form consumed by the endpoint
iteration and final decoder. -/
theorem exists_selectedBlockData_for_dyadicIteration
    (hB : 0 < B) (hk : 0 < k) (hn : 0 < B * k)
    (hs : 0 ≤ s) (hspos : 0 < s)
    (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (omega : ℝ) (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (rho : ℝ) (hrho : 0 < rho)
    (hpack : G.LocallyPacksInto (B * k))
    (offset : ℕ) (hoffset : 0 < offset)
    (hoffsetMean : extendedProfileBlockCombinedMeanBound
      rho s omega β q r B k ≤ offset)
    (dummyProb : ExtendedProfilePackedBlockState k β q r → ℝ)
    (hdummy0 : ∀ a, 0 ≤ dummyProb a)
    (hdummySum : ∑ a, dummyProb a = 1) :
    ∃ choice : (G.V × Fin B) → ExtendedProfilePackedBlockState k β q r,
      (∀ v b, 0 < G.extendedProfileBlockMass R0 omega v
        (G.decodeExtendedProfileBlock R0 v (choice (v, b)))) ∧
      (∀ large : G.ExtendedProfileLargeRow
          (n := B * k) (β := β) (q := q) (r := r),
        G.selectedBlockCapacityLoad R0 rho omega choice (Sum.inl large) /
            extendedProfileCandidateCapacityScale rho s omega β q r <
          ((B * k : ℕ) : ℝ) * rho /
              (extendedProfileCandidateCapacityScale rho s omega β q r *
                extendedProfileSmoothingKappa omega β q r) +
            extendedProfileBlockCombinedDeviation
              rho s omega β q r B k) ∧
      (∀ v,
        (∑ e : G.StarEdge v, G.weight e.1 *
          (G.selectedExtendedProfileTotalOptionMass
            R0 rho omega choice e.1 - rho * s) ^ 2) ≤
          extendedProfileBlockQuadraticBound rho s omega β q r B k) ∧
      ∀ v c,
        G.selectedBlockNormalizedTinyReservoirLoad R0 rho omega choice (v, c) ≤
          (rho / extendedProfileSmoothingKappa omega β q r) *
              G.extendedProfileReservoirSize R0 v
                (G.decodedExtendedProfileBlockSelection R0 choice v c) +
            extendedProfileCandidateCapacityScale rho s omega β q r /
                ((B * k : ℕ) : ℝ) *
              extendedProfileBlockCombinedDeviation
                rho s omega β q r B k := by
  obtain ⟨selected, hselected, hlarge, htiny, hvariance⟩ :=
    G.exists_extendedProfileBlock_reservoir_capacity_and_variance R0
      hB hk hn hs hspos
      hq hr0 hleft omega homega0 homega1 rho hrho hpack offset hoffset
      hoffsetMean dummyProb hdummy0 hdummySum
  let choice := G.encodeExtendedProfileBlockSelection R0 selected
  have hvariance' : ∀ v,
      G.selectedTotalRawExtendedProfileBlockVariance R0 rho omega choice v ≤
        extendedProfileBlockSelectedVarianceBound
          rho s omega β q r B k := by
    simpa [choice] using hvariance
  have hquad := (G.selectedBlock_quadratic_and_signedDeficit_le_explicit
    R0 hB hk rho omega choice hvariance').1
  refine ⟨choice, ?_, ?_, hquad, ?_⟩
  · intro v b
    simpa [choice, encodeExtendedProfileBlockSelection] using hselected v b
  · intro large
    simpa [choice] using hlarge large
  · intro v c
    apply le_of_lt
    apply G.selectedBlockNormalizedTinyReservoirLoad_lt_of_capacityRow R0
      hn hs hq hr0 hleft rho omega homega0 homega1 hrho.le choice
    have hrow := htiny (v, c)
    convert hrow using 1 <;>
      simp [choice] <;> ring

end WeightedSimpleGraph

end

end WeightedEdgeColoring
