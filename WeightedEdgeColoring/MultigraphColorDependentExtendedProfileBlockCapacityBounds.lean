import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileCandidateColumns
import WeightedEdgeColoring.MultigraphColorDependentExtendedProfileBlockVarianceSelection

/-!
# Candidate-capacity columns for fixed color blocks

This is the direct adapter between the per-color polynomial bound and the
simultaneous block capacity/variance selector.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

noncomputable section

namespace WeightedMultigraph

universe u

variable (G : WeightedMultigraph.{u})
variable {B k n : ℕ}
variable {s β q r : ℝ} {hβ : 0 < β} {hr : 0 < r}
variable (proposal : G.E → (Fin B × Fin k) → ℝ)
variable (R : ∀ v c, G.BoundedProfileRealization
  (fun e : G.StarEdge v ↦ proposal e.1 c) s β q r hβ hr)

/-- A block source contains exactly `k` color coordinates, each paying the
per-color candidate column bound. -/
theorem sum_colorDependentBlockCandidateUse_le_column
    {L : ℕ} (hL : 0 < L)
    (hn : 0 < n) (hs : 0 < s) (hq : 0 ≤ q) (hr0 : 0 ≤ r)
    (hleft : 0 ≤ 1 - s * (1 + q + r))
    (homega0 : 0 < omega) (homega1 : omega ≤ 1)
    (hrho : 0 < rho) (hC0 : 0 < C0)
    (hproposal : ∀ e c, proposal e c ≤ C0 / (n : ℝ))
    (hstar : ∀ v, G.starWeight v ≤ n)
    (source : G.V × Fin B)
    (a : G.ColorDependentExtendedProfilePackedBlockState
      (k := k) (β := β) (q := q) (r := r)) :
    (∑ row : G.ColorDependentExtendedProfileCapacityRow
        (G.ColorDependentCandidateRowAt R),
      G.colorDependentBlockCandidateUse proposal R n
        ((L : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
        rho omega source a row) ≤
      (k : ℝ) * colorDependentCandidatePerColorColumnBound n β q r := by
  classical
  rw [Fintype.sum_sigma, Fintype.sum_prod_type]
  calc
    (∑ b : Fin B, ∑ i : Fin k,
      ∑ row : G.ColorDependentCandidateRowAt R (b, i),
        G.colorDependentBlockCandidateUse proposal R n
          ((L : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
          rho omega source a ⟨(b, i), row⟩) =
      ∑ i : Fin k,
        ∑ row : G.ColorDependentCandidateRowAt R (source.2, i),
          G.scaledColorDependentCandidateAtomUse proposal R n
            ((L : ℝ) * colorDependentCandidateCapacityScale rho s omega β q r C0)
            rho omega source.1 (source.2, i)
              (G.decodeColorDependentExtendedProfileBlock
                proposal R source a i) row := by
      rw [Finset.sum_eq_single source.2]
      · simp [colorDependentBlockCandidateUse]
      · intro b _hb hb
        have hne : b ≠ source.2 := hb
        apply Finset.sum_eq_zero
        intro i _hi
        apply Finset.sum_eq_zero
        intro row _hrow
        simp [colorDependentBlockCandidateUse, Ne.symm hne]
      · simp
    _ ≤ ∑ _i : Fin k,
        colorDependentCandidatePerColorColumnBound n β q r := by
      apply Finset.sum_le_sum
      intro i _hi
      exact G.sum_scaledColorDependentCandidateAtomUse_mul_le_column proposal R
        hL hn hs hq hr0 hleft homega0 homega1 hrho hC0 hproposal hstar
          source.1 (source.2, i)
          (G.decodeColorDependentExtendedProfileBlock proposal R source a i)
    _ = (k : ℝ) *
        colorDependentCandidatePerColorColumnBound n β q r := by simp

end WeightedMultigraph

end

end WeightedEdgeColoring
