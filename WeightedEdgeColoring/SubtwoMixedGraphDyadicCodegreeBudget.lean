import WeightedEdgeColoring.SubtwoMixedGraphJointInitialSlotBudget

/-! Polynomial codegree and pair-scale bounds for the actual mixed candidates. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_dyadicCodegreeCaps
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {β qstep r rho s omega C0 : ℝ}
    {mult m n : ℕ}
    (hm : 2 ≤ m) (hnLower : m ^ 20 ≤ n)
    (hscale0 : 0 ≤ mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0)
    (hscaleGrow : mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0 ≤ m) :
    let places := explicitLargeSlotBound β qstep r
    let scale := mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0
    let A := boundedMultiplicityDyadicFixedCodegreeCoefficient mult places scale
    let N := dyadicSimpleQuantizationScale m
    let reserve := dyadicSimpleReserveScale m
    let lambda := dyadicSimpleCodegreeScale A m
    (N : ℝ) * ((places : ℝ) * scale / (n : ℝ)) ≤ lambda ∧
      scale / (n : ℝ) ≤ 1 / (reserve : ℝ) ∧
      (N : ℝ) / reserve ≤ lambda ∧
      (mult : ℝ) * N / reserve ≤ lambda := by
  let places := explicitLargeSlotBound β qstep r
  let scale := mixedGraphCandidateCapacityScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  let A := boundedMultiplicityDyadicFixedCodegreeCoefficient mult places scale
  let N := dyadicSimpleQuantizationScale m
  let reserve := dyadicSimpleReserveScale m
  let lambda := dyadicSimpleCodegreeScale A m
  have hm1 : 1 ≤ m := by omega
  have hA : 1 ≤ A := by
    dsimp [A, boundedMultiplicityDyadicFixedCodegreeCoefficient,
      boundedMultiplicityDyadicCodegreeCoefficient]
    omega
  have hN : 0 < N := by
    dsimp [N, dyadicSimpleQuantizationScale]
    positivity
  have hreserve : 0 < reserve := by
    dsimp [reserve, dyadicSimpleReserveScale]
    positivity
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by omega : 0 < m) _) hnLower
  have hordinary : (N : ℝ) * ((places : ℝ) * scale / n) ≤ lambda := by
    simpa [N, lambda, A, scale, places] using
      boundedMultiplicityDyadic_ordinaryJobCodegree_fixed
        (mult := mult) (m := m) (palette := n) (placeCount := places)
        (scale := scale) hm1 hscale0 hnLower
  have hpair : scale / (n : ℝ) ≤ 1 / (reserve : ℝ) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hreserveR : (0 : ℝ) < reserve := by exact_mod_cast hreserve
    rw [div_le_div_iff₀ hnR hreserveR]
    simp only [one_mul]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hresCast : (reserve : ℝ) = (m : ℝ) ^ 16 := by
      simp [reserve, dyadicSimpleReserveScale]
    have hnCast : (m : ℝ) ^ 20 ≤ n := by exact_mod_cast hnLower
    rw [hresCast]
    calc
      scale * (m : ℝ) ^ 16 ≤
          (m : ℝ) * (m : ℝ) ^ 16 := by gcongr
      _ = (m : ℝ) ^ 17 := by ring
      _ ≤ (m : ℝ) ^ 20 := pow_le_pow_right₀ hmR (by omega)
      _ ≤ n := hnCast
  have hextra : (N : ℝ) / reserve ≤ lambda := by
    simpa [N, reserve, lambda] using
      boundedMultiplicityDyadic_extraCodegree_for_coefficient hm1 hA
  have hmult : (mult : ℝ) * N / reserve ≤ lambda := by
    simpa [N, reserve, lambda, A] using
      boundedMultiplicityDyadic_extraPairCodegree_fixed
        (mult := mult) (m := m) (placeCount := places)
        (scale := scale) hm1
  exact ⟨hordinary, hpair, hextra, hmult⟩

end WeightedMultigraph

end

end WeightedEdgeColoring
