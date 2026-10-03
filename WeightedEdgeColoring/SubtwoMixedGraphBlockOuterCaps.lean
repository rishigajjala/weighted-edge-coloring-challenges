import WeightedEdgeColoring.SubtwoMixedGraphDyadicSupportBudget
import WeightedEdgeColoring.SubtwoMixedGraphBlockInitialSlotEventual

/-! Uniform dyadic codegree and support budgets for `Fin B × Fin k`. -/

namespace WeightedEdgeColoring

noncomputable section

namespace WeightedMultigraph

theorem mixedGraph_eventually_blockOuterCaps
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    {k mult : ℕ}
    {β qstep r rho s omega C0 extraGamma : ℝ}
    (hβ : 0 < β) (hextraGamma : extraGamma < 1)
    (hscale0 : 0 ≤ mixedGraphCandidateCapacityScale (Label := Label)
      (β := β) (qstep := qstep) (r := r) rho s omega C0) :
    ∃ n0 : ℕ, ∀ n B : ℕ, n0 ≤ n → B * k ≤ 4 * n →
      let m := dyadicSimpleRoot n
      let places := explicitLargeSlotBound β qstep r
      let scale := mixedGraphCandidateCapacityScale (Label := Label)
        (β := β) (qstep := qstep) (r := r) rho s omega C0
      let A := boundedMultiplicityDyadicFixedCodegreeCoefficient
        mult places scale
      let Ecoef := boundedMultiplicityDyadicSupportCoefficient β extraGamma
      let Ccoef := 4 * boundedMultiplicityDyadicChoiceCoefficient
        places β extraGamma
      let N := dyadicSimpleQuantizationScale m
      let reserve := dyadicSimpleReserveScale m
      let lambda := dyadicSimpleCodegreeScale A m
      let E := Ecoef * m ^ 20
      let C := Ccoef * m ^ 20
      (N : ℝ) * ((places : ℝ) * scale / (n : ℝ)) ≤ lambda ∧
      scale / (n : ℝ) ≤ 1 / (reserve : ℝ) ∧
      (N : ℝ) / reserve ≤ lambda ∧
      (mult : ℝ) * N / reserve ≤ lambda ∧
      2 * ((n : ℝ) / β / (1 - extraGamma) + 1 + reserve) ≤ E ∧
      B * k * places * places + E ≤ C := by
  let places := explicitLargeSlotBound β qstep r
  let scale := mixedGraphCandidateCapacityScale (Label := Label)
    (β := β) (qstep := qstep) (r := r) rho s omega C0
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1
    (eventually_const_le_pos_mul_nat scale 1 (by norm_num))
  refine ⟨max (2 ^ 20) (M0 ^ 20), ?_⟩
  intro n B hn hpalette
  dsimp only
  let m := dyadicSimpleRoot n
  have hMpow : M0 ^ 20 ≤ n := (le_max_right (2 ^ 20) _).trans hn
  have hmM : M0 ≤ m := le_dyadicSimpleRoot_of_pow_le hMpow
  have hm2 : 2 ≤ m := by
    apply le_dyadicSimpleRoot_of_pow_le
    exact (le_max_left (2 ^ 20) _).trans hn
  have hnLower : m ^ 20 ≤ n := dyadicSimpleRoot_pow_le n
  have hnUpper : n ≤ 2 ^ 20 * m ^ 20 := by
    have hsucc : m + 1 ≤ 2 * m := by omega
    have hpow := Nat.pow_le_pow_left hsucc 20
    have hnlt := lt_succ_dyadicSimpleRoot_pow n
    calc
      n ≤ (m + 1) ^ 20 := le_of_lt hnlt
      _ ≤ (2 * m) ^ 20 := hpow
      _ = 2 ^ 20 * m ^ 20 := by ring
  have hscaleGrow : scale ≤ m := by
    simpa [scale] using hM0 m hmM
  obtain ⟨hc1, hc2, hc3, hc4⟩ :=
    mixedGraph_dyadicCodegreeCaps
      (Label := Label) (β := β) (qstep := qstep) (r := r)
      (rho := rho) (s := s) (omega := omega) (C0 := C0)
      (mult := mult) (m := m) (n := n)
      hm2 hnLower hscale0 hscaleGrow
  obtain ⟨hs1, hs2⟩ := mixedGraph_dyadicSupportCaps
    (m := m) (n := n) (palette := B * k) (places := places)
    (β := β) (extraGamma := extraGamma)
    (by omega : 1 ≤ m) hβ hextraGamma hnUpper hpalette
  exact ⟨hc1, hc2, hc3, hc4, hs1, hs2⟩

end WeightedMultigraph

end
end WeightedEdgeColoring
