import WeightedEdgeColoring.SubtwoInterpolatedPotential
import WeightedEdgeColoring.SubtwoPriceCover

/-! Every nonnegative ten-coordinate disjoint-packet price vector has a
verified endpoint certificate of total potential at most `157/40`. -/

namespace WeightedEdgeColoring.Subtwo.AllPricePotential

open EndpointPotential TwoModelGeometry PriceRelabel

theorem exists_certificate (p : Bundle → ℝ)
    (hp : ∀ e, 0 ≤ p e)
    (hdisjoint : ∀ e f : Bundle,
      Disjoint (edge e) (edge f) → p e + p f ≤ 1) :
    ∃ m rho : Bundle → ℝ, ∃ h : Vertex → ℝ,
      ∃ C : Certificate m rho h,
        (∀ e, p e ≤ m e) ∧ (∀ e, 0 ≤ m e) ∧
        (∀ e, 0 ≤ rho e) ∧ (∀ e, rho e ≤ 2) ∧
        (∀ v, 0 ≤ h v) ∧
        (∑ v, C.P v) ≤ (157/40:ℝ) := by
  rcases PriceCover.no_high_or_model p hdisjoint with hhalf |
    ⟨π, a, x, y, ha, hsy, hyx, hxa, hdom⟩
  · let a : ℝ := 1/2
    let m := uniformStarM a
    let rho := uniformStarRho a
    let h := uniformStarH a
    let C := uniformStar_certificate a (by norm_num) (by norm_num)
    have hmhalf : ∀ e, m e = (1/2:ℝ) := by
      intro e
      fin_cases e <;> first
        | rfl
        | (change 1-(1/2:ℝ)=1/2; norm_num)
    have hrhalf : ∀ e, rho e = (2/3:ℝ) := by
      intro e
      fin_cases e <;> first
        | rfl
        | (change 2*(1-(1/2:ℝ))/(3*(1/2))=2/3; norm_num)
    have hhhalf : ∀ v, h v = (0:ℝ) := by
      intro v
      fin_cases v <;> first
        | rfl
        | (change (2*(1/2:ℝ)-1)/(3*(1/2))=0; norm_num)
    refine ⟨m, rho, h, C, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; rw [hmhalf]; exact hhalf e
    · intro e; rw [hmhalf]; norm_num
    · intro e; rw [hrhalf]; norm_num
    · intro e; rw [hrhalf]; norm_num
    · intro v; simp [hhhalf]
    · simpa [C] using le_of_eq
        (uniformStar_budget a (by norm_num) (by norm_num))
  · have ha1 : a ≤ 1 := by
      have h0 : 0 ≤ permutePrices π.symm p 9 := by
        simpa [permutePrices] using hp (edgePerm π 9)
      have h9 := hdom 9
      have := le_trans h0 h9
      simp [M] at this
      linarith
    let C₀ := uniformModel_certificate a x y ha ha1 hsy hyx hxa
    let C := PriceRelabel.transport π C₀
    let m := PriceRelabel.permutePrices π (M a x y)
    let rho := PriceRelabel.permutePrices π (uniformStarRho a)
    let h := PriceRelabel.permuteVertices π (uniformStarH a)
    refine ⟨m, rho, h, C, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e
      have he := hdom (edgePerm π.symm e)
      simpa [m, permutePrices, edgePerm_apply_symm] using he
    · intro e
      exact uniformModel_cap_nonneg a x y ha ha1 hsy hyx hxa _
    · intro e
      exact uniformModel_rho_nonneg a ha ha1 _
    · intro e
      exact uniformModel_rho_le_two a ha ha1 _
    · intro v
      exact uniformModel_h_nonneg a ha _
    · simpa [C, C₀, PriceRelabel.transport_budget] using
        (uniformModel_budget a x y ha ha1 hsy hyx hxa)

end WeightedEdgeColoring.Subtwo.AllPricePotential
