import WeightedEdgeColoring.SubtwoNumericGraphBridge
import WeightedEdgeColoring.SubtwoFiveVertexPriceData
import WeightedEdgeColoring.SubtwoGraphEndpointDemand
import WeightedEdgeColoring.SubtwoAllPricePotential

/-! The endpoint certificate applied to actual local fractional bins on at
most five vertices. The finite witness can be supplied by a uniform model
or by an arbitrarily relabelled price certificate. -/

open scoped BigOperators

namespace WeightedEdgeColoring.Subtwo.FiveVertexLocalBound

open EndpointPotential
open GraphEndpoint
open NumericGraphBridge

universe u
variable (G : WeightedMultigraph.{u})

theorem local_bound_finite_certificate
    (label : G.V → Vertex) (hinj : Function.Injective label)
    {m rho : Bundle → ℝ} {h : Vertex → ℝ}
    (C : EndpointPotential.Certificate m rho h)
    (hm : ∀ e, 0 ≤ m e) (hr0 : ∀ e, 0 ≤ rho e)
    (hr2 : ∀ e, rho e ≤ 2) (hh : ∀ v, 0 ≤ h v)
    (hbudget : ∑ v, C.P v ≤ (157/40:ℝ))
    (demand price : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand)
    (hp : ∀ e, 0 ≤ price e)
    (hprice : ∀ p : G.SubtwoWeightedPattern,
      (∑ e, price e * (p.val e : ℝ)) ≤ 1)
    (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1)
    (hmajorant : ∀ i, FiveVertexPriceData.prices G label price i ≤ m i) :
    (∑ e, price e * demand e) ≤ (157/80:ℝ) := by
  let bundle := canonicalBundle G label hinj
  let CG := lift G label hinj bundle
    (canonicalBundle_ends G label hinj)
    (canonicalBundle_shared G label hinj) C hm hr0 hr2 hh
  have hcap : ∀ e, G.subtwoSupportedPriceMax {G.fst e, G.snd e} price ≤
      m (bundle e) := by
    intro e
    have hcode : bundle e = FiveVertexPriceData.bundleCode G label hinj e := rfl
    rw [hcode]
    rw [← FiveVertexPriceData.prices_bundleCode G label hinj price e]
    exact hmajorant _
  have hP : ∑ v, CG.P v ≤ (157/40:ℝ) :=
    (lift_budget_le G label hinj bundle
      (canonicalBundle_ends G label hinj)
      (canonicalBundle_shared G label hinj) C hm hr0 hr2 hh).trans hbudget
  have h := CG.demand_price_bound demand price B hp hcap hprice htotal
  linarith

theorem local_bound_model
    (label : G.V → Vertex) (hinj : Function.Injective label)
    (a x y : ℝ) (ha : (1/2:ℝ) < a) (ha1 : a ≤ 1)
    (hsy : 1-a ≤ y) (hyx : y ≤ x) (hxa : x ≤ a)
    (demand price : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand)
    (hp : ∀ e, 0 ≤ price e)
    (hprice : ∀ p : G.SubtwoWeightedPattern,
      (∑ e, price e * (p.val e : ℝ)) ≤ 1)
    (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1)
    (hmajorant : ∀ i, FiveVertexPriceData.prices G label price i ≤
      TwoModelGeometry.M a x y i) :
    (∑ e, price e * demand e) ≤ (157/80:ℝ) := by
  exact local_bound_finite_certificate G label hinj
    (uniformModel_certificate a x y ha ha1 hsy hyx hxa)
    (uniformModel_cap_nonneg a x y ha ha1 hsy hyx hxa)
    (uniformModel_rho_nonneg a ha ha1)
    (uniformModel_rho_le_two a ha ha1)
    (uniformModel_h_nonneg a ha)
    (uniformModel_budget a x y ha ha1 hsy hyx hxa)
    demand price B hp hprice htotal hmajorant

/-- The genuine five-vertex local theorem at normalized color price one.
The ten numerical prices and the certificate are constructed from the
graph; neither is an input assumption. -/
theorem local_bound_normalized
    (hV : Fintype.card G.V ≤ 5)
    (demand price : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand)
    (hp : ∀ e, 0 ≤ price e)
    (hprice : ∀ p : G.SubtwoWeightedPattern,
      (∑ e, price e * (p.val e : ℝ)) ≤ 1)
    (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1) :
    (∑ e, price e * demand e) ≤ (157/80:ℝ) := by
  obtain ⟨label, hinj⟩ := FiveVertexPriceData.exists_injective_label G hV
  let p : Bundle → ℝ := FiveVertexPriceData.prices G label price
  have hp0 : ∀ i, 0 ≤ p i := by
    intro i
    exact FiveVertexPriceData.prices_nonneg G label price hp i
  have hdis : ∀ i j : Bundle,
      Disjoint (TwoModelGeometry.edge i) (TwoModelGeometry.edge j) →
        p i+p j ≤ 1 := by
    intro i j hij
    exact FiveVertexPriceData.prices_disjoint G label price hprice i j hij
  obtain ⟨m, rho, h, C, hmaj, hm, hr0, hr2, hh, hbudget⟩ :=
    AllPricePotential.exists_certificate p hp0 hdis
  exact local_bound_finite_certificate G label hinj C hm hr0 hr2 hh hbudget
    demand price B hp hprice htotal hmaj

/-- The price bound at the true maximum color price, including its zero
case. No normalization hypothesis is left in the statement. -/
theorem local_bound_price
    (hV : Fintype.card G.V ≤ 5)
    (demand price : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand)
    (hp : ∀ e, 0 ≤ price e)
    (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1) :
    (∑ e, price e * demand e) ≤
      (157/80:ℝ) * G.subtwoColorPriceMax price := by
  let R : ℝ := G.subtwoColorPriceMax price
  have hR0 : 0 ≤ R := G.subtwoColorPriceMax_nonneg price hp
  by_cases hz : R = 0
  · have hzero := (G.subtwoColorPriceMax_eq_zero_iff price hp).mp hz
    simp [R, hz, hzero]
  have hR : 0 < R := by
    rcases lt_or_eq_of_le hR0 with hlt | heq
    · exact hlt
    · exact False.elim (hz heq.symm)
  let price' : G.E → ℝ := fun e ↦ price e / R
  have hp' : ∀ e, 0 ≤ price' e := by
    intro e
    exact div_nonneg (hp e) hR.le
  have hsum (f : G.E → ℝ) :
      (∑ e, price' e * f e) = (∑ e, price e * f e) / R := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [price']
    ring
  have hprice' : ∀ p : G.SubtwoWeightedPattern,
      (∑ e, price' e * (p.val e : ℝ)) ≤ 1 := by
    intro p
    have hraw := Subtwo.patternPrice_le_paletteMaxScore
      G.subtwoReservedColorPattern price none p
    change (∑ e, price e * (p.val e : ℝ)) ≤ R at hraw
    rw [hsum]
    exact (div_le_iff₀ hR).mpr (by simpa using hraw)
  have hnormalized := local_bound_normalized G hV demand price' B hp' hprice' htotal
  rw [hsum] at hnormalized
  exact (div_le_iff₀ hR).mp hnormalized

/-- Local unit-cost bins on at most five vertices admit a genuine palette
allocation with budget `157/80`; the palette uses the graph's actual
weighted multiset patterns, including repeated types. -/
theorem local_palette_attainable
    (hV : Fintype.card G.V ≤ 5)
    (demand : G.E → ℝ) (B : G.SubtwoLocalFractionalBins demand)
    (htotal : ∀ v, (∑ p, B.mass v p) ≤ 1) :
    demand ∈ Subtwo.PaletteAttainable
      (Subtwo.reservedPaletteBudget (157/80:ℝ) (fun _ : G.V ↦ 0))
      G.subtwoReservedColorPattern := by
  have hd : ∀ e, 0 ≤ demand e := by
    intro e
    have hc := B.covers (G.fst e) e
    have hi : G.Inc (G.fst e) e := Or.inl rfl
    rw [if_pos hi] at hc
    rw [← hc]
    exact Finset.sum_nonneg (fun p _ ↦
      mul_nonneg (B.mass_nonneg (G.fst e) p) (Nat.cast_nonneg _))
  have hq : ∀ v : G.V, (0:ℝ) ≤ 0 := by intro v; norm_num
  have hsum : (∑ v : G.V, (0:ℝ)) ≤ (157/80:ℝ) := by simp; norm_num
  apply (G.subtwoGraphPalette_iff_chargeInequalities
    (157/80:ℝ) (fun _ : G.V ↦ 0) hq hsum hd).2
  intro price hp
  simpa using local_bound_price G hV demand price B hp htotal

end WeightedEdgeColoring.Subtwo.FiveVertexLocalBound
