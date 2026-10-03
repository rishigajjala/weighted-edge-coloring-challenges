import WeightedEdgeColoring.WeightedMomentProposal

/-!
# The exact moment-estimate interface for Kempe mixing

The switching argument only has to produce two uniform estimates: one
first-moment pressure estimate for every vertex--color row and one weighted
squared-error estimate for the normalized common-palette sizes.  This file
records that smaller target and proves, deterministically, that it implies
`WeightedMomentPaletteMixing`.
-/

namespace WeightedEdgeColoring

open scoped BigOperators

universe u

/-- Uniform moment estimates obtainable by proper recoloring. -/
def WeightedMomentEstimateMixing : Prop :=
  ∀ alpha C L delta sigma : ℝ,
    0 < alpha → 0 < C → 0 < L → 0 < delta → 0 < sigma →
    ∃ N : ℕ, ∀ (G : WeightedMultigraph.{u}) (n q : ℕ)
      (F R : Finset G.E) (base : G.E → Fin q) (charge : G.E → ℝ),
      N ≤ n →
      0 < n →
      Even q →
      4 ≤ q →
      Disjoint F R →
      G.IsProperOn F base →
      (∀ v, alpha * n ≤ (G.missingColorsAt F base v).card) →
      (q : ℝ) ≤ C * n →
      (∀ e ∈ R, 0 ≤ charge e) →
      (∀ v, G.restrictedCharge R charge v ≤ n) →
      (∀ v w, G.pairCharge R charge v w ≤ L) →
      ∃ mixed : G.E → Fin q,
        G.IsProperOn F mixed ∧
        (∀ v c,
          G.momentNeighborPressure R charge F mixed v c ≤
            G.restrictedCharge R charge v / q + delta) ∧
        ∀ v,
          G.momentSquaredError R charge F mixed v ≤ sigma * n

theorem ratio_mul_chosen_delta_le
    {q n : ℕ} {f alpha C eps : ℝ}
    (hn : 0 < n) (halpha : 0 < alpha) (hC : 0 < C) (heps : 0 < eps)
    (hf : alpha * n ≤ f) (hq : (q : ℝ) ≤ C * n) :
    (q : ℝ) / f * (eps * alpha / C) ≤ eps := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hfpos : 0 < f := lt_of_lt_of_le (mul_pos halpha hnreal) hf
  have hratio : (q : ℝ) / f ≤ C / alpha := by
    rw [div_le_div_iff₀ hfpos halpha]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) halpha.le,
      mul_nonneg hC.le (sub_nonneg.mpr hf)]
  have hdelta : 0 ≤ eps * alpha / C := by positivity
  calc
    (q : ℝ) / f * (eps * alpha / C) ≤
        (C / alpha) * (eps * alpha / C) :=
      mul_le_mul_of_nonneg_right hratio hdelta
    _ = eps := by field_simp

/-- The moment-estimate interface implies the proposal interface consumed by
the bipartite packet completion. -/
theorem weightedMomentPaletteMixing_of_estimateMixing
    (hmix : WeightedMomentEstimateMixing.{u}) :
    WeightedMomentPaletteMixing.{u} := by
  intro alpha C L eps halpha hC hL heps
  let delta : ℝ := eps * alpha / C
  let sigma : ℝ := eps ^ 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  rcases hmix alpha C L delta sigma halpha hC hL hdelta hsigma with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro G n q F R base charge hn hnpos hqeven hqfour hdisjoint hbase
    hmissingBase hpalette hcharge hrestricted hpair
  rcases hN G n q F R base charge hn hnpos hqeven hqfour hdisjoint hbase
      hmissingBase hpalette hcharge hrestricted hpair with
    ⟨mixed, hmixed, hpressure, hsquared⟩
  have hqpos : 0 < q := by omega
  have hmissingMixed : ∀ v,
      alpha * n ≤ G.momentMissingSize F mixed v := by
    intro v
    have hcard := G.card_missingColorsAt_eq_of_isProperOn
      F base mixed hbase hmixed v
    dsimp [WeightedMultigraph.momentMissingSize]
    rw [← hcard]
    exact hmissingBase v
  have hmissingPos : ∀ v, 0 < G.momentMissingSize F mixed v := by
    intro v
    exact lt_of_lt_of_le
      (mul_pos halpha (by exact_mod_cast hnpos)) (hmissingMixed v)
  refine ⟨mixed, G.momentProposal F mixed, hmixed, ?_, ?_, ?_, ?_, ?_⟩
  · intro e heR c hc
    exact G.momentProposal_pos_support F mixed hc
  · intro e heR c
    exact ⟨G.momentProposal_nonneg F mixed hmissingPos e c,
      G.momentProposal_le_linear_diffuse F mixed alpha C halpha hC hnpos
        hmissingMixed hpalette e c⟩
  · intro e heR
    exact G.sum_momentProposal_le_one F mixed hmissingPos e
  · intro v c
    have hrow := G.proposalChargeLoad_momentProposal_le_uniform_add
      R charge F mixed hcharge hmissingPos hqpos v c (hpressure v c)
    have hextra :
        (q : ℝ) / G.momentMissingSize F mixed v * delta ≤ eps := by
      exact ratio_mul_chosen_delta_le hnpos halpha hC heps
        (hmissingMixed v) hpalette
    dsimp [WeightedMultigraph.momentMissingSize] at hrow ⊢
    exact hrow.trans (add_le_add_right hextra _)
  · intro v
    have h := G.uncoveredProposalCharge_momentProposal_le_eps_mul
      R charge F mixed hcharge hmissingPos v
      (n := (n : ℝ)) (eps := eps) (Nat.cast_nonneg n) heps.le
      (hrestricted v) (by simpa [sigma] using hsquared v)
    simpa using h

end WeightedEdgeColoring
