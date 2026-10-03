import WeightedEdgeColoring.SubtwoBundleCharge
import WeightedEdgeColoring.SubtwoGraphPatternCopies

/-!
# The unit bounds used by the dense-five certificate

The certificate checks rounded dual residuals against finite variable
bounds.  In particular its exterior-charge products require a bound on
the actual exterior charge.  Rank-two blocks supply the stronger bound
`Q = 5M - 4κ = 0.459155`, not just the general per-vertex bound `M`.
-/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoExteriorHarmonicCharge_nonneg (S : Finset G.V) (v : G.V) :
    0 ≤ G.subtwoExteriorHarmonicCharge S v := by
  unfold subtwoExteriorHarmonicCharge
  apply Finset.sum_nonneg
  intro e he
  split_ifs
  · exact harmonicCharge_nonneg _
  · rfl

theorem subtwoExteriorHarmonicCharge_le_boundary (S : Finset G.V) (v : G.V) (hv : v ∈ S) :
    G.subtwoExteriorHarmonicCharge S v ≤
      G.subtwoBoundaryCost (fun e => harmonicCharge (G.weight e)) S := by
  unfold subtwoExteriorHarmonicCharge subtwoBoundaryCost
  apply Finset.sum_le_sum
  intro e he
  by_cases hi : G.Inc v e ∧ ¬(G.fst e ∈ S ∧ G.snd e ∈ S)
  · have hsome : G.fst e ∈ S ∨ G.snd e ∈ S := by
      rcases hi.1 with hf | hs
      · left; simpa [hf] using hv
      · right; simpa [hs] using hv
    have hcross : (G.fst e ∈ S) ≠ (G.snd e ∈ S) := by
      intro heq
      apply hi.2
      rcases hsome with hf | hs
      · exact ⟨hf, Eq.mp heq hf⟩
      · exact ⟨Eq.mpr heq hs, hs⟩
    simp [hi, hcross]
  · simp only [if_neg hi]
    split_ifs
    · exact harmonicCharge_nonneg _
    · rfl

/-- Each normalized exterior-charge variable of the actual constructed
five-block is at most `Q < 1`. -/
theorem subtwoFloorFive_exterior_normalized_bounds
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (v : G.V)
    (hv : v ∈ G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q) :
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q
    0 ≤ G.subtwoExteriorHarmonicCharge S v / n ∧
      G.subtwoExteriorHarmonicCharge S v / n ≤ (459155 / 1000000 : ℝ) := by
  dsimp only
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q
  have hb := G.subtwoFloorBlock_boundary_harmonic_le hn hlocal q
  dsimp only at hb
  rw [hrank] at hb
  norm_num only [Nat.cast_ofNat] at hb
  have hconstant : (5 * subtwoM - 4 * subtwoKappa) =
      (459155 / 1000000 : ℝ) := by norm_num [subtwoM, subtwoKappa]
  rw [hconstant] at hb
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (G.subtwoExteriorHarmonicCharge_nonneg S v) hnR.le
  · apply (div_le_iff₀ hnR).2
    exact (G.subtwoExteriorHarmonicCharge_le_boundary S v hv).trans hb

/-- Both a price/exterior product and the exterior avoiding-profit are
within the certificate's unit interval. This uses the actual block bound. -/
theorem subtwoFloorFive_exterior_products_bounds
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (v : G.V)
    (hv : v ∈ G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q)
    (m r : ℝ) (hm : 0 ≤ m ∧ m ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    let Qv := G.subtwoExteriorHarmonicCharge
      (G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q) v / n
    (0 ≤ m * Qv ∧ m * Qv ≤ 1) ∧
      (0 ≤ Qv * (1 - r) ∧ Qv * (1 - r) ≤ 1) := by
  dsimp only
  obtain ⟨hq0, hq⟩ := G.subtwoFloorFive_exterior_normalized_bounds hn hlocal q hrank v hv
  constructor
  · constructor
    · exact mul_nonneg hm.1 hq0
    · have h := mul_le_mul_of_nonneg_right hm.2 hq0
      nlinarith
  · constructor
    · exact mul_nonneg hq0 (sub_nonneg.mpr hr.2)
    · have h := mul_nonneg hq0 hr.1
      nlinarith

end WeightedEdgeColoring.WeightedMultigraph
