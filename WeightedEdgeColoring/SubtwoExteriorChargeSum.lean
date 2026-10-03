import WeightedEdgeColoring.SubtwoBundleCharge

/-! Total original endpoint reservations equal the charge crossing the block. -/

open scoped BigOperators
namespace WeightedEdgeColoring.WeightedMultigraph
universe u
variable (G : WeightedMultigraph.{u})

theorem sum_subtwoExteriorHarmonicCharge (S : Finset G.V) :
    (∑ v ∈ S, G.subtwoExteriorHarmonicCharge S v) =
      G.subtwoBoundaryCost (fun e => harmonicCharge (G.weight e)) S := by
  classical
  let cost : G.E → ℝ := fun e =>
    if G.fst e ∈ S ∧ G.snd e ∈ S then 0 else harmonicCharge (G.weight e)
  have hv : ∀ v, G.subtwoExteriorHarmonicCharge S v = G.subtwoVertexCost cost v := by
    intro v
    rw [G.subtwoVertexCost_eq_incidence]
    unfold subtwoExteriorHarmonicCharge
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : G.Inc v e <;>
      by_cases hs : G.fst e ∈ S ∧ G.snd e ∈ S <;> simp [cost, hi, hs]
  have hint : G.subtwoInternalCost cost S = 0 := by
    unfold subtwoInternalCost
    apply Finset.sum_eq_zero
    intro e _
    by_cases hs : G.fst e ∈ S ∧ G.snd e ∈ S <;> simp [cost, hs]
  have hb : G.subtwoBoundaryCost cost S =
      G.subtwoBoundaryCost (fun e => harmonicCharge (G.weight e)) S := by
    unfold subtwoBoundaryCost
    apply Finset.sum_congr rfl
    intro e _
    by_cases hf : G.fst e ∈ S <;> by_cases hs : G.snd e ∈ S <;> simp [cost, hf, hs]
  simp_rw [hv]
  rw [G.subtwo_incidence_identity, hint, mul_zero, zero_add, hb]

/-- Every actual rank-two block has a total exterior reservation strictly
below the available 1.999 palette. The statement uses no price vector. -/
theorem subtwoFloorFive_exterior_budget
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2) :
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
    (∑ v ∈ S, G.subtwoExteriorHarmonicCharge S v / (n : ℝ)) ≤ subtwoKappa := by
  dsimp only
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
  rw [← Finset.sum_div]
  change (∑ v ∈ S, G.subtwoExteriorHarmonicCharge S v) / (n : ℝ) ≤ subtwoKappa
  have heq := congrArg (fun x : ℝ => x / (n : ℝ)) (G.sum_subtwoExteriorHarmonicCharge S)
  apply le_trans (le_of_eq heq)
  apply (div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  have h := G.subtwoFloorBlock_boundary_harmonic_le hn hlocal b
  dsimp only at h
  rw [hrank] at h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  norm_num [subtwoM, subtwoKappa] at h ⊢
  nlinarith

end WeightedEdgeColoring.WeightedMultigraph
