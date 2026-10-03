import WeightedEdgeColoring.SubtwoThreePhysicalPriceTransfer
import WeightedEdgeColoring.SubtwoFivePhysicalPaletteDual

/-! Actual rank-one triangle reserved palette duality. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

theorem subtwoFloorThree_exterior_budget
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 1) :
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

namespace SubtwoThreePhysicalData

variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoThreePhysicalData n)

theorem sum_over_vertexSet (f : G.V → ℝ) :
    (∑ v : G.V, if v ∈ D.vertexSet then f v else 0) =
      ∑ i : Fin 3, f (D.vertex i) := by
  classical
  calc
    _ = ∑ v ∈ D.vertexSet, f v := by simp
    _ = _ := by
      unfold SubtwoThreePhysicalData.vertexSet
      rw [Finset.sum_image (fun i _ j _ h => D.vertex_injective h)]

theorem physical_dual_sum_identity :
    ((n : ℝ) * G.subtwoColorPriceMax D.price) *
      ((∑ e : G.E, D.price e * G.subtwoFiveInternalDemand D.vertexSet n e) +
        ∑ v : G.V, G.subtwoFiveReservedCharge D.vertexSet n v *
          (G.subtwoColorPriceMax D.price - G.subtwoAvoidingPriceMax D.price v)) =
      G.subtwoColorPriceMax D.price *
        (G.subtwoInternalCost D.price D.vertexSet +
          ∑ i : Fin 3, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
            (G.subtwoColorPriceMax D.price -
              G.subtwoAvoidingPriceMax D.price (D.vertex i))) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast D.n_pos.ne'
  let R := G.subtwoColorPriceMax D.price
  have hint : (∑ e : G.E, D.price e * G.subtwoFiveInternalDemand D.vertexSet n e) =
      G.subtwoInternalCost D.price D.vertexSet / n := by
    unfold subtwoFiveInternalDemand subtwoInternalCost
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> ring
  have hres : (∑ v : G.V, G.subtwoFiveReservedCharge D.vertexSet n v *
      (R - G.subtwoAvoidingPriceMax D.price v)) =
      (∑ i : Fin 3, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
        (R - G.subtwoAvoidingPriceMax D.price (D.vertex i))) / n := by
    calc
      _ = ∑ v : G.V, if v ∈ D.vertexSet then
          (G.subtwoExteriorHarmonicCharge D.vertexSet v *
            (R - G.subtwoAvoidingPriceMax D.price v)) / n else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ D.vertexSet <;>
          simp [subtwoFiveReservedCharge, hv, div_mul_eq_mul_div]
      _ = ∑ i : Fin 3,
          (G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
            (R - G.subtwoAvoidingPriceMax D.price (D.vertex i))) / n := by
        exact D.sum_over_vertexSet _
      _ = _ := by rw [Finset.sum_div]
  rw [hint, hres]
  dsimp [R]
  field_simp

theorem physical_dual_sum_eq_objective :
    ((∑ e : G.E, D.price e * G.subtwoFiveInternalDemand D.vertexSet n e) +
      ∑ v : G.V, G.subtwoFiveReservedCharge D.vertexSet n v *
        (G.subtwoColorPriceMax D.price - G.subtwoAvoidingPriceMax D.price v)) =
      G.subtwoColorPriceMax D.price *
        ((∑ i : Fin 3, D.bundlePrice i) +
          ∑ i : Fin 3, D.exteriorCharge i * (1 - D.avoidingPrice i)) := by
  have hsum := D.physical_dual_sum_identity
  have hnR : ((n : ℝ) * G.subtwoColorPriceMax D.price) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.n_pos.ne') D.price_max_pos.ne'
  have hres :
      (∑ i : Fin 3, D.exteriorCharge i * (1 - D.avoidingPrice i)) =
      (∑ i : Fin 3, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
        (G.subtwoColorPriceMax D.price -
          G.subtwoAvoidingPriceMax D.price (D.vertex i))) /
          ((n : ℝ) * G.subtwoColorPriceMax D.price) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [exteriorCharge, avoidingPrice, subtwoNormalizedAvoidingPrice]
    field_simp [D.price_max_pos.ne', (show (n : ℝ) ≠ 0 from
      by exact_mod_cast D.n_pos.ne')]
  have hobj :
      ((n : ℝ) * G.subtwoColorPriceMax D.price) *
        ((∑ i : Fin 3, D.bundlePrice i) +
          ∑ i : Fin 3, D.exteriorCharge i * (1 - D.avoidingPrice i)) =
      G.subtwoInternalCost D.price D.vertexSet +
        ∑ i : Fin 3, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
          (G.subtwoColorPriceMax D.price -
            G.subtwoAvoidingPriceMax D.price (D.vertex i)) := by
    rw [D.bundlePrice_sum_eq_internal, hres, ← add_div]
    exact (mul_div_cancel₀ _ hnR)
  have hfact :
      ((n : ℝ) * G.subtwoColorPriceMax D.price) *
        ((∑ e : G.E, D.price e * G.subtwoFiveInternalDemand D.vertexSet n e) +
          ∑ v : G.V, G.subtwoFiveReservedCharge D.vertexSet n v *
            (G.subtwoColorPriceMax D.price - G.subtwoAvoidingPriceMax D.price v)) =
      ((n : ℝ) * G.subtwoColorPriceMax D.price) *
        (G.subtwoColorPriceMax D.price *
          ((∑ i : Fin 3, D.bundlePrice i) +
            ∑ i : Fin 3, D.exteriorCharge i * (1 - D.avoidingPrice i))) := by
    calc
      _ = G.subtwoColorPriceMax D.price *
          (G.subtwoInternalCost D.price D.vertexSet +
            ∑ i : Fin 3, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
              (G.subtwoColorPriceMax D.price -
                G.subtwoAvoidingPriceMax D.price (D.vertex i))) := hsum
      _ = _ := by rw [← hobj]; ring
  exact mul_left_cancel₀ hnR hfact

end SubtwoThreePhysicalData

theorem rankOneThree_dual_price_bound
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 1)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) :
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
    (∑ e : G.E, price e * G.subtwoFiveInternalDemand S n e) +
      (∑ v : G.V, G.subtwoFiveReservedCharge S n v *
        (G.subtwoColorPriceMax price - G.subtwoAvoidingPriceMax price v)) ≤
          (1999/1000:ℝ) * G.subtwoColorPriceMax price := by
  dsimp only
  let R := G.subtwoColorPriceMax price
  have hR0 : 0 ≤ R := G.subtwoColorPriceMax_nonneg price hp
  by_cases hz : R = 0
  · have hzero := (G.subtwoColorPriceMax_eq_zero_iff price hp).mp hz
    have hAvoid (v : G.V) : G.subtwoAvoidingPriceMax price v = 0 := by
      have hlo := G.subtwoAvoidingPriceMax_nonneg price hp v
      have hhi := G.subtwoAvoidingPriceMax_le price v
      exact le_antisymm (by simpa [R, hz] using hhi) hlo
    simp [hzero, hAvoid, R, hz]
  have hR : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hz)
  obtain ⟨D, hset, hprice⟩ :=
    G.exists_subtwoThreePhysicalData_of_rank_one_block hn hlocal b hrank price hp hR
  subst price
  have hb := D.physical_reserved_price_bound hlocal b hrank hset
  have heq := D.physical_dual_sum_eq_objective
  rw [hset] at heq
  rw [heq]
  simpa [mul_comm] using (mul_lt_mul_of_pos_left hb D.price_max_pos).le

theorem rankOneThree_palette_attainable
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 1) :
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
    G.subtwoFiveInternalDemand S n ∈
      WeightedEdgeColoring.Subtwo.PaletteAttainable
        (WeightedEdgeColoring.Subtwo.reservedPaletteBudget (1999/1000:ℝ)
          (G.subtwoFiveReservedCharge S n))
        G.subtwoReservedColorPattern := by
  dsimp only
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
  have hsum : (∑ v : G.V, G.subtwoFiveReservedCharge S n v) ≤
      (1999/1000:ℝ) := by
    have h := G.subtwoFloorThree_exterior_budget hn hlocal b hrank
    dsimp only at h
    have heq : (∑ v : G.V, G.subtwoFiveReservedCharge S n v) =
        ∑ v ∈ S, G.subtwoExteriorHarmonicCharge S v / (n : ℝ) := by
      calc
        _ = ∑ v ∈ (Finset.univ : Finset G.V).filter (· ∈ S),
            G.subtwoExteriorHarmonicCharge S v / (n : ℝ) := by
          rw [Finset.sum_filter]
          rfl
        _ = _ := by rw [Finset.filter_univ_mem]
    rw [heq]
    simpa only [subtwoKappa] using h
  apply (G.subtwoGraphPalette_iff_chargeInequalities
    (1999/1000:ℝ) (G.subtwoFiveReservedCharge S n)
    (G.subtwoFiveReservedCharge_nonneg S n) hsum
    (G.subtwoFiveInternalDemand_nonneg S n)).2
  intro price hp
  exact G.rankOneThree_dual_price_bound hn hlocal b hrank price hp

end WeightedEdgeColoring.WeightedMultigraph
