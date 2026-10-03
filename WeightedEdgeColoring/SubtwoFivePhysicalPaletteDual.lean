import WeightedEdgeColoring.SubtwoFivePhysicalLocalBound
import WeightedEdgeColoring.SubtwoPhysicalFiveDataFactory
import WeightedEdgeColoring.SubtwoGraphPalette
import WeightedEdgeColoring.SubtwoExteriorChargeSum

/-! The actual graph-wide price inequality for a dense rank-two five-block.
The interior contains each original edge type with demand `1/n`; the five
reserved labels carry the physical exterior harmonic charge. -/

open scoped BigOperators

namespace WeightedEdgeColoring.WeightedMultigraph

universe u
variable (G : WeightedMultigraph.{u})

noncomputable def subtwoFiveInternalDemand (S : Finset G.V) (n : ℕ) (e : G.E) : ℝ :=
  if G.fst e ∈ S ∧ G.snd e ∈ S then 1 / (n : ℝ) else 0

noncomputable def subtwoFiveReservedCharge (S : Finset G.V) (n : ℕ) (v : G.V) : ℝ :=
  if v ∈ S then G.subtwoExteriorHarmonicCharge S v / n else 0

theorem subtwoFiveInternalDemand_nonneg (S : Finset G.V) (n : ℕ) (e : G.E) :
    0 ≤ G.subtwoFiveInternalDemand S n e := by
  unfold subtwoFiveInternalDemand
  split_ifs <;> positivity

theorem subtwoFiveReservedCharge_nonneg (S : Finset G.V) (n : ℕ) (v : G.V) :
    0 ≤ G.subtwoFiveReservedCharge S n v := by
  unfold subtwoFiveReservedCharge
  split_ifs
  · exact div_nonneg (G.subtwoExteriorHarmonicCharge_nonneg S v) (Nat.cast_nonneg _)
  · rfl

namespace SubtwoFivePhysicalData

variable {G : WeightedMultigraph.{u}} {n : ℕ} (D : G.SubtwoFivePhysicalData n)

theorem sum_over_vertexSet (f : G.V → ℝ) :
    (∑ v : G.V, if v ∈ D.vertexSet then f v else 0) =
      ∑ i : Fin 5, f (D.vertex i) := by
  classical
  calc
    _ = ∑ v ∈ D.vertexSet, f v := by simp
    _ = _ := by
      unfold SubtwoFivePhysicalData.vertexSet
      rw [Finset.sum_image (fun i _ j _ h => D.vertex_injective h)]

theorem physical_dual_sum_identity :
    ((n : ℝ) * G.subtwoColorPriceMax D.price) *
      ((∑ e : G.E, D.price e * G.subtwoFiveInternalDemand D.vertexSet n e) +
        ∑ v : G.V, G.subtwoFiveReservedCharge D.vertexSet n v *
          (G.subtwoColorPriceMax D.price - G.subtwoAvoidingPriceMax D.price v)) =
      G.subtwoColorPriceMax D.price *
        (G.subtwoInternalCost D.price D.vertexSet +
          ∑ i : Fin 5, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
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
      (∑ i : Fin 5, G.subtwoExteriorHarmonicCharge D.vertexSet (D.vertex i) *
        (R - G.subtwoAvoidingPriceMax D.price (D.vertex i))) / n := by
    calc
      _ = ∑ v : G.V, if v ∈ D.vertexSet then
          (G.subtwoExteriorHarmonicCharge D.vertexSet v *
            (R - G.subtwoAvoidingPriceMax D.price v)) / n else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ D.vertexSet <;>
          simp [subtwoFiveReservedCharge, hv, div_mul_eq_mul_div]
      _ = ∑ i : Fin 5,
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
        ((∑ e : Fin 10, D.demandPrice e) +
          ∑ v : Fin 5, D.avoidingLoss v) := by
  have hsum := D.physical_dual_sum_identity
  have hobj := D.palette_dual_objective_identity
  rw [← hobj] at hsum
  have hnR : ((n : ℝ) * G.subtwoColorPriceMax D.price) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast D.n_pos.ne') D.price_max_pos.ne'
  have hfact :
      ((n : ℝ) * G.subtwoColorPriceMax D.price) *
        ((∑ e : G.E, D.price e * G.subtwoFiveInternalDemand D.vertexSet n e) +
          ∑ v : G.V, G.subtwoFiveReservedCharge D.vertexSet n v *
            (G.subtwoColorPriceMax D.price - G.subtwoAvoidingPriceMax D.price v)) =
      ((n : ℝ) * G.subtwoColorPriceMax D.price) *
        (G.subtwoColorPriceMax D.price *
          ((∑ e : Fin 10, D.demandPrice e) +
            ∑ v : Fin 5, D.avoidingLoss v)) := by
    calc
      _ = G.subtwoColorPriceMax D.price *
          (((n : ℝ) * G.subtwoColorPriceMax D.price) *
            ((∑ e : Fin 10, D.demandPrice e) +
              ∑ v : Fin 5, D.avoidingLoss v)) := hsum
      _ = _ := by ring
  exact mul_left_cancel₀ hnR hfact

end SubtwoFivePhysicalData

theorem rankTwoFive_dual_price_bound
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2)
    (price : G.E → ℝ) (hp : ∀ e, 0 ≤ price e) :
    let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
    (∑ e : G.E, price e * G.subtwoFiveInternalDemand S n e) +
      (∑ v : G.V, G.subtwoFiveReservedCharge S n v *
        (G.subtwoColorPriceMax price - G.subtwoAvoidingPriceMax price v)) ≤
          (1999/1000:ℝ) * G.subtwoColorPriceMax price := by
  dsimp only
  let S := G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) b
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
    G.exists_subtwoFivePhysicalData_of_rank_two_block hn hlocal b hrank price hp hR
  subst price
  have hb := D.physical_reserved_price_bound hlocal b hrank hset
  have heq := D.physical_dual_sum_eq_objective
  rw [hset] at heq
  rw [heq]
  simpa [mul_comm] using (mul_lt_mul_of_pos_left hb D.price_max_pos).le

/-- The actual dense five-block demand can be allocated among an unrestricted
1999/1000 palette and its five endpoint-reserved subpalettes. -/
theorem rankTwoFive_palette_attainable
    {n : ℕ} (hn : 0 < n) (hlocal : G.LocallyPacksInto n)
    (b : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank
      (G.subtwoFloorCost n) b = 2) :
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
    have h := G.subtwoFloorFive_exterior_budget hn hlocal b hrank
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
  exact G.rankTwoFive_dual_price_bound hn hlocal b hrank price hp

end WeightedEdgeColoring.WeightedMultigraph
