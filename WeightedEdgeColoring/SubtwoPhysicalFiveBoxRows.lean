import WeightedEdgeColoring.SubtwoPhysicalFiveVector
import WeightedEdgeColoring.SubtwoBilinearRelaxation

/-!
# Box bounds and product rows for the actual five-block vector

The price box bounds the first ten coordinates. Exterior charge has the
stronger cap 0.459155, and all other coordinates have cap one. The exact
product interpretation then proves every McCormick row of the certificate.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}

def subtwoFiveBaseCap (y : Fin 75) : ℝ :=
  if 10 ≤ y.val ∧ y.val < 15 then 459155 / 1000000 else 1

def subtwoFiveVectorLower (L : Fin 10 → ℝ) (k : Fin 970) : ℝ :=
  if h : k.val < 10 then L ⟨k.val, h⟩ else 0

def subtwoFiveVectorUpper (U : Fin 10 → ℝ) (k : Fin 970) : ℝ :=
  if h : k.val < 10 then U ⟨k.val, h⟩ else
  if 20 ≤ k.val ∧ k.val < 25 then 459155 / 1000000 else 1

namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem vector_pair (e : Fin 10) : D.vector ⟨e.val, by omega⟩ = D.pairPrice e := by
  unfold vector
  dsimp only
  rw [dif_pos e.is_lt]

theorem vector_exterior (v : Fin 5) : D.vector ⟨20 + v.val, by omega⟩ = D.exteriorCharge v := by
  unfold vector
  dsimp only
  rw [dif_neg (by omega : ¬20 + v.val < 10),
    dif_neg (by omega : ¬20 + v.val < 20), dif_pos (by omega : 20 + v.val < 25)]
  apply congrArg D.exteriorCharge
  apply Fin.ext
  change 20 + v.val - 20 = v.val
  omega

theorem baseCoordinate_le_cap_of_rank_two_block
    (hlocal : G.LocallyPacksInto n) (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (hset : D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q)
    (y : Fin 75) : D.baseCoordinate y ≤ subtwoFiveBaseCap y := by
  by_cases h0 : y.val < 10
  · simp only [baseCoordinate, dif_pos h0, subtwoFiveBaseCap,
      if_neg (by omega : ¬(10 ≤ y.val ∧ y.val < 15))]
    exact (D.bundleCost_bounds _).2
  · by_cases h1 : y.val < 15
    · simp only [baseCoordinate, dif_neg h0, dif_pos h1, subtwoFiveBaseCap,
        if_pos (by omega : 10 ≤ y.val ∧ y.val < 15)]
      exact (D.exteriorCharge_bounds_of_rank_two_block hlocal q hrank hset _).2
    · simp only [baseCoordinate, dif_neg h0, dif_neg h1, subtwoFiveBaseCap,
        if_neg (by omega : ¬(10 ≤ y.val ∧ y.val < 15))]
      exact (D.heavyMass_bounds _).2

/-- These are the finite lower and upper bounds used by the converted
integer certificate, with unknown upper bounds replaced by one. -/
theorem vector_certificate_bounds_of_rank_two_block
    (hlocal : G.LocallyPacksInto n) (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (hset : D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q)
    (L U : Fin 10 → ℝ) (hbox : ∀ e, L e ≤ D.pairPrice e ∧ D.pairPrice e ≤ U e)
    (k : Fin 970) :
    subtwoFiveVectorLower L k ≤ D.vector k ∧ D.vector k ≤ subtwoFiveVectorUpper U k := by
  obtain ⟨hk0, hk1⟩ := D.vector_bounds_of_rank_two_block hlocal q hrank hset k
  by_cases h0 : k.val < 10
  · have he : D.vector k = D.pairPrice ⟨k.val, h0⟩ := D.vector_pair ⟨k.val, h0⟩
    simpa only [subtwoFiveVectorLower, subtwoFiveVectorUpper, dif_pos h0, he] using hbox ⟨k.val, h0⟩
  · simp only [subtwoFiveVectorLower, subtwoFiveVectorUpper, dif_neg h0]
    refine ⟨hk0, ?_⟩
    split_ifs with hc
    · have he : D.vector k = D.exteriorCharge ⟨k.val - 20, by omega⟩ := by
        calc
          D.vector k = D.vector ⟨20 + (k.val - 20), by omega⟩ :=
            congrArg D.vector (Fin.ext (by
              change k.val = 20 + (k.val - 20)
              omega))
          _ = _ := D.vector_exterior ⟨k.val - 20, by omega⟩
      rw [he]
      exact (D.exteriorCharge_bounds_of_rank_two_block hlocal q hrank hset _).2
    · exact hk1

/-- All four product-relaxation rows for each of the 750 lifted columns,
using the actual coordinate and the correct cap of its base variable. -/
theorem vector_product_mccormick_of_rank_two_block
    (hlocal : G.LocallyPacksInto n) (q : (G.subtwoFloorQuotient n).V)
    (hrank : G.floorPacketization.groupedGraph.subtwoFinalRank (G.subtwoFloorCost n) q = 2)
    (hset : D.vertexSet = G.floorPacketization.groupedGraph.subtwoFiber (G.subtwoFloorBlock n) q)
    (L U : Fin 10 → ℝ) (hbox : ∀ e, L e ≤ D.pairPrice e ∧ D.pairPrice e ≤ U e)
    (e : Fin 10) (y : Fin 75) :
    let X := D.vector ⟨220 + 75 * e.val + y.val, by omega⟩
    let cap := subtwoFiveBaseCap y
    X - U e * D.baseCoordinate y ≤ 0 ∧
      -X + L e * D.baseCoordinate y ≤ 0 ∧
      X - cap * D.pairPrice e - L e * D.baseCoordinate y ≤ -cap * L e ∧
      -X + cap * D.pairPrice e + U e * D.baseCoordinate y ≤ cap * U e := by
  have hy0 := (D.baseCoordinate_bounds (fun v =>
    (D.exteriorCharge_bounds_of_rank_two_block hlocal q hrank hset v).2.trans (by norm_num)) y).1
  exact SubtwoBilinearRelaxation.all_mccormick_rows (L e) (U e) (D.pairPrice e)
    (D.baseCoordinate y) (subtwoFiveBaseCap y) _ (hbox e).1 (hbox e).2 hy0
    (D.baseCoordinate_le_cap_of_rank_two_block hlocal q hrank hset y) (D.vector_product e y)

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
