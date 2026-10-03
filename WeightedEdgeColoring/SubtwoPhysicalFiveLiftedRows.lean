import WeightedEdgeColoring.SubtwoPhysicalFiveBoxRows

/-!
# Multiplied rows on the physical 970-coordinate vector

Every valid base row and every valid price row can be multiplied using
the true product columns. This file connects the generic real-arithmetic
proofs to the actual encoded graph observables.
-/

open scoped BigOperators
set_option autoImplicit false

namespace WeightedEdgeColoring.WeightedMultigraph
noncomputable section
universe u
variable {G : WeightedMultigraph.{u}} {n : ℕ}

namespace SubtwoFivePhysicalData
variable (D : G.SubtwoFivePhysicalData n)

theorem vector_baseCoordinate (y : Fin 75) :
    D.vector ⟨10 + y.val, by omega⟩ = D.baseCoordinate y := by
  unfold vector baseCoordinate
  dsimp only
  split_ifs <;> try omega
  all_goals
    congr 1
    apply Fin.ext
    dsimp only
    omega

theorem baseCoordinate_nonneg (y : Fin 75) : 0 ≤ D.baseCoordinate y := by
  unfold baseCoordinate
  split_ifs
  · exact (D.bundleCost_bounds _).1
  · exact D.exteriorCharge_nonneg _
  · exact (D.heavyMass_bounds _).1

/-- A physical base inequality supplies both RLT rows for every boxed
price coordinate. No independent value is assigned to a product column. -/
theorem vector_rlt_rows (a : Fin 75 → ℝ) (d : ℝ)
    (hrow : (∑ y, a y * D.baseCoordinate y) ≤ d)
    (L U : Fin 10 → ℝ) (hbox : ∀ e, L e ≤ D.pairPrice e ∧ D.pairPrice e ≤ U e)
    (e : Fin 10) :
    ((∑ y : Fin 75, a y * D.vector ⟨220 + 75 * e.val + y.val, by omega⟩) -
      L e * (∑ y : Fin 75, a y * D.vector ⟨10 + y.val, by omega⟩) - d * D.pairPrice e ≤ -L e * d) ∧
    (-(∑ y : Fin 75, a y * D.vector ⟨220 + 75 * e.val + y.val, by omega⟩) +
      U e * (∑ y : Fin 75, a y * D.vector ⟨10 + y.val, by omega⟩) + d * D.pairPrice e ≤ U e * d) := by
  simp only [D.vector_baseCoordinate]
  exact ⟨SubtwoBilinearRelaxation.rlt_lower_linear a D.baseCoordinate
      (fun y => D.vector ⟨220 + 75 * e.val + y.val, by omega⟩)
      (L e) (D.pairPrice e) d (hbox e).1 hrow (D.vector_product e),
    SubtwoBilinearRelaxation.rlt_upper_linear a D.baseCoordinate
      (fun y => D.vector ⟨220 + 75 * e.val + y.val, by omega⟩)
      (U e) (D.pairPrice e) d (hbox e).2 hrow (D.vector_product e)⟩

theorem vector_multiply_price_row (a : Fin 10 → ℝ) (d : ℝ)
    (hrow : (∑ e, a e * D.pairPrice e) ≤ d) (y : Fin 75) :
    (∑ e : Fin 10, a e * D.vector ⟨220 + 75 * e.val + y.val, by omega⟩) ≤
      d * D.vector ⟨10 + y.val, by omega⟩ := by
  rw [D.vector_baseCoordinate]
  exact SubtwoBilinearRelaxation.multiply_price_row a D.pairPrice
    (fun e => D.vector ⟨220 + 75 * e.val + y.val, by omega⟩)
    (D.baseCoordinate y) d (D.baseCoordinate_nonneg y) hrow (fun e => D.vector_product e y)

/-- Disjoint pair supports in the five-vertex block give the genuine
disjoint-price inequality needed before multiplying a price row. -/
theorem pairPrice_disjoint (e f : Fin 10)
    (hdisjoint : Disjoint ({(subtwoFivePair e).1, (subtwoFivePair e).2} : Finset (Fin 5))
      {(subtwoFivePair f).1, (subtwoFivePair f).2}) :
    D.pairPrice e + D.pairPrice f ≤ 1 := by
  have hd : Disjoint
      (({(subtwoFivePair e).1, (subtwoFivePair e).2} : Finset (Fin 5)).image D.vertex)
      (({(subtwoFivePair f).1, (subtwoFivePair f).2} : Finset (Fin 5)).image D.vertex) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hy
    exact Finset.disjoint_left.mp hdisjoint hi ((D.vertex_injective he) ▸ hj)
  apply G.subtwoNormalizedSetPrice_disjoint D.price D.price_max_pos
  simpa only [Finset.image_insert, Finset.image_singleton] using hd

theorem vector_lifted_disjoint_pair (e f : Fin 10)
    (hdisjoint : Disjoint ({(subtwoFivePair e).1, (subtwoFivePair e).2} : Finset (Fin 5))
      {(subtwoFivePair f).1, (subtwoFivePair f).2}) (y : Fin 75) :
    D.vector ⟨220 + 75 * e.val + y.val, by omega⟩ +
      D.vector ⟨220 + 75 * f.val + y.val, by omega⟩ -
      D.vector ⟨10 + y.val, by omega⟩ ≤ 0 := by
  rw [D.vector_baseCoordinate]
  exact SubtwoBilinearRelaxation.lifted_disjoint_pair (D.pairPrice e) (D.pairPrice f)
    (D.baseCoordinate y) _ _ (D.baseCoordinate_nonneg y)
    (D.pairPrice_disjoint e f hdisjoint) (D.vector_product e y) (D.vector_product f y)

end SubtwoFivePhysicalData
end
end WeightedEdgeColoring.WeightedMultigraph
